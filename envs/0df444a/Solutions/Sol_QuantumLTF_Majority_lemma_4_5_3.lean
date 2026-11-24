-- Prove2me | solution 3 for QuantumLTF.Majority.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T01:40:29.658624+00:00
-- url     : https://prove2.me/submissions/42ec8f25-eff9-4ef2-bbb9-e0980d0117b5

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_as_character_sum
import Theorems.Thm_QuantumLTF_Majority_boolean_character_orthogonality
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_weighted_orthogonality
import Theorems.Thm_QuantumLTF_Majority_lemma_4_2_two_channel
import Theorems.Thm_QuantumLTF_Majority_normalized_intersection_sum
import Theorems.Thm_QuantumLTF_Majority_pointwise_correction_bound_to_log_energy

namespace Aux_w_maj_sdp

open QuantumLTF.Majority QAlgorithms

lemma krawtchouk_reflection (r t a : ℕ) (ha : a ≤ r) :
    krawtchouk r t (r - a) = (-1 : ℤ) ^ t * krawtchouk r t a := by
  unfold krawtchouk
  rw [← Finset.sum_range_reflect
    (fun j => (-1 : ℤ) ^ j * ((r - a).choose j : ℤ) * ((r - (r - a)).choose (t - j) : ℤ)) (t + 1)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hr : r - (r - a) = a := Nat.sub_sub_self ha
  have ht1 : t + 1 - 1 - j = t - j := by omega
  have ht2 : t - (t - j) = j := Nat.sub_sub_self hj'
  rw [hr, ht1, ht2]
  have hsq : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hpow : (-1 : ℤ) ^ (t - j) = (-1 : ℤ) ^ t * (-1 : ℤ) ^ j := by
    calc (-1 : ℤ) ^ (t - j)
        = (-1 : ℤ) ^ (t - j) * ((-1 : ℤ) ^ j * (-1 : ℤ) ^ j) := by rw [hsq, mul_one]
      _ = ((-1 : ℤ) ^ (t - j) * (-1 : ℤ) ^ j) * (-1 : ℤ) ^ j := by ring
      _ = (-1 : ℤ) ^ t * (-1 : ℤ) ^ j := by rw [← pow_add, Nat.sub_add_cancel hj']
  rw [hpow]
  ring

private lemma choose_triple_symm (r t a j : ℕ) (ht : t ≤ r) (ha : a ≤ r) (hjt : j ≤ t) (hja : j ≤ a) :
    r.choose a * a.choose j * (r - a).choose (t - j) =
      r.choose t * t.choose j * (r - t).choose (a - j) := by
  have h1 : r.choose a * a.choose j = r.choose j * (r - j).choose (a - j) := Nat.choose_mul hja
  have h2 : r.choose t * t.choose j = r.choose j * (r - j).choose (t - j) := Nat.choose_mul hjt
  have ha1 : (r - j) - (a - j) = r - a := by omega
  have ht1 : (r - j) - (t - j) = r - t := by omega
  have h3 : (r - j).choose ((a - j) + (t - j)) * ((a - j) + (t - j)).choose (a - j) =
      (r - j).choose (a - j) * (r - a).choose (t - j) := by
    have := Nat.choose_mul (n := r - j) (k := (a - j) + (t - j)) (s := a - j) (Nat.le_add_right _ _)
    simpa [ha1, Nat.add_sub_cancel_left] using this
  have h4 : (r - j).choose ((t - j) + (a - j)) * ((t - j) + (a - j)).choose (t - j) =
      (r - j).choose (t - j) * (r - t).choose (a - j) := by
    have := Nat.choose_mul (n := r - j) (k := (t - j) + (a - j)) (s := t - j) (Nat.le_add_right _ _)
    simpa [ht1, Nat.add_sub_cancel_left] using this
  have hsym : ((a - j) + (t - j)).choose (a - j) = ((t - j) + (a - j)).choose (t - j) := by
    calc ((a - j) + (t - j)).choose (a - j)
        = ((a - j) + (t - j)).choose (((a - j) + (t - j)) - (t - j)) := by rw [Nat.add_sub_cancel]
      _ = ((a - j) + (t - j)).choose (t - j) := Nat.choose_symm (Nat.le_add_left _ _)
      _ = ((t - j) + (a - j)).choose (t - j) := by rw [Nat.add_comm]
  calc r.choose a * a.choose j * (r - a).choose (t - j)
      = r.choose j * ((r - j).choose (a - j) * (r - a).choose (t - j)) := by rw [h1, mul_assoc]
    _ = r.choose j * ((r - j).choose ((a - j) + (t - j)) * ((a - j) + (t - j)).choose (a - j)) := by rw [← h3]
    _ = r.choose j * ((r - j).choose ((t - j) + (a - j)) * ((t - j) + (a - j)).choose (t - j)) := by rw [hsym, Nat.add_comm (a - j)]
    _ = r.choose j * ((r - j).choose (t - j) * (r - t).choose (a - j)) := by rw [h4]
    _ = r.choose t * t.choose j * (r - t).choose (a - j) := by rw [← mul_assoc, ← h2]

lemma krawtchouk_reciprocity (r t a : ℕ) (ht : t ≤ r) (ha : a ≤ r) :
    (r.choose a : ℤ) * krawtchouk r t a = (r.choose t : ℤ) * krawtchouk r a t := by
  unfold krawtchouk
  rw [Finset.mul_sum, Finset.mul_sum]
  have hL : ∑ j ∈ Finset.range (t + 1), (r.choose a : ℤ) * ((-1 : ℤ) ^ j * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ)) =
      ∑ j ∈ Finset.range (min t a + 1), (r.choose a : ℤ) * ((-1 : ℤ) ^ j * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ)) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j hj1 hj2 => ?_
    rw [Finset.mem_range] at hj1 hj2
    have hja : a < j := by omega
    simp [Nat.choose_eq_zero_of_lt hja]
  have hR : ∑ j ∈ Finset.range (a + 1), (r.choose t : ℤ) * ((-1 : ℤ) ^ j * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ)) =
      ∑ j ∈ Finset.range (min t a + 1), (r.choose t : ℤ) * ((-1 : ℤ) ^ j * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ)) := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun j hj1 hj2 => ?_
    rw [Finset.mem_range] at hj1 hj2
    have hjt : t < j := by omega
    simp [Nat.choose_eq_zero_of_lt hjt]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hjt : j ≤ t := by omega
  have hja : j ≤ a := by omega
  have hnat := choose_triple_symm r t a j ht ha hjt hja
  have hint : (r.choose a : ℤ) * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ) =
      (r.choose t : ℤ) * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ) := by
    exact_mod_cast hnat
  calc (r.choose a : ℤ) * ((-1 : ℤ) ^ j * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ))
      = (-1 : ℤ) ^ j * ((r.choose a : ℤ) * (a.choose j : ℤ) * ((r - a).choose (t - j) : ℤ)) := by ring
    _ = (-1 : ℤ) ^ j * ((r.choose t : ℤ) * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ)) := by rw [hint]
    _ = (r.choose t : ℤ) * ((-1 : ℤ) ^ j * (t.choose j : ℤ) * ((r - t).choose (a - j) : ℤ)) := by ring

noncomputable def krawtchoukPoly (r u : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (u + 1),
    Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) *
      (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))) *
      (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ)))

private lemma desc_prod_eq_descFactorial (m j : ℕ) :
    (∏ i ∈ Finset.range j, ((m : ℝ) - (i : ℝ))) = (Nat.descFactorial m j : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
    by_cases hjm : j ≤ m
    · rw [Nat.cast_mul, Nat.cast_sub hjm]
      ring
    · have hlt : m < j := Nat.lt_of_not_ge hjm
      have hdf : Nat.descFactorial m j = 0 := Nat.descFactorial_of_lt hlt
      simp [hdf]

private lemma desc_prod_eq_choose_mul_factorial (m j : ℕ) :
    (∏ i ∈ Finset.range j, ((m : ℝ) - (i : ℝ))) = (m.choose j : ℝ) * (j.factorial : ℝ) := by
  rw [desc_prod_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

lemma krawtchoukPoly_eval (r u t : ℕ) (ht : t ≤ r) :
    (krawtchoukPoly r u).eval (t : ℝ) = (krawtchouk r u t : ℝ) := by
  unfold krawtchoukPoly krawtchouk
  rw [Polynomial.eval_finsetSum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X]
  have h1 := desc_prod_eq_choose_mul_factorial t j
  have h2 : (∏ i ∈ Finset.range (u - j), ((r : ℝ) - (t : ℝ) - (i : ℝ))) =
      (((r - t).choose (u - j) : ℕ) : ℝ) * (((u - j).factorial : ℕ) : ℝ) := by
    have hsub : (r : ℝ) - (t : ℝ) = ((r - t : ℕ) : ℝ) := by rw [Nat.cast_sub ht]
    simp_rw [hsub]
    exact desc_prod_eq_choose_mul_factorial (r - t) (u - j)
  rw [h1, h2]
  have hjf : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have huf : ((u - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (u - j))
  field_simp [hjf, huf]

private lemma krawtchoukPoly_term_deg_and_coeff (r u j : ℕ) (hj : j ≤ u) :
    let T := Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) *
      (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))) *
      (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ)))
    T.natDegree ≤ u ∧ T.coeff u = (-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ)) := by
  intro T
  let P₁ : Polynomial ℝ := ∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))
  let Q₂ : Polynomial ℝ := ∏ i ∈ Finset.range (u - j), (Polynomial.X - Polynomial.C ((r : ℝ) - (i : ℝ)))
  have hP1_monic : P₁.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hQ2_monic : Q₂.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hP1_deg : P₁.natDegree = j := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    trans ∑ _ ∈ Finset.range j, 1
    · exact Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_sub_C (i : ℝ)
    · simp
  have hQ2_deg : Q₂.natDegree = u - j := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    trans ∑ _ ∈ Finset.range (u - j), 1
    · exact Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_sub_C ((r : ℝ) - (i : ℝ))
    · simp
  have hP2_eq : (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ))) =
      Polynomial.C ((-1 : ℝ) ^ (u - j)) * Q₂ := by
    have hfac : ∀ i : ℕ, Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ) =
        (-1 : Polynomial ℝ) * (Polynomial.X - Polynomial.C ((r : ℝ) - (i : ℝ))) := fun i => by
      simp only [map_sub]; ring
    simp_rw [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    simp [Q₂]
  have hPQ_monic : (P₁ * Q₂).Monic := hP1_monic.mul hQ2_monic
  have hPQ_deg : (P₁ * Q₂).natDegree = u := by
    rw [Polynomial.natDegree_mul' (by simp [hP1_monic.leadingCoeff, hQ2_monic.leadingCoeff]),
      hP1_deg, hQ2_deg]
    omega
  have hTeq : T = Polynomial.C ((-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) * (P₁ * Q₂) := by
    dsimp [T]
    change Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) * P₁ *
        (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ))) = _
    rw [hP2_eq]
    have hpow : (-1 : ℝ) ^ j * (-1 : ℝ) ^ (u - j) = (-1 : ℝ) ^ u := by
      rw [← pow_add, Nat.add_sub_cancel' hj]
    calc Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) * P₁ *
          (Polynomial.C ((-1 : ℝ) ^ (u - j)) * Q₂)
        = (Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) *
            Polynomial.C ((-1 : ℝ) ^ (u - j))) * (P₁ * Q₂) := by ring
      _ = Polynomial.C ((-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) * (P₁ * Q₂) := by
          rw [← map_mul]; congr 2; rw [← hpow]; ring
  rw [hTeq]
  constructor
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hPQ_deg.le
  · rw [Polynomial.coeff_C_mul, ← hPQ_deg, Polynomial.coeff_natDegree, hPQ_monic.leadingCoeff, mul_one]

lemma krawtchoukPoly_deg_le (r u : ℕ) : (krawtchoukPoly r u).natDegree ≤ u := by
  unfold krawtchoukPoly
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le fun j hj => ?_
  exact (krawtchoukPoly_term_deg_and_coeff r u j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).1

lemma krawtchoukPoly_coeff_self (r u : ℕ) :
    (krawtchoukPoly r u).coeff u = (-2 : ℝ) ^ u / (u.factorial : ℝ) := by
  unfold krawtchoukPoly
  rw [Polynomial.finsetSum_coeff]
  have hsum : ∑ j ∈ Finset.range (u + 1),
      (Polynomial.C ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((u - j).factorial : ℝ))) *
        (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))) *
        (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ)))).coeff u =
      ∑ j ∈ Finset.range (u + 1), (-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact (krawtchoukPoly_term_deg_and_coeff r u j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).2
  rw [hsum]
  have hu : (u.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero u)
  have hterm : ∀ j ∈ Finset.range (u + 1),
      (-1 : ℝ) ^ u / ((j.factorial : ℝ) * ((u - j).factorial : ℝ)) =
        ((-1 : ℝ) ^ u / (u.factorial : ℝ)) * (u.choose j : ℝ) := by
    intro j hj
    have hj' : j ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hch := Nat.choose_mul_factorial_mul_factorial hj'
    have hchR : (u.choose j : ℝ) * (j.factorial : ℝ) * ((u - j).factorial : ℝ) = (u.factorial : ℝ) := by
      exact_mod_cast hch
    have hjf : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have huf : ((u - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (u - j))
    field_simp [hu, hjf, huf]
    nlinarith [hchR]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hbin : ∑ j ∈ Finset.range (u + 1), (u.choose j : ℝ) = (2 : ℝ) ^ u := by
    exact_mod_cast Nat.sum_range_choose u
  rw [hbin]
  have hpow : (-1 : ℝ) ^ u * (2 : ℝ) ^ u = (-2 : ℝ) ^ u := by
    rw [← mul_pow]; norm_num
  rw [div_mul_eq_mul_div, hpow]

lemma krawtchoukPoly_coeff_self_ne_zero (r u : ℕ) :
    (krawtchoukPoly r u).coeff u ≠ 0 := by
  rw [krawtchoukPoly_coeff_self]
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero u))

lemma krawtchouk_poly_orthogonality (r a : ℕ) (ha : a ≤ r) :
    ∀ d : ℕ, d < a → ∀ P : Polynomial ℝ, P.natDegree ≤ d →
      ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ) = 0 := by
  intro d hd P hP
  induction d generalizing P with
  | zero =>
    have hP0 : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hP
    rw [hP0]
    have h0 : krawtchoukPoly r 0 = 1 := by
      unfold krawtchoukPoly; simp
    have hsum : ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * (Polynomial.C (P.coeff 0)).eval (t : ℝ) =
        P.coeff 0 * ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * (krawtchouk r 0 t : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hk0 : (krawtchouk r 0 t : ℝ) = 1 := by
        rw [← krawtchoukPoly_eval r 0 t (Nat.lt_succ_iff.mp t.isLt), h0]; simp
      simp [hk0]; ring
    rw [hsum]
    have horth := krawtchouk_weighted_orthogonality r ⟨a, by omega⟩ ⟨0, by omega⟩
    have ha0 : a ≠ 0 := by omega
    simp [ha0] at horth
    rw [horth, mul_zero]
  | succ d ih =>
    let K := krawtchoukPoly r (d + 1)
    let c := P.coeff (d + 1) / K.coeff (d + 1)
    let P' := P - Polynomial.C c * K
    have hK_ne : K.coeff (d + 1) ≠ 0 := krawtchoukPoly_coeff_self_ne_zero r (d + 1)
    have hP'_deg : P'.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      simp only [P', Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      by_cases hNd : N = d + 1
      · subst hNd
        dsimp [c]
        rw [div_mul_cancel₀ _ hK_ne, sub_self]
      · have hNgt : d + 1 < N := by omega
        have h1 : P.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hNgt)
        have h2 : K.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (krawtchoukPoly_deg_le r (d + 1)) hNgt)
        simp [h1, h2]
    have hsplit : ∀ t : Fin (r + 1), P.eval (t : ℝ) = P'.eval (t : ℝ) + c * K.eval (t : ℝ) := fun t => by
      simp [P']
    have hsum : ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ) =
        (∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P'.eval (t : ℝ)) +
        c * ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * (krawtchouk r (d + 1) t : ℝ) := by
      calc ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ)
          = ∑ t : Fin (r + 1), ((r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P'.eval (t : ℝ) +
              c * ((r.choose t : ℝ) * (krawtchouk r a t : ℝ) * K.eval (t : ℝ))) := by
            refine Finset.sum_congr rfl fun t _ => ?_; rw [hsplit t]; ring
        _ = (∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P'.eval (t : ℝ)) +
              c * ∑ t : Fin (r + 1), (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * K.eval (t : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = _ := by
            congr 2
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [krawtchoukPoly_eval r (d + 1) t (Nat.lt_succ_iff.mp t.isLt)]
    rw [hsum, ih (by omega) P' hP'_deg]
    have horth := krawtchouk_weighted_orthogonality r ⟨a, by omega⟩ ⟨d + 1, by omega⟩
    have hne : (⟨a, by omega⟩ : Fin (r + 1)) ≠ ⟨d + 1, by omega⟩ := by
      intro h; simp at h; omega
    simp [hne] at horth
    rw [horth]
    ring

lemma L_vanish_of_gt (m : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ m) (a : Fin (2 * m + 1 + 1))
    (ha : m < (a : ℕ)) :
    ∑ t : Fin (2 * m + 1 + 1), (krawtchouk (2 * m + 1) t a : ℝ) * P.eval (t : ℝ) = 0 := by
  let r := 2 * m + 1
  have ha_le : (a : ℕ) ≤ r := Nat.lt_succ_iff.mp a.isLt
  have hpos : (0 : ℝ) < (r.choose a : ℝ) := by
    exact_mod_cast Nat.choose_pos ha_le
  have hmul : (r.choose a : ℝ) * ∑ t : Fin (r + 1), (krawtchouk r t a : ℝ) * P.eval (t : ℝ) = 0 := by
    rw [Finset.mul_sum]
    have hrew : ∀ t : Fin (r + 1),
        (r.choose a : ℝ) * ((krawtchouk r t a : ℝ) * P.eval (t : ℝ)) =
          (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ) := by
      intro t
      have ht_le : (t : ℕ) ≤ r := Nat.lt_succ_iff.mp t.isLt
      have hrec : (r.choose a : ℝ) * (krawtchouk r t a : ℝ) = (r.choose t : ℝ) * (krawtchouk r a t : ℝ) := by
        exact_mod_cast krawtchouk_reciprocity r t a ht_le ha_le
      calc (r.choose a : ℝ) * ((krawtchouk r t a : ℝ) * P.eval (t : ℝ))
          = ((r.choose a : ℝ) * (krawtchouk r t a : ℝ)) * P.eval (t : ℝ) := by ring
        _ = ((r.choose t : ℝ) * (krawtchouk r a t : ℝ)) * P.eval (t : ℝ) := by rw [hrec]
        _ = (r.choose t : ℝ) * (krawtchouk r a t : ℝ) * P.eval (t : ℝ) := by ring
    rw [Finset.sum_congr rfl fun t _ => hrew t]
    exact krawtchouk_poly_orthogonality r a ha_le m ha P hP
  exact (mul_eq_zero.mp hmul).resolve_left hpos.ne'

lemma U_vanish_of_le (m : ℕ) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ m) (a : Fin (2 * m + 1 + 1))
    (ha : (a : ℕ) ≤ m) :
    ∑ t : Fin (2 * m + 1 + 1), (krawtchouk (2 * m + 1) t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * Q.eval (t : ℝ)) = 0 := by
  let r := 2 * m + 1
  let a' : Fin (r + 1) := ⟨r - a, by omega⟩
  have hgt : m < (a' : ℕ) := by dsimp [a']; omega
  have hL := L_vanish_of_gt m Q hQ a' hgt
  have hrew : ∀ t : Fin (r + 1),
      (krawtchouk r t a' : ℝ) * Q.eval (t : ℝ) =
        (krawtchouk r t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * Q.eval (t : ℝ)) := by
    intro t
    have ha_le : (a : ℕ) ≤ r := Nat.lt_succ_iff.mp a.isLt
    have href : (krawtchouk r t a' : ℝ) = (-1 : ℝ) ^ (t : ℕ) * (krawtchouk r t a : ℝ) := by
      exact_mod_cast krawtchouk_reflection r t a ha_le
    rw [href]
    ring
  rw [← hL]
  symm
  exact Finset.sum_congr rfl fun t _ => hrew t

lemma krawtchouk_eq_powersetCard_sum {n' r : ℕ} (A : Finset (Fin n')) (hA : A.card = r)
    (u : Fin (r + 1)) (S : Qubits n') :
    (krawtchouk r u ((A.filter fun i => S i).card) : ℤ) =
      ∑ T ∈ A.powersetCard (u : ℕ), (-1 : ℤ) ^ ((T.filter fun i => S i).card) := by
  let A₁ := A.filter fun i => S i = true
  let A₀ := A.filter fun i => !(S i = true)
  let a := A₁.card
  have ha_le : a ≤ r := by
    rw [← hA]
    exact Finset.card_filter_le _ _
  have hA₀_card : A₀.card = r - a := by
    have hsum := Finset.card_filter_add_card_filter_not (s := A) (p := fun i => S i = true)
    rw [hA] at hsum
    dsimp [A₀]
    have hcard_eq : A₀.card = (A.filter fun i => ¬(S i = true)).card := by
      congr 1; ext i; dsimp [A₀]; simp
    rw [hcard_eq]
    dsimp [a, A₁]
    exact Nat.eq_sub_of_add_eq' hsum
  have hA₁_sub : ∀ x ∈ A₁, x ∈ A := fun x hx => (Finset.mem_filter.mp hx).1
  have hA₀_sub : ∀ x ∈ A₀, x ∈ A := fun x hx => (Finset.mem_filter.mp hx).1
  let e₁ : Fin a ≃ A₁ := (Fintype.equivFinOfCardEq (by simp [a])).symm
  let e₀ : Fin (r - a) ≃ A₀ := (Fintype.equivFinOfCardEq (by simp [hA₀_card])).symm
  let φ : Fin r → Fin n' := fun i =>
    if h : (i : ℕ) < a then (e₁ ⟨i, h⟩).1 else (e₀ ⟨i - a, by omega⟩).1
  have hφ_mem : ∀ i : Fin r, φ i ∈ A := fun i => by
    dsimp [φ]
    split_ifs with h
    · exact hA₁_sub _ (e₁ ⟨i, h⟩).2
    · exact hA₀_sub _ (e₀ ⟨i - a, by omega⟩).2
  have hφ_S : ∀ i : Fin r, S (φ i) = true ↔ (i : ℕ) < a := fun i => by
    dsimp [φ]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => (Finset.mem_filter.mp (e₁ ⟨i, h⟩).2).2⟩
    · constructor
      · intro hS
        exfalso
        have hnot := (Finset.mem_filter.mp (e₀ ⟨i - a, by omega⟩).2).2
        simp [hS] at hnot
      · intro hi; exact False.elim (h hi)
  have hφ_inj : Function.Injective φ := by
    intro i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have h' : (e₁ ⟨i, hi⟩).1 = (e₁ ⟨j, hj⟩).1 := by
        simpa [φ, hi, hj] using hij
      have h'' := e₁.injective (Subtype.ext h')
      ext; simpa using congrArg Fin.val h''
    · exfalso
      have h1 := (hφ_S i).mpr hi
      rw [hij] at h1
      exact hj ((hφ_S j).mp h1)
    · exfalso
      have h1 := (hφ_S j).mpr hj
      rw [← hij] at h1
      exact hi ((hφ_S i).mp h1)
    · have h' : (e₀ ⟨i - a, by omega⟩).1 = (e₀ ⟨j - a, by omega⟩).1 := by
        simpa [φ, hi, hj] using hij
      have h'' := e₀.injective (Subtype.ext h')
      have hval := congrArg Fin.val h''
      dsimp at hval
      ext; omega
  let e : Fin r ↪ Fin n' := ⟨φ, hφ_inj⟩
  have hmap_eq : (Finset.univ : Finset (Fin r)).map e = A := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_map] at hx
      rcases hx with ⟨i, _, rfl⟩
      exact hφ_mem i
    · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hA]
  have hpow_eq : ((Finset.univ : Finset (Fin r)).powersetCard (u : ℕ)).map (Finset.mapEmbedding e).toEmbedding =
      A.powersetCard (u : ℕ) := by
    rw [← hmap_eq]
    ext T
    simp only [Finset.mem_map, Finset.mem_powersetCard, Finset.mapEmbedding_apply,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨T₀, ⟨_, hT₀c⟩, rfl⟩
      exact ⟨Finset.map_subset_map.mpr (Finset.subset_univ _), by simpa using hT₀c⟩
    · rintro ⟨hTsub, hTc⟩
      refine ⟨T.preimage e e.injective.injOn, ?_, ?_⟩
      · refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_preimage T e e.injective.injOn, Finset.filter_true_of_mem]
        · exact hTc
        · intro x hx
          have hx' := hTsub hx
          rw [Finset.mem_map] at hx'
          rcases hx' with ⟨i, _, rfl⟩
          exact ⟨i, rfl⟩
      · ext x
        simp only [Finset.mem_map, Finset.mem_preimage]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact hi
        · intro hx
          have hx' := hTsub hx
          rw [Finset.mem_map] at hx'
          rcases hx' with ⟨i, _, rfl⟩
          exact ⟨i, hx, rfl⟩
  have hchar := krawtchouk_as_character_sum r u ⟨a, by omega⟩
  change (krawtchouk r u a : ℤ) = _
  rw [hchar, ← hpow_eq, Finset.sum_map]
  refine Finset.sum_congr rfl fun T₀ _ => ?_
  congr 1
  change (T₀ ∩ Finset.univ.filter fun i : Fin r => (i : ℕ) < a).card = ((T₀.map e).filter fun i => S i).card
  have hfilt : ((T₀.map e).filter fun i => S i = true) =
      (T₀ ∩ Finset.univ.filter fun i : Fin r => (i : ℕ) < a).map e := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_inter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hSx⟩
      exact ⟨i, ⟨hi, (hφ_S i).mp (by simpa [e] using hSx)⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hia⟩, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, by simpa [e] using (hφ_S i).mpr hia⟩
  have hfilt' : ((T₀.map e).filter fun i => S i) =
      ((T₀.map e).filter fun i => S i = true) := by
    ext x; simp
  rw [hfilt', hfilt, Finset.card_map]

lemma krawtchouk_cross_expectation {n' r s : ℕ} (A B : Finset (Fin n'))
    (hA : A.card = r) (hB : B.card = s) (u : Fin (r + 1)) (v : Fin (s + 1)) :
    (2 : ℝ) ^ (-(n' : ℤ)) *
        ∑ S : Qubits n',
          (krawtchouk r u ((A.filter fun i => S i).card) : ℝ) *
          (krawtchouk s v ((B.filter fun i => S i).card) : ℝ) =
      if (u : ℕ) = (v : ℕ) then (((A ∩ B).card.choose (u : ℕ) : ℕ) : ℝ) else 0 := by
  have hint :
      ∑ S : Qubits n',
          (krawtchouk r u ((A.filter fun i => S i).card) : ℤ) *
          (krawtchouk s v ((B.filter fun i => S i).card) : ℤ) =
        (2 : ℤ) ^ n' * (if (u : ℕ) = (v : ℕ) then (((A ∩ B).card.choose (u : ℕ) : ℕ) : ℤ) else 0) := by
    have h1 : ∀ S : Qubits n',
        (krawtchouk r u ((A.filter fun i => S i).card) : ℤ) *
        (krawtchouk s v ((B.filter fun i => S i).card) : ℤ) =
        ∑ T ∈ A.powersetCard (u : ℕ), ∑ U ∈ B.powersetCard (v : ℕ),
          (-1 : ℤ) ^ ((T.filter fun i => S i).card) * (-1 : ℤ) ^ ((U.filter fun i => S i).card) := by
      intro S
      rw [krawtchouk_eq_powersetCard_sum A hA u S, krawtchouk_eq_powersetCard_sum B hB v S,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Finset.mul_sum]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have hswap : ∀ T ∈ A.powersetCard (u : ℕ),
        ∑ S : Qubits n', ∑ U ∈ B.powersetCard (v : ℕ),
          (-1 : ℤ) ^ ((T.filter fun i => S i).card) * (-1 : ℤ) ^ ((U.filter fun i => S i).card) =
        ∑ U ∈ B.powersetCard (v : ℕ),
          if T = U then (2 : ℤ) ^ n' else 0 := by
      intro T _
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun U _ => ?_
      exact boolean_character_orthogonality n' T U
    rw [Finset.sum_congr rfl hswap]
    by_cases huv : (u : ℕ) = (v : ℕ)
    · simp only [huv, ↓reduceIte]
      have hcard : ∑ T ∈ A.powersetCard (v : ℕ), ∑ U ∈ B.powersetCard (v : ℕ), (if T = U then (2 : ℤ) ^ n' else 0) =
          (2 : ℤ) ^ n' * (((A ∩ B).powersetCard (v : ℕ)).card : ℤ) := by
        have hinner : ∀ T ∈ A.powersetCard (v : ℕ),
            (∑ U ∈ B.powersetCard (v : ℕ), if T = U then (2 : ℤ) ^ n' else 0) =
              if T ∈ B.powersetCard (v : ℕ) then (2 : ℤ) ^ n' else 0 := by
          intro T _
          rw [Finset.sum_ite_eq]
        rw [Finset.sum_congr rfl hinner]
        rw [← Finset.sum_filter]
        have hfilt : (A.powersetCard (v : ℕ)).filter (fun T => T ∈ B.powersetCard (v : ℕ)) =
            (A ∩ B).powersetCard (v : ℕ) := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
          tauto
        rw [hfilt, Finset.sum_const, nsmul_eq_mul]
        ring
      rw [hcard]
      simp [Finset.card_powersetCard]
    · simp only [huv, ↓reduceIte, mul_zero]
      refine Finset.sum_eq_zero fun T hT => ?_
      refine Finset.sum_eq_zero fun U hU => ?_
      have hTc := (Finset.mem_powersetCard.mp hT).2
      have hUc := (Finset.mem_powersetCard.mp hU).2
      have hne : T ≠ U := fun h => by subst h; exact huv (hTc.symm.trans hUc)
      simp [hne]
  have hreal : (∑ S : Qubits n',
      (krawtchouk r u ((A.filter fun i => S i).card) : ℝ) *
      (krawtchouk s v ((B.filter fun i => S i).card) : ℝ)) =
      (2 : ℝ) ^ n' * (if (u : ℕ) = (v : ℕ) then (((A ∩ B).card.choose (u : ℕ) : ℕ) : ℝ) else 0) := by
    exact_mod_cast hint
  rw [hreal, ← mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]

/-! ### Step 3: Mod-4 polynomials, correction polynomials, and cross-layer moment identity -/

def rootSetP (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * m)).filter fun r => r % 4 = 0 ∨ r % 4 = 1

def rootSetQ (m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 * m)).filter fun r => r % 4 = 2 ∨ r % 4 = 3

lemma rootSetP_disjoint_rootSetQ (m : ℕ) : Disjoint (rootSetP m) (rootSetQ m) := by
  rw [Finset.disjoint_left]
  intro x hxP hxQ
  simp only [rootSetP, rootSetQ, Finset.mem_filter] at hxP hxQ
  omega

lemma rootSetP_union_rootSetQ (m : ℕ) : rootSetP m ∪ rootSetQ m = Finset.Icc 1 (2 * m) := by
  ext x
  simp only [Finset.mem_union, rootSetP, rootSetQ, Finset.mem_filter, Finset.mem_Icc]
  omega

lemma rootSetP_mono {m l : ℕ} (hml : m ≤ l) : rootSetP m ⊆ rootSetP l := by
  intro x hx
  simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
  omega

lemma rootSetQ_mono {m l : ℕ} (hml : m ≤ l) : rootSetQ m ⊆ rootSetQ l := by
  intro x hx
  simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
  omega

lemma card_rootSetP_and_Q (m : ℕ) : (rootSetP m).card = m ∧ (rootSetQ m).card = m := by
  induction m with
  | zero => simp [rootSetP, rootSetQ]
  | succ m ih =>
    have hP_step : rootSetP (m + 1) =
        if Even m then insert (2 * m + 1) (rootSetP m) else insert (2 * m + 2) (rootSetP m) := by
      ext x
      simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]
      split_ifs with hm
      · rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        rcases hm with ⟨k, hk⟩
        omega
      · rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        rw [Nat.not_even_iff_odd] at hm
        rcases hm with ⟨k, hk⟩
        omega
    have hQ_step : rootSetQ (m + 1) =
        if Even m then insert (2 * m + 2) (rootSetQ m) else insert (2 * m + 1) (rootSetQ m) := by
      ext x
      simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]
      split_ifs with hm
      · rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        rcases hm with ⟨k, hk⟩
        omega
      · rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        rw [Nat.not_even_iff_odd] at hm
        rcases hm with ⟨k, hk⟩
        omega
    constructor
    · rw [hP_step]
      split_ifs with hm
      · have hnot : 2 * m + 1 ∉ rootSetP m := by
          simp [rootSetP]
        rw [Finset.card_insert_of_notMem hnot, ih.1]
      · have hnot : 2 * m + 2 ∉ rootSetP m := by
          simp [rootSetP]
        rw [Finset.card_insert_of_notMem hnot, ih.1]
    · rw [hQ_step]
      split_ifs with hm
      · have hnot : 2 * m + 2 ∉ rootSetQ m := by
          simp [rootSetQ]
        rw [Finset.card_insert_of_notMem hnot, ih.2]
      · have hnot : 2 * m + 1 ∉ rootSetQ m := by
          simp [rootSetQ]
        rw [Finset.card_insert_of_notMem hnot, ih.2]

noncomputable def pPolyRaw (m : ℕ) : Polynomial ℝ :=
  ∏ r ∈ rootSetP m, (Polynomial.X - Polynomial.C (r : ℝ))

noncomputable def qPolyRaw (m : ℕ) : Polynomial ℝ :=
  ∏ r ∈ rootSetQ m, (Polynomial.X - Polynomial.C (r : ℝ))

lemma pPolyRaw_deg (m : ℕ) : (pPolyRaw m).natDegree ≤ m := by
  unfold pPolyRaw
  refine (Polynomial.natDegree_prod_le _ _).trans (le_of_eq ?_)
  calc ∑ r ∈ rootSetP m, (Polynomial.X - Polynomial.C (r : ℝ)).natDegree
      = ∑ _ ∈ rootSetP m, 1 := Finset.sum_congr rfl fun r _ => Polynomial.natDegree_X_sub_C (r : ℝ)
    _ = (rootSetP m).card := by simp
    _ = m := (card_rootSetP_and_Q m).1

lemma qPolyRaw_deg (m : ℕ) : (qPolyRaw m).natDegree ≤ m := by
  unfold qPolyRaw
  refine (Polynomial.natDegree_prod_le _ _).trans (le_of_eq ?_)
  calc ∑ r ∈ rootSetQ m, (Polynomial.X - Polynomial.C (r : ℝ)).natDegree
      = ∑ _ ∈ rootSetQ m, 1 := Finset.sum_congr rfl fun r _ => Polynomial.natDegree_X_sub_C (r : ℝ)
    _ = (rootSetQ m).card := by simp
    _ = m := (card_rootSetP_and_Q m).2

lemma pPolyRaw_eval_zero_ne (m : ℕ) : (pPolyRaw m).eval 0 ≠ 0 := by
  unfold pPolyRaw
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro r hr
  simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc] at hr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  linarith

lemma qPolyRaw_eval_zero_ne (m : ℕ) : (qPolyRaw m).eval 0 ≠ 0 := by
  unfold qPolyRaw
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro r hr
  simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc] at hr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  linarith

private lemma prod_Icc_eq_factorial (N : ℕ) :
    (∏ r ∈ Finset.Icc 1 N, (r : ℝ)) = (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hnot : N + 1 ∉ Finset.Icc 1 N := by simp
    rw [hIcc, Finset.prod_insert hnot, ih, Nat.factorial_succ]
    push_cast; ring

lemma pPolyRaw_mul_qPolyRaw_eval_zero (m : ℕ) :
    (pPolyRaw m).eval 0 * (qPolyRaw m).eval 0 = ((2 * m).factorial : ℝ) := by
  unfold pPolyRaw qPolyRaw
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  rw [← Finset.prod_union (rootSetP_disjoint_rootSetQ m), rootSetP_union_rootSetQ]
  have hneg : ∀ r ∈ Finset.Icc 1 (2 * m), (-(r : ℝ)) = (-1 : ℝ) * (r : ℝ) := fun r _ => by ring
  rw [Finset.prod_congr rfl hneg, Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : (Finset.Icc 1 (2 * m)).card = 2 * m := by simp
  rw [hcard, pow_mul]
  simp [prod_Icc_eq_factorial]

noncomputable def PPoly (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (Real.sqrt 2 * (pPolyRaw m).eval 0)) * pPolyRaw m

noncomputable def QPoly (m : ℕ) : Polynomial ℝ :=
  Polynomial.C (1 / (Real.sqrt 2 * (qPolyRaw m).eval 0)) * qPolyRaw m

lemma PPoly_deg (m : ℕ) : (PPoly m).natDegree ≤ m :=
  (Polynomial.natDegree_C_mul_le _ _).trans (pPolyRaw_deg m)

lemma QPoly_deg (m : ℕ) : (QPoly m).natDegree ≤ m :=
  (Polynomial.natDegree_C_mul_le _ _).trans (qPolyRaw_deg m)

lemma PPoly_eval_zero (m : ℕ) : (PPoly m).eval 0 = 1 / Real.sqrt 2 := by
  unfold PPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hp := pPolyRaw_eval_zero_ne m
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hp, hs]

lemma QPoly_eval_zero (m : ℕ) : (QPoly m).eval 0 = 1 / Real.sqrt 2 := by
  unfold QPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hq := qPolyRaw_eval_zero_ne m
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hq, hs]

lemma PPoly_eval_root {m t : ℕ} (ht : t ∈ rootSetP m) : (PPoly m).eval (t : ℝ) = 0 := by
  unfold PPoly pPolyRaw
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X]
  have hprod : (∏ r ∈ rootSetP m, ((t : ℝ) - (r : ℝ))) = 0 := Finset.prod_eq_zero ht (by simp)
  rw [hprod, mul_zero]

lemma QPoly_eval_root {m t : ℕ} (ht : t ∈ rootSetQ m) : (QPoly m).eval (t : ℝ) = 0 := by
  unfold QPoly qPolyRaw
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X]
  have hprod : (∏ r ∈ rootSetQ m, ((t : ℝ) - (r : ℝ))) = 0 := Finset.prod_eq_zero ht (by simp)
  rw [hprod, mul_zero]

noncomputable def DPoly (m l : ℕ) : Polynomial ℝ :=
  if Even m then
    Polynomial.C (1 / (Real.sqrt 2 * (qPolyRaw l).eval 0)) *
      ∏ r ∈ (rootSetQ l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ))
  else
    Polynomial.C (1 / (Real.sqrt 2 * (pPolyRaw l).eval 0)) *
      ∏ r ∈ (rootSetP l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ))

noncomputable def CPoly (m l : ℕ) : Polynomial ℝ :=
  Polynomial.X * DPoly m l

lemma two_mul_add_two_mem_rootSet {m l : ℕ} (hml : m < l) :
    (Even m → 2 * m + 2 ∈ rootSetQ l) ∧ (¬ Even m → 2 * m + 2 ∈ rootSetP l) := by
  constructor
  · intro hm
    rcases hm with ⟨k, hk⟩
    simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro hm
    rw [Nat.not_even_iff_odd] at hm
    rcases hm with ⟨k, hk⟩
    simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]
    omega

lemma linear_mul_DPoly {m l : ℕ} (hml : m < l) :
    (Polynomial.X - Polynomial.C ((2 * m + 2 : ℕ) : ℝ)) * DPoly m l =
      if Even m then QPoly l else PPoly l := by
  have hmem := two_mul_add_two_mem_rootSet hml
  by_cases hm : Even m
  · simp only [DPoly, hm, ↓reduceIte, QPoly, qPolyRaw]
    have h2 : 2 * m + 2 ∈ rootSetQ l := hmem.1 hm
    calc (Polynomial.X - Polynomial.C ((2 * m + 2 : ℕ) : ℝ)) *
          (Polynomial.C (1 / (Real.sqrt 2 * (qPolyRaw l).eval 0)) *
            ∏ r ∈ (rootSetQ l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ)))
        = Polynomial.C (1 / (Real.sqrt 2 * (qPolyRaw l).eval 0)) *
            ((Polynomial.X - Polynomial.C ((2 * m + 2 : ℕ) : ℝ)) *
              ∏ r ∈ (rootSetQ l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ))) := by ring
      _ = Polynomial.C (1 / (Real.sqrt 2 * (qPolyRaw l).eval 0)) *
            ∏ r ∈ rootSetQ l, (Polynomial.X - Polynomial.C (r : ℝ)) := by
          rw [Finset.mul_prod_erase (rootSetQ l) (fun r => Polynomial.X - Polynomial.C (r : ℝ)) h2]
  · simp only [DPoly, hm, ↓reduceIte, PPoly, pPolyRaw]
    have h2 : 2 * m + 2 ∈ rootSetP l := hmem.2 hm
    calc (Polynomial.X - Polynomial.C ((2 * m + 2 : ℕ) : ℝ)) *
          (Polynomial.C (1 / (Real.sqrt 2 * (pPolyRaw l).eval 0)) *
            ∏ r ∈ (rootSetP l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ)))
        = Polynomial.C (1 / (Real.sqrt 2 * (pPolyRaw l).eval 0)) *
            ((Polynomial.X - Polynomial.C ((2 * m + 2 : ℕ) : ℝ)) *
              ∏ r ∈ (rootSetP l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ))) := by ring
      _ = Polynomial.C (1 / (Real.sqrt 2 * (pPolyRaw l).eval 0)) *
            ∏ r ∈ rootSetP l, (Polynomial.X - Polynomial.C (r : ℝ)) := by
          rw [Finset.mul_prod_erase (rootSetP l) (fun r => Polynomial.X - Polynomial.C (r : ℝ)) h2]

lemma CPoly_deg {m l : ℕ} (hml : m < l) : (CPoly m l).natDegree ≤ l := by
  have hmem := two_mul_add_two_mem_rootSet hml
  have hD : (DPoly m l).natDegree ≤ l - 1 := by
    by_cases hm : Even m
    · simp only [DPoly, hm, ↓reduceIte]
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine (Polynomial.natDegree_prod_le _ _).trans (le_of_eq ?_)
      have hcard : ((rootSetQ l).erase (2 * m + 2)).card = l - 1 := by
        rw [Finset.card_erase_of_mem (hmem.1 hm), (card_rootSetP_and_Q l).2]
      calc ∑ r ∈ (rootSetQ l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ)).natDegree
          = ∑ _ ∈ (rootSetQ l).erase (2 * m + 2), 1 :=
            Finset.sum_congr rfl fun r _ => Polynomial.natDegree_X_sub_C (r : ℝ)
        _ = ((rootSetQ l).erase (2 * m + 2)).card := by simp
        _ = l - 1 := hcard
    · simp only [DPoly, hm, ↓reduceIte]
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine (Polynomial.natDegree_prod_le _ _).trans (le_of_eq ?_)
      have hcard : ((rootSetP l).erase (2 * m + 2)).card = l - 1 := by
        rw [Finset.card_erase_of_mem (hmem.2 hm), (card_rootSetP_and_Q l).1]
      calc ∑ r ∈ (rootSetP l).erase (2 * m + 2), (Polynomial.X - Polynomial.C (r : ℝ)).natDegree
          = ∑ _ ∈ (rootSetP l).erase (2 * m + 2), 1 :=
            Finset.sum_congr rfl fun r _ => Polynomial.natDegree_X_sub_C (r : ℝ)
        _ = ((rootSetP l).erase (2 * m + 2)).card := by simp
        _ = l - 1 := hcard
  unfold CPoly
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_X]
  omega

lemma CPoly_eval_zero (m l : ℕ) : (CPoly m l).eval 0 = 0 := by
  simp [CPoly]

lemma CPoly_eval_root {m l t : ℕ} (hml : m < l) (ht : t ≤ 2 * m)
    (hroot : (Even m → t ∈ rootSetQ m) ∧ (¬ Even m → t ∈ rootSetP m)) :
    (CPoly m l).eval (t : ℝ) = 0 := by
  have heq := congrArg (Polynomial.eval (t : ℝ)) (linear_mul_DPoly hml)
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heq
  have hne : (t : ℝ) - ((2 * m + 2 : ℕ) : ℝ) ≠ 0 := by
    have : (t : ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : t < 2 * m + 2)
    linarith
  have hR : (if Even m then QPoly l else PPoly l).eval (t : ℝ) = 0 := by
    by_cases hm : Even m
    · simp only [hm, ↓reduceIte]
      exact QPoly_eval_root (rootSetQ_mono hml.le (hroot.1 hm))
    · simp only [hm, ↓reduceIte]
      exact PPoly_eval_root (rootSetP_mono hml.le (hroot.2 hm))
  rw [hR] at heq
  have hD : (DPoly m l).eval (t : ℝ) = 0 := (mul_eq_zero.mp heq).resolve_left hne
  simp [CPoly, hD]

lemma CPoly_eval_endpoint {m l : ℕ} (hml : m < l) :
    (CPoly m l).eval ((2 * m + 1 : ℕ) : ℝ) / ((2 * m + 1 : ℕ) : ℝ) =
      -(if Even m then (QPoly l).eval ((2 * m + 1 : ℕ) : ℝ) else (PPoly l).eval ((2 * m + 1 : ℕ) : ℝ)) := by
  have heq := congrArg (Polynomial.eval ((2 * m + 1 : ℕ) : ℝ)) (linear_mul_DPoly hml)
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heq
  have hdiff : ((2 * m + 1 : ℕ) : ℝ) - ((2 * m + 2 : ℕ) : ℝ) = -1 := by
    push_cast; ring
  rw [hdiff] at heq
  have hD : (DPoly m l).eval ((2 * m + 1 : ℕ) : ℝ) =
      -(if Even m then (QPoly l).eval ((2 * m + 1 : ℕ) : ℝ) else (PPoly l).eval ((2 * m + 1 : ℕ) : ℝ)) := by
    by_cases hm : Even m <;> simp only [hm, ↓reduceIte] at heq ⊢ <;> linarith
  have hpos : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [CPoly, Polynomial.eval_mul, Polynomial.eval_X]
  rw [mul_div_cancel_left₀ _ hpos, hD]

noncomputable def pVecPoly (M l : ℕ) (c : Fin (M + 1)) : Polynomial ℝ :=
  Fin.cases (PPoly l) (fun j : Fin M =>
    if (j : ℕ) < l ∧ ¬ Even (j : ℕ) then
      Polynomial.C (1 / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) * CPoly j l
    else if (j : ℕ) = l ∧ Even (j : ℕ) then
      PPoly l
    else 0) c

noncomputable def qVecPoly (M l : ℕ) (c : Fin (M + 1)) : Polynomial ℝ :=
  Fin.cases (QPoly l) (fun j : Fin M =>
    if (j : ℕ) < l ∧ Even (j : ℕ) then
      Polynomial.C (1 / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) * CPoly j l
    else if (j : ℕ) = l ∧ ¬ Even (j : ℕ) then
      QPoly l
    else 0) c

lemma pVecPoly_deg (M l : ℕ) (c : Fin (M + 1)) : (pVecPoly M l c).natDegree ≤ l := by
  refine Fin.cases ?_ ?_ c
  · simpa [pVecPoly] using PPoly_deg l
  · intro j
    simp only [pVecPoly, Fin.cases_succ]
    split_ifs with h1 h2
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (CPoly_deg h1.1)
    · exact PPoly_deg l
    · simp

lemma qVecPoly_deg (M l : ℕ) (c : Fin (M + 1)) : (qVecPoly M l c).natDegree ≤ l := by
  refine Fin.cases ?_ ?_ c
  · simpa [qVecPoly] using QPoly_deg l
  · intro j
    simp only [qVecPoly, Fin.cases_succ]
    split_ifs with h1 h2
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (CPoly_deg h1.1)
    · exact QPoly_deg l
    · simp

noncomputable def LVec (M l : ℕ) (a : Fin (2 * l + 1 + 1)) (c : Fin (M + 1)) : ℝ :=
  ∑ t : Fin (2 * l + 1 + 1), (krawtchouk (2 * l + 1) t a : ℝ) * (pVecPoly M l c).eval (t : ℝ)

noncomputable def UVec (M l : ℕ) (a : Fin (2 * l + 1 + 1)) (c : Fin (M + 1)) : ℝ :=
  ∑ t : Fin (2 * l + 1 + 1), (krawtchouk (2 * l + 1) t a : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * (qVecPoly M l c).eval (t : ℝ))

noncomputable def WVec (M l : ℕ) (a : Fin (2 * l + 1 + 1)) (c : Fin (M + 1)) : ℝ :=
  LVec M l a c + UVec M l a c

lemma LVec_eq_zero_of_gt {M l : ℕ} {a : Fin (2 * l + 1 + 1)} (ha : l < (a : ℕ)) (c : Fin (M + 1)) :
    LVec M l a c = 0 :=
  L_vanish_of_gt l (pVecPoly M l c) (pVecPoly_deg M l c) a ha

lemma UVec_eq_zero_of_le {M l : ℕ} {a : Fin (2 * l + 1 + 1)} (ha : (a : ℕ) ≤ l) (c : Fin (M + 1)) :
    UVec M l a c = 0 :=
  U_vanish_of_le l (qVecPoly M l c) (qVecPoly_deg M l c) a ha

noncomputable def cML (M m l : ℕ) (t : ℝ) : ℝ :=
  ∑ c : Fin (M + 1),
    ((pVecPoly M m c).eval t * (qVecPoly M l c).eval t +
     (qVecPoly M m c).eval t * (pVecPoly M l c).eval t)

lemma cML_comm (M m l : ℕ) (t : ℝ) : cML M m l t = cML M l m t := by
  unfold cML
  refine Finset.sum_congr rfl fun c _ => by ring

lemma cML_self (M m : ℕ) (t : ℝ) :
    cML M m m t = 2 * (PPoly m).eval t * (QPoly m).eval t := by
  unfold cML
  rw [Fin.sum_univ_succ]
  have hrest : ∑ j : Fin M,
      ((pVecPoly M m j.succ).eval t * (qVecPoly M m j.succ).eval t +
       (qVecPoly M m j.succ).eval t * (pVecPoly M m j.succ).eval t) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [pVecPoly, qVecPoly, Fin.cases_succ]
    by_cases h1 : (j : ℕ) < m
    · by_cases h3 : Even (j : ℕ) <;> simp [h1, h3, Nat.ne_of_lt h1]
    · by_cases h2 : (j : ℕ) = m
      · by_cases hm : Even m
        · simp [h2, hm]
        · simp [h2, hm]
      · simp [h1, h2]
  rw [hrest, add_zero]
  simp [pVecPoly, qVecPoly]
  ring

lemma cML_lt {M m l : ℕ} (hml : m < l) (hlM : l ≤ M) (t : ℝ) :
    cML M m l t = (PPoly m).eval t * (QPoly l).eval t + (QPoly m).eval t * (PPoly l).eval t +
      (if Even m then (PPoly m).eval t else (QPoly m).eval t) *
        ((CPoly m l).eval t / ((2 * m + 1 : ℕ) : ℝ)) := by
  unfold cML
  rw [Fin.sum_univ_succ]
  let mFin : Fin M := ⟨m, lt_of_lt_of_le hml hlM⟩
  have hsingle : ∑ j : Fin M,
      ((pVecPoly M m j.succ).eval t * (qVecPoly M l j.succ).eval t +
       (qVecPoly M m j.succ).eval t * (pVecPoly M l j.succ).eval t) =
      (if Even m then (PPoly m).eval t else (QPoly m).eval t) *
        ((CPoly m l).eval t / ((2 * m + 1 : ℕ) : ℝ)) := by
    rw [Finset.sum_eq_single mFin]
    · simp only [mFin, pVecPoly, qVecPoly, Fin.cases_succ]
      by_cases hm : Even m
      · simp [hm, hml, div_eq_mul_inv, mul_comm, mul_assoc]
      · simp [hm, hml, div_eq_mul_inv, mul_comm, mul_assoc]
    · intro j _ hne
      have hj : (j : ℕ) ≠ m := fun h => hne (Fin.ext h)
      simp only [pVecPoly, qVecPoly, Fin.cases_succ]
      split_ifs <;> simp_all
      all_goals omega
    · intro hnot; exact False.elim (hnot (Finset.mem_univ mFin))
  rw [hsingle]
  simp only [pVecPoly, qVecPoly, Fin.cases_zero]

lemma cML_eval_zero {M m l : ℕ} (hml : m ≤ l) (hlM : l ≤ M) :
    cML M m l 0 = 1 := by
  by_cases heq : m = l
  · subst heq
    rw [cML_self, PPoly_eval_zero, QPoly_eval_zero]
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    linarith
  · have hlt : m < l := lt_of_le_of_ne hml heq
    rw [cML_lt hlt hlM, PPoly_eval_zero, QPoly_eval_zero, PPoly_eval_zero, QPoly_eval_zero,
      CPoly_eval_zero, zero_div, mul_zero, add_zero]
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    linarith

lemma cML_self_zero_of_interior {M m t : ℕ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * m) :
    cML M m m (t : ℝ) = 0 := by
  rw [cML_self]
  have hu : t ∈ rootSetP m ∪ rootSetQ m := by
    rw [rootSetP_union_rootSetQ, Finset.mem_Icc]
    exact ⟨ht1, ht2⟩
  rcases Finset.mem_union.mp hu with hP | hQ
  · rw [PPoly_eval_root hP]; simp
  · rw [QPoly_eval_root hQ]; simp

lemma cML_lt_zero_of_le {M m l t : ℕ} (hml : m < l) (hlM : l ≤ M)
    (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * m + 1) :
    cML M m l (t : ℝ) = 0 := by
  rw [cML_lt hml hlM]
  by_cases htop : t = 2 * m + 1
  · subst htop
    rw [CPoly_eval_endpoint hml]
    by_cases hm : Even m
    · have hP : (2 * m + 1) ∈ rootSetP l := by
        rcases hm with ⟨k, hk⟩
        simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [PPoly_eval_root hP]
      simp [hm]
    · have hQ : (2 * m + 1) ∈ rootSetQ l := by
        rw [Nat.not_even_iff_odd] at hm
        rcases hm with ⟨k, hk⟩
        simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [QPoly_eval_root hQ]
      simp [hm]
  · have ht_le : t ≤ 2 * m := by omega
    have hu : t ∈ rootSetP m ∪ rootSetQ m := by
      rw [rootSetP_union_rootSetQ, Finset.mem_Icc]
      exact ⟨ht1, ht_le⟩
    rcases Finset.mem_union.mp hu with hP | hQ
    · have hPl : t ∈ rootSetP l := rootSetP_mono hml.le hP
      rw [PPoly_eval_root hP, PPoly_eval_root hPl]
      by_cases hm : Even m
      · simp [hm]
      · have hC : (CPoly m l).eval (t : ℝ) = 0 := CPoly_eval_root hml ht_le
          ⟨fun h => False.elim (hm h), fun _ => hP⟩
        simp [hm, hC]
    · have hQl : t ∈ rootSetQ l := rootSetQ_mono hml.le hQ
      rw [QPoly_eval_root hQ, QPoly_eval_root hQl]
      by_cases hm : Even m
      · have hC : (CPoly m l).eval (t : ℝ) = 0 := CPoly_eval_root hml ht_le
          ⟨fun _ => hQ, fun h => False.elim (h hm)⟩
        simp [hm, hC]
      · simp [hm]

lemma odd_cross_moment_identity {n' M m l : ℕ} (hmM : m ≤ M) (hlM : l ≤ M)
    (A B : Finset (Fin n')) (hA : A.card = 2 * m + 1) (hB : B.card = 2 * l + 1) (hne : A ≠ B) :
    (∑ S : Qubits n', if majorityBit A S ≠ majorityBit B S then
      (2 : ℝ) ^ (-(n' : ℤ)) * ∑ c : Fin (M + 1),
        WVec M m ⟨(A.filter fun i => S i).card, by
          have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
        WVec M l ⟨(B.filter fun i => S i).card, by
          have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c
      else 0) = 1 := by
  have hpoint : ∀ S : Qubits n',
      (if majorityBit A S ≠ majorityBit B S then
        ∑ c : Fin (M + 1),
          WVec M m ⟨(A.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
          WVec M l ⟨(B.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c
        else 0) =
      ∑ c : Fin (M + 1),
        (LVec M m ⟨(A.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
         UVec M l ⟨(B.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c +
         UVec M m ⟨(A.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
         LVec M l ⟨(B.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c) := by
    intro S
    let a : Fin (2 * m + 1 + 1) := ⟨(A.filter fun i => S i).card, by
      have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩
    let b : Fin (2 * l + 1 + 1) := ⟨(B.filter fun i => S i).card, by
      have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩
    have hmA : majorityBit A S = decide ((a : ℕ) ≤ m) := by
      simp only [majorityBit, a, hA, decide_eq_decide]
      omega
    have hmB : majorityBit B S = decide ((b : ℕ) ≤ l) := by
      simp only [majorityBit, b, hB, decide_eq_decide]
      omega
    by_cases ha : (a : ℕ) ≤ m <;> by_cases hb : (b : ℕ) ≤ l
    · have hmab : majorityBit A S = majorityBit B S := by simp [hmA, hmB, ha, hb]
      simp only [hmab, ne_eq, not_true_eq_false, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [UVec_eq_zero_of_le ha c, UVec_eq_zero_of_le hb c]; ring
    · have hmab : majorityBit A S ≠ majorityBit B S := by simp [hmA, hmB, ha, hb]
      simp only [hmab, ne_eq, not_false_eq_true, ↓reduceIte]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hbgt : l < (b : ℕ) := Nat.lt_of_not_ge hb
      rw [WVec, WVec, UVec_eq_zero_of_le ha c, LVec_eq_zero_of_gt hbgt c]; ring
    · have hmab : majorityBit A S ≠ majorityBit B S := by simp [hmA, hmB, ha, hb]
      simp only [hmab, ne_eq, not_false_eq_true, ↓reduceIte]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hagt : m < (a : ℕ) := Nat.lt_of_not_ge ha
      rw [WVec, WVec, LVec_eq_zero_of_gt hagt c, UVec_eq_zero_of_le hb c]; ring
    · have hmab : majorityBit A S = majorityBit B S := by simp [hmA, hmB, ha, hb]
      simp only [hmab, ne_eq, not_true_eq_false, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun c _ => ?_
      have hagt : m < (a : ℕ) := Nat.lt_of_not_ge ha
      have hbgt : l < (b : ℕ) := Nat.lt_of_not_ge hb
      rw [LVec_eq_zero_of_gt hagt c, LVec_eq_zero_of_gt hbgt c]; ring
  have hsum_rew :
      (∑ S : Qubits n', if majorityBit A S ≠ majorityBit B S then
        (2 : ℝ) ^ (-(n' : ℤ)) * ∑ c : Fin (M + 1),
          WVec M m ⟨(A.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
          WVec M l ⟨(B.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c
        else 0) =
      (2 : ℝ) ^ (-(n' : ℤ)) * ∑ S : Qubits n', ∑ c : Fin (M + 1),
        (LVec M m ⟨(A.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
         UVec M l ⟨(B.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c +
         UVec M m ⟨(A.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
         LVec M l ⟨(B.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs with h
    · rw [← hpoint S]; simp [h]
    · have h0 := hpoint S; simp only [h, ↓reduceIte] at h0; rw [← h0, mul_zero]
  rw [hsum_rew, Finset.sum_comm]
  have hcoord : ∀ c : Fin (M + 1),
      (2 : ℝ) ^ (-(n' : ℤ)) * ∑ S : Qubits n',
        (LVec M m ⟨(A.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
         UVec M l ⟨(B.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c +
         UVec M m ⟨(A.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := A) (p := fun i => S i); rw [hA] at this; omega⟩ c *
         LVec M l ⟨(B.filter fun i => S i).card, by
            have := Finset.card_filter_le (s := B) (p := fun i => S i); rw [hB] at this; omega⟩ c) =
      ∑ t : Fin (2 * min m l + 1 + 1),
        (-1 : ℝ) ^ (t : ℕ) * (((A ∩ B).card.choose (t : ℕ) : ℕ) : ℝ) *
          ((pVecPoly M m c).eval (t : ℝ) * (qVecPoly M l c).eval (t : ℝ) +
           (qVecPoly M m c).eval (t : ℝ) * (pVecPoly M l c).eval (t : ℝ)) := by
    intro c
    unfold LVec UVec
    have hexp : ∀ S : Qubits n',
        (∑ u : Fin (2 * m + 1 + 1), (krawtchouk (2 * m + 1) u ((A.filter fun i => S i).card) : ℝ) *
            (pVecPoly M m c).eval (u : ℝ)) *
          (∑ v : Fin (2 * l + 1 + 1), (krawtchouk (2 * l + 1) v ((B.filter fun i => S i).card) : ℝ) *
            ((-1 : ℝ) ^ (v : ℕ) * (qVecPoly M l c).eval (v : ℝ))) +
        (∑ u : Fin (2 * m + 1 + 1), (krawtchouk (2 * m + 1) u ((A.filter fun i => S i).card) : ℝ) *
            ((-1 : ℝ) ^ (u : ℕ) * (qVecPoly M m c).eval (u : ℝ))) *
          (∑ v : Fin (2 * l + 1 + 1), (krawtchouk (2 * l + 1) v ((B.filter fun i => S i).card) : ℝ) *
            (pVecPoly M l c).eval (v : ℝ)) =
        ∑ u : Fin (2 * m + 1 + 1), ∑ v : Fin (2 * l + 1 + 1),
          ((krawtchouk (2 * m + 1) u ((A.filter fun i => S i).card) : ℝ) *
           (krawtchouk (2 * l + 1) v ((B.filter fun i => S i).card) : ℝ)) *
          ((-1 : ℝ) ^ (v : ℕ) * (pVecPoly M m c).eval (u : ℝ) * (qVecPoly M l c).eval (v : ℝ) +
           (-1 : ℝ) ^ (u : ℕ) * (qVecPoly M m c).eval (u : ℝ) * (pVecPoly M l c).eval (v : ℝ)) := by
      intro S
      simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    simp_rw [hexp]
    rw [Finset.sum_comm, Finset.mul_sum]
    have hu_swap : ∑ u : Fin (2 * m + 1 + 1),
        (2 : ℝ) ^ (-(n' : ℤ)) * ∑ S : Qubits n', ∑ v : Fin (2 * l + 1 + 1),
          ((krawtchouk (2 * m + 1) u ((A.filter fun i => S i).card) : ℝ) *
           (krawtchouk (2 * l + 1) v ((B.filter fun i => S i).card) : ℝ)) *
          ((-1 : ℝ) ^ (v : ℕ) * (pVecPoly M m c).eval (u : ℝ) * (qVecPoly M l c).eval (v : ℝ) +
           (-1 : ℝ) ^ (u : ℕ) * (qVecPoly M m c).eval (u : ℝ) * (pVecPoly M l c).eval (v : ℝ)) =
        ∑ u : Fin (2 * m + 1 + 1), ∑ v : Fin (2 * l + 1 + 1),
          (if (u : ℕ) = (v : ℕ) then (((A ∩ B).card.choose (u : ℕ) : ℕ) : ℝ) else 0) *
          ((-1 : ℝ) ^ (v : ℕ) * (pVecPoly M m c).eval (u : ℝ) * (qVecPoly M l c).eval (v : ℝ) +
           (-1 : ℝ) ^ (u : ℕ) * (qVecPoly M m c).eval (u : ℝ) * (pVecPoly M l c).eval (v : ℝ)) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← Finset.sum_mul, ← mul_assoc, krawtchouk_cross_expectation A B hA hB u v]
    rw [hu_swap]
    have hdiag : ∀ u : Fin (2 * m + 1 + 1),
        (∑ v : Fin (2 * l + 1 + 1),
          (if (u : ℕ) = (v : ℕ) then (((A ∩ B).card.choose (u : ℕ) : ℕ) : ℝ) else 0) *
          ((-1 : ℝ) ^ (v : ℕ) * (pVecPoly M m c).eval (u : ℝ) * (qVecPoly M l c).eval (v : ℝ) +
           (-1 : ℝ) ^ (u : ℕ) * (qVecPoly M m c).eval (u : ℝ) * (pVecPoly M l c).eval (v : ℝ))) =
        if h : (u : ℕ) ≤ 2 * l + 1 then
          (-1 : ℝ) ^ (u : ℕ) * (((A ∩ B).card.choose (u : ℕ) : ℕ) : ℝ) *
            ((pVecPoly M m c).eval (u : ℝ) * (qVecPoly M l c).eval (u : ℝ) +
             (qVecPoly M m c).eval (u : ℝ) * (pVecPoly M l c).eval (u : ℝ))
        else 0 := by
      intro u
      by_cases h : (u : ℕ) ≤ 2 * l + 1
      · simp only [h, ↓reduceDIte]
        rw [Finset.sum_eq_single (⟨u, by omega⟩ : Fin (2 * l + 1 + 1))]
        · simp; ring
        · intro v _ hne
          have hne' : (u : ℕ) ≠ (v : ℕ) := fun heq => hne (Fin.ext heq.symm)
          simp [hne']
        · intro hnot; exact False.elim (hnot (Finset.mem_univ _))
      · simp only [h, ↓reduceDIte]
        refine Finset.sum_eq_zero fun v _ => ?_
        have hne' : (u : ℕ) ≠ (v : ℕ) := by have := v.isLt; omega
        simp [hne']
    simp_rw [hdiag]
    by_cases hml : m ≤ l
    · exact Fintype.sum_equiv (finCongr (by omega : 2 * m + 1 + 1 = 2 * min m l + 1 + 1)) _ _ fun u => by
        have hu : (u : ℕ) ≤ 2 * l + 1 := by have := u.isLt; omega
        simp [hu]
    · have hlm : l ≤ m := Nat.le_of_not_ge hml
      have hfilt :
          (∑ u : Fin (2 * m + 1 + 1), if h : (u : ℕ) ≤ 2 * l + 1 then
            (-1 : ℝ) ^ (u : ℕ) * (((A ∩ B).card.choose (u : ℕ) : ℕ) : ℝ) *
              ((pVecPoly M m c).eval (u : ℝ) * (qVecPoly M l c).eval (u : ℝ) +
               (qVecPoly M m c).eval (u : ℝ) * (pVecPoly M l c).eval (u : ℝ))
            else 0) =
          ∑ u ∈ Finset.univ.filter (fun u : Fin (2 * m + 1 + 1) => (u : ℕ) ≤ 2 * l + 1),
            (-1 : ℝ) ^ (u : ℕ) * (((A ∩ B).card.choose (u : ℕ) : ℕ) : ℝ) *
              ((pVecPoly M m c).eval (u : ℝ) * (qVecPoly M l c).eval (u : ℝ) +
               (qVecPoly M m c).eval (u : ℝ) * (pVecPoly M l c).eval (u : ℝ)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ => ?_
        split_ifs with h <;> rfl
      rw [hfilt]
      refine Finset.sum_bij (fun u hu => ⟨(u : ℕ), by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu; omega⟩)
        (fun u _ => Finset.mem_univ _)
        (fun u₁ u₂ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun t _ => ⟨⟨(t : ℕ), by have := t.isLt; omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := t.isLt; omega, Fin.ext rfl⟩)
        (fun u _ => by simp)
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun c _ => hcoord c, Finset.sum_comm]
  have hrew : ∑ t : Fin (2 * min m l + 1 + 1), ∑ c : Fin (M + 1),
        (-1 : ℝ) ^ (t : ℕ) * (((A ∩ B).card.choose (t : ℕ) : ℕ) : ℝ) *
          ((pVecPoly M m c).eval (t : ℝ) * (qVecPoly M l c).eval (t : ℝ) +
           (qVecPoly M m c).eval (t : ℝ) * (pVecPoly M l c).eval (t : ℝ)) =
      ∑ t : Fin (2 * min m l + 1 + 1),
        (-1 : ℝ) ^ (t : ℕ) * (((A ∩ B).card.choose (t : ℕ) : ℕ) : ℝ) * cML M m l (t : ℝ) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]; rfl
  rw [hrew]
  rw [Finset.sum_eq_single (0 : Fin (2 * min m l + 1 + 1))]
  · have hm0 : cML M m l 0 = 1 := by
      by_cases hml : m ≤ l
      · exact cML_eval_zero hml hlM
      · rw [cML_comm]; exact cML_eval_zero (Nat.le_of_not_ge hml) hmM
    simp [hm0]
  · intro t _ ht0
    have ht1 : 1 ≤ (t : ℕ) := Nat.pos_of_ne_zero (fun h => ht0 (Fin.ext h))
    by_cases hcard : (A ∩ B).card < (t : ℕ)
    · simp [Nat.choose_eq_zero_of_lt hcard]
    · have ht_le : (t : ℕ) ≤ (A ∩ B).card := Nat.le_of_not_lt hcard
      have hc0 : cML M m l (t : ℝ) = 0 := by
        by_cases heq : m = l
        · subst heq
          have hinter_lt : (A ∩ B).card < 2 * m + 1 := by
            have hle1 : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
            have hle2 : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
            by_contra hge
            have heq1 : (A ∩ B).card = A.card := by omega
            have heq2 : (A ∩ B).card = B.card := by omega
            have hsub1 : A ∩ B = A := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
            have hsub2 : A ∩ B = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
            exact hne (hsub1.symm.trans hsub2)
          exact cML_self_zero_of_interior ht1 (by omega)
        · by_cases hml : m < l
          · have ht_min : (t : ℕ) ≤ 2 * m + 1 := by
              have := t.isLt; simp [min_eq_left hml.le] at this; omega
            exact cML_lt_zero_of_le hml hlM ht1 ht_min
          · have hlm : l < m := by omega
            rw [cML_comm]
            have ht_min : (t : ℕ) ≤ 2 * l + 1 := by
              have := t.isLt; simp [min_eq_right hlm.le] at this; omega
            exact cML_lt_zero_of_le hlm hmM ht1 ht_min
      rw [hc0, mul_zero]
  · intro hnot; exact False.elim (hnot (Finset.mem_univ _))

/-! ### Step 4: Block pairing, pointwise bounds, and logarithmic energy cost -/

noncomputable def compProd (N t : ℕ) : ℝ :=
  ∏ u ∈ (Finset.Icc 1 N).erase t, |(t : ℝ) - (u : ℝ)|

lemma compProd_pos (N t : ℕ) : 0 < compProd N t := by
  unfold compProd
  refine Finset.prod_pos fun u hu => ?_
  have hne : u ≠ t := (Finset.mem_erase.mp hu).1
  have hneR : (t : ℝ) ≠ (u : ℝ) := by
    intro h; apply hne; exact_mod_cast h.symm
  exact abs_pos.mpr (sub_ne_zero.mpr hneR)

lemma compProd_zero (N : ℕ) : compProd N 0 = (N.factorial : ℝ) := by
  unfold compProd
  have h0 : 0 ∉ Finset.Icc 1 N := by simp
  rw [Finset.erase_eq_of_notMem h0]
  have hrew : ∀ u ∈ Finset.Icc 1 N, |((0 : ℕ) : ℝ) - (u : ℝ)| = (u : ℝ) := fun u _ => by
    rw [Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg u)]
  rw [Finset.prod_congr rfl hrew, prod_Icc_eq_factorial]

lemma compProd_succ (N : ℕ) : compProd N (N + 1) = (N.factorial : ℝ) := by
  unfold compProd
  have hN : N + 1 ∉ Finset.Icc 1 N := by simp
  rw [Finset.erase_eq_of_notMem hN]
  have hbij : (∏ u ∈ Finset.Icc 1 N, |((N + 1 : ℕ) : ℝ) - (u : ℝ)|) = ∏ v ∈ Finset.Icc 1 N, (v : ℝ) := by
    refine Finset.prod_bij (fun u _ => N + 1 - u)
      (fun u hu => by simp only [Finset.mem_Icc] at hu ⊢; omega)
      (fun u₁ u₂ hu₁ hu₂ h => by simp only [Finset.mem_Icc] at hu₁ hu₂; omega)
      (fun v hv => ⟨N + 1 - v, by simp only [Finset.mem_Icc] at hv ⊢; omega, by simp only [Finset.mem_Icc] at hv; omega⟩)
      (fun u hu => by
        simp only [Finset.mem_Icc] at hu
        have hle : (u : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : u ≤ N + 1)
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        rw [Nat.cast_sub (by omega : u ≤ N + 1)])
  rw [hbij, prod_Icc_eq_factorial]

lemma compProd_interior (N t : ℕ) (ht1 : 1 ≤ t) (htN : t ≤ N) :
    compProd N t = ((t - 1).factorial : ℝ) * ((N - t).factorial : ℝ) := by
  unfold compProd
  have hpart : (Finset.Icc 1 N).erase t = Finset.Icc 1 (t - 1) ∪ Finset.Icc (t + 1) N := by
    ext u
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (t - 1)) (Finset.Icc (t + 1) N) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [Finset.mem_Icc] at hu1 hu2
    omega
  rw [hpart, Finset.prod_union hdisj]
  have hL : (∏ u ∈ Finset.Icc 1 (t - 1), |(t : ℝ) - (u : ℝ)|) = ((t - 1).factorial : ℝ) := by
    have hbij : (∏ u ∈ Finset.Icc 1 (t - 1), |(t : ℝ) - (u : ℝ)|) = ∏ v ∈ Finset.Icc 1 (t - 1), (v : ℝ) := by
      refine Finset.prod_bij (fun u _ => t - u)
        (fun u hu => by simp only [Finset.mem_Icc] at hu ⊢; omega)
        (fun u₁ u₂ hu₁ hu₂ h => by simp only [Finset.mem_Icc] at hu₁ hu₂; omega)
        (fun v hv => ⟨t - v, by simp only [Finset.mem_Icc] at hv ⊢; omega, by simp only [Finset.mem_Icc] at hv; omega⟩)
        (fun u hu => by
          simp only [Finset.mem_Icc] at hu
          have hle : (u : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : u ≤ t)
          rw [abs_of_nonneg (sub_nonneg.mpr hle), Nat.cast_sub (by omega : u ≤ t)])
    rw [hbij, prod_Icc_eq_factorial]
  have hR : (∏ u ∈ Finset.Icc (t + 1) N, |(t : ℝ) - (u : ℝ)|) = ((N - t).factorial : ℝ) := by
    have hbij : (∏ u ∈ Finset.Icc (t + 1) N, |(t : ℝ) - (u : ℝ)|) = ∏ v ∈ Finset.Icc 1 (N - t), (v : ℝ) := by
      refine Finset.prod_bij (fun u _ => u - t)
        (fun u hu => by simp only [Finset.mem_Icc] at hu ⊢; omega)
        (fun u₁ u₂ hu₁ hu₂ h => by simp only [Finset.mem_Icc] at hu₁ hu₂; omega)
        (fun v hv => ⟨t + v, by simp only [Finset.mem_Icc] at hv ⊢; omega, by simp only [Finset.mem_Icc] at hv; omega⟩)
        (fun u hu => by
          simp only [Finset.mem_Icc] at hu
          have hle : (t : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : t ≤ u)
          rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub, Nat.cast_sub (by omega : t ≤ u)])
    rw [hbij, prod_Icc_eq_factorial]
  rw [hL, hR]

lemma choose_mul_compProd_le {l : ℕ} (hl : 1 ≤ l) (t : Fin (2 * l + 1 + 1)) :
    ((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ) ≤
      4 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by
  let r := 2 * l + 1
  have hr_pos : (0 : ℝ) < r := by positivity
  have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
  by_cases ht0 : (t : ℕ) = 0
  · simp only [ht0, Nat.choose_zero_right, Nat.cast_one, one_mul, compProd_zero]
    rw [div_self hfac_pos.ne']
    have hden_pos : (0 : ℝ) < ((0 + 1 : ℕ) : ℝ) * ((r - 0 + 1 : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ hden_pos, one_mul]
    have hle : ((0 + 1 : ℕ) : ℝ) * ((r - 0 + 1 : ℕ) : ℝ) ≤ 4 * (r : ℝ) := by
      have : (0 + 1) * (r - 0 + 1) ≤ 4 * r := by dsimp [r]; omega
      exact_mod_cast this
    exact hle
  · by_cases htr : (t : ℕ) = r
    · simp only [htr]
      dsimp [r]
      rw [Nat.choose_self, Nat.cast_one, one_mul, compProd_succ, div_self hfac_pos.ne']
      have hden_pos : (0 : ℝ) < ((2 * l + 1 + 1 : ℕ) : ℝ) * ((2 * l + 1 - (2 * l + 1) + 1 : ℕ) : ℝ) := by positivity
      rw [le_div_iff₀ hden_pos, one_mul]
      have hle : ((2 * l + 1 + 1 : ℕ) : ℝ) * ((2 * l + 1 - (2 * l + 1) + 1 : ℕ) : ℝ) ≤ 4 * ((2 * l + 1 : ℕ) : ℝ) := by
        have hnat_le : (2 * l + 1 + 1) * (2 * l + 1 - (2 * l + 1) + 1) ≤ 4 * (2 * l + 1) := by
          simp only [Nat.sub_self, zero_add, mul_one]; omega
        exact_mod_cast hnat_le
      exact hle
    · have ht1 : 1 ≤ (t : ℕ) := Nat.pos_of_ne_zero ht0
      have ht_le : (t : ℕ) ≤ 2 * l := by have := t.isLt; omega
      rw [compProd_interior (2 * l) (t : ℕ) ht1 ht_le]
      have hrt : 1 ≤ r - (t : ℕ) := by dsimp [r]; omega
      have hnat : r.choose (t : ℕ) * ((t : ℕ) - 1).factorial * (2 * l - (t : ℕ)).factorial * ((t : ℕ) * (r - (t : ℕ))) =
          r * (2 * l).factorial := by
        have hch := Nat.choose_mul_factorial_mul_factorial (show (t : ℕ) ≤ r by omega)
        have ht_fac : (t : ℕ).factorial = (t : ℕ) * ((t : ℕ) - 1).factorial := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero ht0
          rw [hk, Nat.factorial_succ]; simp
        have hrt_fac : (r - (t : ℕ)).factorial = (r - (t : ℕ)) * (2 * l - (t : ℕ)).factorial := by
          have hsub : r - (t : ℕ) = (2 * l - (t : ℕ)) + 1 := by dsimp [r]; omega
          rw [hsub, Nat.factorial_succ]
        have hr_fac : r.factorial = r * (2 * l).factorial := by
          dsimp [r]; rw [Nat.factorial_succ]
        calc r.choose (t : ℕ) * ((t : ℕ) - 1).factorial * (2 * l - (t : ℕ)).factorial * ((t : ℕ) * (r - (t : ℕ)))
            = r.choose (t : ℕ) * ((t : ℕ) * ((t : ℕ) - 1).factorial) * ((r - (t : ℕ)) * (2 * l - (t : ℕ)).factorial) := by ring
          _ = r.choose (t : ℕ) * (t : ℕ).factorial * (r - (t : ℕ)).factorial := by rw [← ht_fac, ← hrt_fac]
          _ = r.factorial := hch
          _ = r * (2 * l).factorial := hr_fac
      have hreal : ((r.choose (t : ℕ) : ℝ) * ((((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ))) / ((2 * l).factorial : ℝ) =
          (r : ℝ) / (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by
        have htR : ((t : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ht0
        have hrtR : ((r - (t : ℕ) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : r - (t : ℕ) ≠ 0)
        have hcast : (r.choose (t : ℕ) : ℝ) * (((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ) *
            (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) = (r : ℝ) * ((2 * l).factorial : ℝ) := by
          exact_mod_cast hnat
        field_simp [hfac_pos.ne', htR, hrtR]
        linarith [hcast]
      change (r.choose (t : ℕ) : ℝ) * ((((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ)) / ((2 * l).factorial : ℝ) ≤ _
      rw [hreal]
      have hden1 : (((t : ℕ) + 1 : ℕ) : ℝ) ≤ 2 * ((t : ℕ) : ℝ) := by
        exact_mod_cast (by omega : (t : ℕ) + 1 ≤ 2 * (t : ℕ))
      have hden2 : ((r - (t : ℕ) + 1 : ℕ) : ℝ) ≤ 2 * ((r - (t : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : r - (t : ℕ) + 1 ≤ 2 * (r - (t : ℕ)))
      have ht_pos : (0 : ℝ) < ((t : ℕ) : ℝ) := by positivity
      have hrt_pos : (0 : ℝ) < ((r - (t : ℕ) : ℕ) : ℝ) := by positivity
      have hden_pos : (0 : ℝ) < (((t : ℕ) + 1 : ℕ) : ℝ) * ((r - (t : ℕ) + 1 : ℕ) : ℝ) := by positivity
      rw [div_le_div_iff₀ (mul_pos ht_pos hrt_pos) hden_pos]
      have hmul : (((t : ℕ) + 1 : ℕ) : ℝ) * ((r - (t : ℕ) + 1 : ℕ) : ℝ) ≤
          4 * (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by
        nlinarith [hden1, hden2]
      nlinarith [hr_pos, hmul]

private lemma prod_erase_union {A B : Finset ℕ} (hdisj : Disjoint A B) (t : ℕ) (f : ℕ → ℝ) :
    (∏ u ∈ (A ∪ B).erase t, f u) = (∏ u ∈ A.erase t, f u) * (∏ u ∈ B.erase t, f u) := by
  have heq : (A ∪ B).erase t = A.erase t ∪ B.erase t := by
    ext x; simp only [Finset.mem_erase, Finset.mem_union]; tauto
  rw [heq, Finset.prod_union (hdisj.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))]

private lemma block4_ineq (a t : ℕ) :
    (∏ u ∈ ({a, a + 3} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) then (2 : ℝ) else 1) *
        (∏ u ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = a
  · subst h0
    have hL : ({t, t + 3} : Finset ℕ).erase t = {t + 3} := by ext x; simp
    have hR : ({t, t + 1, t + 2, t + 3} : Finset ℕ).erase t = {t + 1, t + 2, t + 3} := by ext x; simp
    have hmem : t ∈ ({t, t + 1, t + 2, t + 3} : Finset ℕ) := by simp
    rw [hL, hR, if_pos hmem, Finset.prod_singleton]
    rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
    have ha1 : |(t : ℝ) - ((t + 1 : ℕ) : ℝ)| = 1 := by push_cast; norm_num
    have ha2 : |(t : ℝ) - ((t + 2 : ℕ) : ℝ)| = 2 := by push_cast; norm_num
    have ha3 : |(t : ℝ) - ((t + 3 : ℕ) : ℝ)| = 3 := by push_cast; norm_num
    rw [ha1, ha2, ha3]
    push_cast; norm_num
  · by_cases h1 : t = a + 1
    · subst h1
      have hL : ({a, a + 3} : Finset ℕ).erase (a + 1) = {a, a + 3} := by ext x; simp
      have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 1) = {a, a + 2, a + 3} := by ext x; simp; omega
      have hmem : a + 1 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by simp
      rw [hL, hR, if_pos hmem]
      rw [Finset.prod_insert (by simp), Finset.prod_singleton]
      rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
      have ha0 : |((a + 1 : ℕ) : ℝ) - (a : ℝ)| = 1 := by push_cast; norm_num
      have ha2 : |((a + 1 : ℕ) : ℝ) - ((a + 2 : ℕ) : ℝ)| = 1 := by push_cast; norm_num
      have ha3 : |((a + 1 : ℕ) : ℝ) - ((a + 3 : ℕ) : ℝ)| = 2 := by push_cast; norm_num
      rw [ha0, ha2, ha3]
      push_cast; norm_num
    · by_cases h2 : t = a + 2
      · subst h2
        have hL : ({a, a + 3} : Finset ℕ).erase (a + 2) = {a, a + 3} := by ext x; simp
        have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 2) = {a, a + 1, a + 3} := by ext x; simp; omega
        have hmem : a + 2 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by simp
        rw [hL, hR, if_pos hmem]
        rw [Finset.prod_insert (by simp), Finset.prod_singleton]
        rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
        have ha0 : |((a + 2 : ℕ) : ℝ) - (a : ℝ)| = 2 := by push_cast; norm_num
        have ha1 : |((a + 2 : ℕ) : ℝ) - ((a + 1 : ℕ) : ℝ)| = 1 := by push_cast; norm_num
        have ha3 : |((a + 2 : ℕ) : ℝ) - ((a + 3 : ℕ) : ℝ)| = 1 := by push_cast; norm_num
        rw [ha0, ha1, ha3]
        push_cast; norm_num
      · by_cases h3 : t = a + 3
        · subst h3
          have hL : ({a, a + 3} : Finset ℕ).erase (a + 3) = {a} := by ext x; simp; omega
          have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 3) = {a, a + 1, a + 2} := by ext x; simp; omega
          have hmem : a + 3 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by simp
          rw [hL, hR, if_pos hmem, Finset.prod_singleton]
          rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_singleton]
          have ha0 : |((a + 3 : ℕ) : ℝ) - (a : ℝ)| = 3 := by push_cast; norm_num
          have ha1 : |((a + 3 : ℕ) : ℝ) - ((a + 1 : ℕ) : ℝ)| = 2 := by push_cast; norm_num
          have ha2 : |((a + 3 : ℕ) : ℝ) - ((a + 2 : ℕ) : ℝ)| = 1 := by push_cast; norm_num
          rw [ha0, ha1, ha2]
          push_cast; norm_num
        · have hnotL : t ∉ ({a, a + 3} : Finset ℕ) := by simp [h0, h3]
          have hnotR : t ∉ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by simp [h0, h1, h2, h3]
          rw [Finset.erase_eq_of_notMem hnotL, Finset.erase_eq_of_notMem hnotR, if_neg hnotR, one_mul]
          rw [Finset.prod_insert (by simp), Finset.prod_singleton]
          rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp),
            Finset.prod_insert (by simp), Finset.prod_singleton]
          push_cast
          have hlt_or_gt : t < a ∨ a + 3 < t := by omega
          rcases hlt_or_gt with hlt | hgt
          · have hx : (t : ℝ) < (a : ℝ) := by exact_mod_cast hlt
            rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith),
              abs_of_neg (by linarith)]
            nlinarith
          · have hx : (a : ℝ) + 3 < (t : ℝ) := by exact_mod_cast hgt
            rw [abs_of_pos (by linarith), abs_of_pos (by linarith), abs_of_pos (by linarith),
              abs_of_pos (by linarith)]
            nlinarith

private lemma pair2Left_ineq (t : ℕ) :
    (∏ u ∈ ({2} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t = 0 then (2 : ℝ) else 1) * (∏ u ∈ ({1, 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = 0
  · subst h0; norm_num
  · by_cases h1 : t = 1
    · subst h1
      have hL : ({2} : Finset ℕ).erase 1 = {2} := by ext x; simp
      have hR : ({1, 2} : Finset ℕ).erase 1 = {2} := by ext x; simp
      rw [hL, hR, if_neg h0, one_mul, Finset.prod_singleton, Finset.prod_singleton]
      norm_num
    · by_cases h2 : t = 2
      · subst h2
        have hL : ({2} : Finset ℕ).erase 2 = ∅ := by simp
        have hR : ({1, 2} : Finset ℕ).erase 2 = {1} := by ext x; simp; omega
        rw [hL, hR, if_neg h0, one_mul, Finset.prod_empty, Finset.prod_singleton]
        norm_num
      · have hL : ({2} : Finset ℕ).erase t = {2} := by ext x; simp; omega
        have hR : ({1, 2} : Finset ℕ).erase t = {1, 2} := by ext x; simp; omega
        rw [hL, hR, if_neg h0, one_mul, Finset.prod_singleton, Finset.prod_insert (by simp), Finset.prod_singleton]
        have ht3 : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 3 ≤ t)
        rw [abs_of_pos (by push_cast; linarith), abs_of_pos (by push_cast; linarith)]
        push_cast; nlinarith

private lemma pair2Right_ineq (a t : ℕ) (ht : t ≤ a + 2) :
    (∏ u ∈ ({a} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t = a + 2 then (2 : ℝ) else 1) * (∏ u ∈ ({a, a + 1} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = a
  · subst h0
    have hL : ({t} : Finset ℕ).erase t = ∅ := by simp
    have hR : ({t, t + 1} : Finset ℕ).erase t = {t + 1} := by ext x; simp
    rw [hL, hR, if_neg (by omega), one_mul, Finset.prod_empty, Finset.prod_singleton]
    push_cast; norm_num
  · by_cases h1 : t = a + 1
    · subst h1
      have hL : ({a} : Finset ℕ).erase (a + 1) = {a} := by ext x; simp
      have hR : ({a, a + 1} : Finset ℕ).erase (a + 1) = {a} := by ext x; simp; omega
      rw [hL, hR, if_neg (by omega), one_mul, Finset.prod_singleton, Finset.prod_singleton]
      push_cast; norm_num
    · by_cases h2 : t = a + 2
      · subst h2
        have hL : ({a} : Finset ℕ).erase (a + 2) = {a} := by ext x; simp
        have hR : ({a, a + 1} : Finset ℕ).erase (a + 2) = {a, a + 1} := by ext x; simp
        rw [hL, hR, if_pos rfl, Finset.prod_singleton, Finset.prod_insert (by simp), Finset.prod_singleton]
        rw [abs_of_pos (by push_cast; linarith), abs_of_pos (by push_cast; linarith)]
        push_cast; norm_num
      · have hlt : t < a := by omega
        have hL : ({a} : Finset ℕ).erase t = {a} := by ext x; simp; omega
        have hR : ({a, a + 1} : Finset ℕ).erase t = {a, a + 1} := by ext x; simp; omega
        rw [hL, hR, if_neg h2, one_mul, Finset.prod_singleton, Finset.prod_insert (by simp), Finset.prod_singleton]
        have hta : (t : ℝ) < (a : ℝ) := by exact_mod_cast hlt
        rw [abs_of_neg (by linarith), abs_of_neg (by push_cast; linarith)]
        push_cast; nlinarith

private lemma rootSetP_even_bound (j t : ℕ) :
    (∏ u ∈ (rootSetP (2 * j)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
        (∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) := by
  induction j with
  | zero => simp [rootSetP]
  | succ j ih =>
    have hIcc : Finset.Icc 1 (4 * (j + 1)) =
        Finset.Icc 1 (4 * j) ∪ {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hdisj_Icc : Disjoint (Finset.Icc 1 (4 * j)) {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2; omega
    have hP : rootSetP (2 * (j + 1)) = rootSetP (2 * j) ∪ {4 * j + 1, 4 * j + 4} := by
      ext x
      simp only [Finset.mem_union, rootSetP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    have hdisj_P : Disjoint (rootSetP (2 * j)) {4 * j + 1, 4 * j + 4} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      omega
    rw [hP, prod_erase_union hdisj_P, hIcc, prod_erase_union hdisj_Icc]
    have hb4 := block4_ineq (4 * j + 1) t
    have hb4' : (∏ u ∈ ({4 * j + 1, 4 * j + 4} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
        (if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1) *
          (∏ u ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
      simpa [show 4 * j + 1 + 1 = 4 * j + 2 from rfl, show 4 * j + 1 + 2 = 4 * j + 3 from rfl,
        show 4 * j + 1 + 3 = 4 * j + 4 from rfl] using hb4
    have hnn1 : 0 ≤ ∏ u ∈ (rootSetP (2 * j)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2 :=
      Finset.prod_nonneg fun _ _ => sq_nonneg _
    have hnn2 : 0 ≤ (if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1) *
        (∏ u ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
      refine mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    have hmul := mul_le_mul ih hb4' (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
          (if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1) =
        if t ∈ Finset.Icc 1 (4 * j) ∪ {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} then (2 : ℝ) else 1 := by
      simp only [Finset.mem_union]
      by_cases hA : t ∈ Finset.Icc 1 (4 * j) <;>
        by_cases hB : t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ)
      · exfalso; exact Finset.disjoint_left.mp hdisj_Icc hA hB
      · simp [hA, hB]
      · simp [hA, hB]
      · simp [hA, hB]
    calc (∏ u ∈ (rootSetP (2 * j)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j + 1, 4 * j + 4} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
            ∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
          ((if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := hmul
      _ = ((if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
            (if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by ring
      _ = _ := by rw [hfac]

lemma rootSetP_bound (l t : ℕ) (ht : t ≤ 2 * l + 1) :
    (∏ u ∈ (rootSetP l).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤ 2 * compProd (2 * l) t := by
  rcases Nat.even_or_odd l with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h := rootSetP_even_bound j t
    have heq : j + j = 2 * j := by omega
    rw [heq]
    have h2 : (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) ≤ 2 := by split_ifs <;> norm_num
    have hnn : 0 ≤ ∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)| :=
      Finset.prod_nonneg fun _ _ => abs_nonneg _
    have hc : 2 * (2 * j) = 4 * j := by omega
    unfold compProd; rw [hc]
    exact h.trans (mul_le_mul_of_nonneg_right h2 hnn)
  · have hIcc : Finset.Icc 1 (2 * (2 * j + 1)) = Finset.Icc 1 (4 * j) ∪ {4 * j + 1, 4 * j + 2} := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hdisj_Icc : Disjoint (Finset.Icc 1 (4 * j)) {4 * j + 1, 4 * j + 2} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2; omega
    have hP : rootSetP (2 * j + 1) = rootSetP (2 * j) ∪ {4 * j + 1} := by
      ext x
      simp only [Finset.mem_union, rootSetP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      omega
    have hdisj_P : Disjoint (rootSetP (2 * j)) {4 * j + 1} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hx1 hx2; omega
    unfold compProd
    rw [hP, prod_erase_union hdisj_P, hIcc, prod_erase_union hdisj_Icc]
    have h1 := rootSetP_even_bound j t
    have h2 := pair2Right_ineq (4 * j + 1) t (by omega)
    have h2' : (∏ u ∈ ({4 * j + 1} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
        (if t = 4 * j + 3 then (2 : ℝ) else 1) *
          (∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
      simpa [show 4 * j + 1 + 1 = 4 * j + 2 from rfl, show 4 * j + 1 + 2 = 4 * j + 3 from rfl] using h2
    have hmul := mul_le_mul h1 h2' (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
          (if t = 4 * j + 3 then (2 : ℝ) else 1) ≤ 2 := by
      by_cases hA : t ∈ Finset.Icc 1 (4 * j) <;> by_cases hB : t = 4 * j + 3
      · exfalso; simp only [Finset.mem_Icc] at hA; omega
      · simp [hA, hB]
      · simp [hB]
      · simp [hA, hB]
    have hnn : 0 ≤ (∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
        ∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)| :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    calc (∏ u ∈ (rootSetP (2 * j)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j + 1} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
            (if t = 4 * j + 3 then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
          nlinarith [hmul]
      _ ≤ 2 * ((∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          mul_le_mul_of_nonneg_right hfac hnn

private lemma rootSetQ_odd_bound (j t : ℕ) :
    (∏ u ∈ (rootSetQ (2 * j + 1)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) *
        (∏ u ∈ (Finset.Icc 1 (4 * j + 2)).erase t, |(t : ℝ) - (u : ℝ)|) := by
  induction j with
  | zero =>
    have hQ : rootSetQ 1 = {2} := by
      ext x; simp [rootSetQ]; omega
    have hIcc : Finset.Icc 1 2 = {1, 2} := by
      ext x; simp; omega
    have hins : insert 0 (Finset.Icc 3 2) = {0} := by
      ext x; simp
    simpa [hQ, hIcc, hins] using pair2Left_ineq t
  | succ j ih =>
    have hIcc : Finset.Icc 1 (4 * (j + 1) + 2) =
        Finset.Icc 1 (4 * j + 2) ∪ {4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hdisj_Icc : Disjoint (Finset.Icc 1 (4 * j + 2)) {4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2; omega
    have hQ : rootSetQ (2 * (j + 1) + 1) = rootSetQ (2 * j + 1) ∪ {4 * j + 3, 4 * j + 6} := by
      ext x
      simp only [Finset.mem_union, rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    have hdisj_Q : Disjoint (rootSetQ (2 * j + 1)) {4 * j + 3, 4 * j + 6} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      omega
    rw [hQ, prod_erase_union hdisj_Q, hIcc, prod_erase_union hdisj_Icc]
    have hb4 := block4_ineq (4 * j + 3) t
    have hb4' : (∏ u ∈ ({4 * j + 3, 4 * j + 6} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
        (if t ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ) then (2 : ℝ) else 1) *
          (∏ u ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
      simpa [show 4 * j + 3 + 1 = 4 * j + 4 from rfl, show 4 * j + 3 + 2 = 4 * j + 5 from rfl,
        show 4 * j + 3 + 3 = 4 * j + 6 from rfl] using hb4
    have hmul := mul_le_mul ih hb4' (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) *
          (if t ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ) then (2 : ℝ) else 1) =
        if t ∈ insert 0 (Finset.Icc 3 (4 * (j + 1) + 2)) then (2 : ℝ) else 1 := by
      have hU : insert 0 (Finset.Icc 3 (4 * (j + 1) + 2)) =
          insert 0 (Finset.Icc 3 (4 * j + 2)) ∪ {4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} := by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
      have hdisjU : Disjoint (insert 0 (Finset.Icc 3 (4 * j + 2))) {4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_singleton] at hx1 hx2; omega
      simp only [hU, Finset.mem_union]
      by_cases hA : t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) <;>
        by_cases hB : t ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ)
      · exfalso; exact Finset.disjoint_left.mp hdisjU hA hB
      · simp [hA, hB]
      · simp [hA, hB]
      · simp [hA, hB]
    calc (∏ u ∈ (rootSetQ (2 * j + 1)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j + 3, 4 * j + 6} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) *
            (if t ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ) then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
          nlinarith [hmul]
      _ = _ := by rw [hfac]

lemma rootSetQ_bound (l t : ℕ) (hl : 1 ≤ l) (ht : t ≤ 2 * l + 1) :
    (∏ u ∈ (rootSetQ l).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤ 2 * compProd (2 * l) t := by
  rcases Nat.even_or_odd l with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hj0 : j ≠ 0 := by omega
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hl_eq : l = 2 * j' + 2 := by omega
    rw [hl_eq] at ht ⊢
    have hIcc : Finset.Icc 1 (2 * (2 * j' + 2)) = Finset.Icc 1 (4 * j' + 2) ∪ {4 * j' + 3, 4 * j' + 4} := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
    have hdisj_Icc : Disjoint (Finset.Icc 1 (4 * j' + 2)) {4 * j' + 3, 4 * j' + 4} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2; omega
    have hQ : rootSetQ (2 * j' + 2) = rootSetQ (2 * j' + 1) ∪ {4 * j' + 3} := by
      ext x
      simp only [Finset.mem_union, rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      omega
    have hdisj_Q : Disjoint (rootSetQ (2 * j' + 1)) {4 * j' + 3} := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton] at hx1 hx2; omega
    unfold compProd
    rw [hQ, prod_erase_union hdisj_Q, hIcc, prod_erase_union hdisj_Icc]
    have h1 := rootSetQ_odd_bound j' t
    have h2 := pair2Right_ineq (4 * j' + 3) t (by omega)
    have h2' : (∏ u ∈ ({4 * j' + 3} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
        (if t = 4 * j' + 5 then (2 : ℝ) else 1) *
          (∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
      simpa [show 4 * j' + 3 + 1 = 4 * j' + 4 from rfl, show 4 * j' + 3 + 2 = 4 * j' + 5 from rfl] using h2
    have hmul := mul_le_mul h1 h2' (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) then (2 : ℝ) else 1) *
          (if t = 4 * j' + 5 then (2 : ℝ) else 1) ≤ 2 := by
      by_cases hA : t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) <;> by_cases hB : t = 4 * j' + 5
      · exfalso; simp only [Finset.mem_insert, Finset.mem_Icc] at hA; omega
      · simp [hA, hB]
      · simp [hB]
      · simp [hA, hB]
    have hnn : 0 ≤ (∏ u ∈ (Finset.Icc 1 (4 * j' + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
        ∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)| :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    calc (∏ u ∈ (rootSetQ (2 * j' + 1)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j' + 3} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) then (2 : ℝ) else 1) *
            (if t = 4 * j' + 5 then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j' + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
          nlinarith [hmul]
      _ ≤ 2 * ((∏ u ∈ (Finset.Icc 1 (4 * j' + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          mul_le_mul_of_nonneg_right hfac hnn
  · subst hj
    have h := rootSetQ_odd_bound j t
    have h2 : (if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) ≤ 2 := by
      split_ifs <;> norm_num
    have hnn : 0 ≤ ∏ u ∈ (Finset.Icc 1 (4 * j + 2)).erase t, |(t : ℝ) - (u : ℝ)| :=
      Finset.prod_nonneg fun _ _ => abs_nonneg _
    have hc : 2 * (2 * j + 1) = 4 * j + 2 := by omega
    unfold compProd; rw [hc]
    exact h.trans (mul_le_mul_of_nonneg_right h2 hnn)

lemma pPolyRaw_eval_zero_sq_bounds (l : ℕ) (hl : 1 ≤ l) :
    ((2 * l).factorial : ℝ) / 2 ≤ ((pPolyRaw l).eval 0) ^ 2 ∧
      ((2 * l).factorial : ℝ) / 2 ≤ ((qPolyRaw l).eval 0) ^ 2 := by
  have hp0 : ((pPolyRaw l).eval 0) ^ 2 ≤ 2 * ((2 * l).factorial : ℝ) := by
    have hP := rootSetP_bound l 0 (by omega)
    have hnot : 0 ∉ rootSetP l := by simp [rootSetP]
    rw [Finset.erase_eq_of_notMem hnot, compProd_zero] at hP
    unfold pPolyRaw
    rw [Polynomial.eval_prod, ← Finset.prod_pow]
    simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hP
  have hq0 : ((qPolyRaw l).eval 0) ^ 2 ≤ 2 * ((2 * l).factorial : ℝ) := by
    have hQ := rootSetQ_bound l 0 hl (by omega)
    have hnot : 0 ∉ rootSetQ l := by simp [rootSetQ]
    rw [Finset.erase_eq_of_notMem hnot, compProd_zero] at hQ
    unfold qPolyRaw
    rw [Polynomial.eval_prod, ← Finset.prod_pow]
    simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hQ
  have hmul : ((pPolyRaw l).eval 0) ^ 2 * ((qPolyRaw l).eval 0) ^ 2 = (((2 * l).factorial : ℝ) ^ 2) := by
    have h := pPolyRaw_mul_qPolyRaw_eval_zero l
    nlinarith [sq ((pPolyRaw l).eval 0 * (qPolyRaw l).eval 0 - ((2 * l).factorial : ℝ))]
  have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
  have hp_pos : 0 < ((pPolyRaw l).eval 0) ^ 2 := sq_pos_of_ne_zero (pPolyRaw_eval_zero_ne l)
  have hq_pos : 0 < ((qPolyRaw l).eval 0) ^ 2 := sq_pos_of_ne_zero (qPolyRaw_eval_zero_ne l)
  constructor
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hq0, hmul, hfac_pos]
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hp0, hmul, hfac_pos]

lemma PPoly_sq_bound (l t : ℕ) (hl : 1 ≤ l) (ht : t ≤ 2 * l + 1) :
    ((PPoly l).eval (t : ℝ)) ^ 2 ≤ 2 * compProd (2 * l) t / ((2 * l).factorial : ℝ) := by
  by_cases hmem : t ∈ rootSetP l
  · rw [PPoly_eval_root hmem, zero_pow (by norm_num)]
    exact div_nonneg (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) (by positivity)
  · have hP := rootSetP_bound l t ht
    rw [Finset.erase_eq_of_notMem hmem] at hP
    have hraw : ((pPolyRaw l).eval (t : ℝ)) ^ 2 ≤ 2 * compProd (2 * l) t := by
      unfold pPolyRaw
      rw [Polynomial.eval_prod, ← Finset.prod_pow]
      simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hP
    have h0 := (pPolyRaw_eval_zero_sq_bounds l hl).1
    have hden : ((2 * l).factorial : ℝ) ≤ 2 * ((pPolyRaw l).eval 0) ^ 2 := by linarith
    have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
    have hsq : ((PPoly l).eval (t : ℝ)) ^ 2 = ((pPolyRaw l).eval (t : ℝ)) ^ 2 / (2 * ((pPolyRaw l).eval 0) ^ 2) := by
      unfold PPoly
      rw [Polynomial.eval_mul, Polynomial.eval_C, mul_pow]
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [pPolyRaw_eval_zero_ne l]
      rw [hs]; ring
    rw [hsq]
    exact div_le_div₀ (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) hraw hfac_pos hden

lemma QPoly_sq_bound (l t : ℕ) (hl : 1 ≤ l) (ht : t ≤ 2 * l + 1) :
    ((QPoly l).eval (t : ℝ)) ^ 2 ≤ 2 * compProd (2 * l) t / ((2 * l).factorial : ℝ) := by
  by_cases hmem : t ∈ rootSetQ l
  · rw [QPoly_eval_root hmem, zero_pow (by norm_num)]
    exact div_nonneg (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) (by positivity)
  · have hQ := rootSetQ_bound l t hl ht
    rw [Finset.erase_eq_of_notMem hmem] at hQ
    have hraw : ((qPolyRaw l).eval (t : ℝ)) ^ 2 ≤ 2 * compProd (2 * l) t := by
      unfold qPolyRaw
      rw [Polynomial.eval_prod, ← Finset.prod_pow]
      simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hQ
    have h0 := (pPolyRaw_eval_zero_sq_bounds l hl).2
    have hden : ((2 * l).factorial : ℝ) ≤ 2 * ((qPolyRaw l).eval 0) ^ 2 := by linarith
    have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
    have hsq : ((QPoly l).eval (t : ℝ)) ^ 2 = ((qPolyRaw l).eval (t : ℝ)) ^ 2 / (2 * ((qPolyRaw l).eval 0) ^ 2) := by
      unfold QPoly
      rw [Polynomial.eval_mul, Polynomial.eval_C, mul_pow]
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [qPolyRaw_eval_zero_ne l]
      rw [hs]; ring
    rw [hsq]
    exact div_le_div₀ (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) hraw hfac_pos hden

lemma DPoly_sq_bound {m l t : ℕ} (hml : m < l) (ht : t ≤ 2 * l + 1) :
    ((DPoly m l).eval (t : ℝ)) ^ 2 ≤
      8 * (compProd (2 * l) t / ((2 * l).factorial : ℝ)) / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by
  have hl : 1 ≤ l := by omega
  have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
  by_cases hts : t = 2 * m + 2
  · subst hts
    have hzero : (1 + |((2 * m + 2 : ℕ) : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 = 1 := by simp
    rw [hzero, div_one]
    by_cases hm : Even m
    · have hQ := rootSetQ_bound l (2 * m + 2) hl ht
      have hsq : ((DPoly m l).eval ((2 * m + 2 : ℕ) : ℝ)) ^ 2 =
          (∏ u ∈ (rootSetQ l).erase (2 * m + 2), (((2 * m + 2 : ℕ) : ℝ) - (u : ℝ)) ^ 2) /
            (2 * ((qPolyRaw l).eval 0) ^ 2) := by
        simp only [DPoly, hm, ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
          Polynomial.eval_sub, Polynomial.eval_X, mul_pow, Finset.prod_pow]
        have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        field_simp [qPolyRaw_eval_zero_ne l]
        rw [hs]; ring
      rw [hsq]
      have hden : ((2 * l).factorial : ℝ) ≤ 2 * ((qPolyRaw l).eval 0) ^ 2 := by
        linarith [(pPolyRaw_eval_zero_sq_bounds l hl).2]
      have hle2 : (∏ u ∈ (rootSetQ l).erase (2 * m + 2), (((2 * m + 2 : ℕ) : ℝ) - (u : ℝ)) ^ 2) /
          (2 * ((qPolyRaw l).eval 0) ^ 2) ≤ 2 * compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ) :=
        div_le_div₀ (mul_nonneg (by norm_num) (compProd_pos (2 * l) (2 * m + 2)).le) hQ hfac_pos hden
      have hle8 : 2 * compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ) ≤
          8 * (compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ)) := by
        have hnn : 0 ≤ compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ) :=
          div_nonneg (compProd_pos (2 * l) (2 * m + 2)).le hfac_pos.le
        calc 2 * compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ)
            = 2 * (compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ)) := by ring
          _ ≤ 8 * (compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ)) := by linarith
      exact hle2.trans hle8
    · have hP := rootSetP_bound l (2 * m + 2) ht
      have hsq : ((DPoly m l).eval ((2 * m + 2 : ℕ) : ℝ)) ^ 2 =
          (∏ u ∈ (rootSetP l).erase (2 * m + 2), (((2 * m + 2 : ℕ) : ℝ) - (u : ℝ)) ^ 2) /
            (2 * ((pPolyRaw l).eval 0) ^ 2) := by
        simp only [DPoly, hm, ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
          Polynomial.eval_sub, Polynomial.eval_X, mul_pow, Finset.prod_pow]
        have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        field_simp [pPolyRaw_eval_zero_ne l]
        rw [hs]; ring
      rw [hsq]
      have hden : ((2 * l).factorial : ℝ) ≤ 2 * ((pPolyRaw l).eval 0) ^ 2 := by
        linarith [(pPolyRaw_eval_zero_sq_bounds l hl).1]
      have hle2 : (∏ u ∈ (rootSetP l).erase (2 * m + 2), (((2 * m + 2 : ℕ) : ℝ) - (u : ℝ)) ^ 2) /
          (2 * ((pPolyRaw l).eval 0) ^ 2) ≤ 2 * compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ) :=
        div_le_div₀ (mul_nonneg (by norm_num) (compProd_pos (2 * l) (2 * m + 2)).le) hP hfac_pos hden
      have hle8 : 2 * compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ) ≤
          8 * (compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ)) := by
        have hnn : 0 ≤ compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ) :=
          div_nonneg (compProd_pos (2 * l) (2 * m + 2)).le hfac_pos.le
        calc 2 * compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ)
            = 2 * (compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ)) := by ring
          _ ≤ 8 * (compProd (2 * l) (2 * m + 2) / ((2 * l).factorial : ℝ)) := by linarith
      exact hle2.trans hle8
  · have heq := congrArg (Polynomial.eval (t : ℝ)) (linear_mul_DPoly hml)
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heq
    have hdiff_ne : (t : ℝ) - ((2 * m + 2 : ℕ) : ℝ) ≠ 0 := by
      intro h; apply hts; exact_mod_cast (sub_eq_zero.mp h)
    have habs_ge1 : (1 : ℝ) ≤ |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)| := by
      have hlt_or_gt : t < 2 * m + 2 ∨ 2 * m + 2 < t := by omega
      rcases hlt_or_gt with hlt | hgt
      · have : (t : ℝ) + 1 ≤ ((2 * m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : t + 1 ≤ 2 * m + 2)
        rw [abs_of_neg (by linarith)]; linarith
      · have : ((2 * m + 2 : ℕ) : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast (by omega : 2 * m + 2 + 1 ≤ t)
        rw [abs_of_pos (by linarith)]; linarith
    have hR_sq : ((if Even m then QPoly l else PPoly l).eval (t : ℝ)) ^ 2 ≤
        2 * compProd (2 * l) t / ((2 * l).factorial : ℝ) := by
      by_cases hm : Even m
      · simp only [hm, ↓reduceIte]; exact QPoly_sq_bound l t hl ht
      · simp only [hm, ↓reduceIte]; exact PPoly_sq_bound l t hl ht
    have hD_sq : ((DPoly m l).eval (t : ℝ)) ^ 2 =
        ((if Even m then QPoly l else PPoly l).eval (t : ℝ)) ^ 2 / ((t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)) ^ 2 := by
      rw [← heq, mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero 2 hdiff_ne)]
    rw [hD_sq]
    have hinv : (1 : ℝ) / ((t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)) ^ 2 ≤
        4 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by
      have h1 : 1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)| ≤ 2 * |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)| := by linarith
      have h2 : (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 ≤ 4 * ((t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)) ^ 2 := by
        calc (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2
            ≤ (2 * |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by nlinarith
          _ = 4 * |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)| ^ 2 := by ring
          _ = 4 * ((t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)) ^ 2 := by rw [sq_abs]
      rw [div_le_div_iff₀ (sq_pos_of_ne_zero hdiff_ne) (by positivity)]
      linarith
    calc ((if Even m then QPoly l else PPoly l).eval (t : ℝ)) ^ 2 / ((t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)) ^ 2
        = ((if Even m then QPoly l else PPoly l).eval (t : ℝ)) ^ 2 * (1 / ((t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)) ^ 2) := by ring
      _ ≤ (2 * compProd (2 * l) t / ((2 * l).factorial : ℝ)) * (4 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) := by
          exact mul_le_mul hR_sq hinv (by positivity) (div_nonneg (mul_nonneg (by norm_num) (compProd_pos (2 * l) t).le) hfac_pos.le)
      _ = 8 * (compProd (2 * l) t / ((2 * l).factorial : ℝ)) / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by ring

lemma PQ_pointwise_bound {l : ℕ} (hl : 1 ≤ l) (t : Fin (2 * l + 1 + 1)) :
    ((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) ≤
      16 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by
  have ht : (t : ℕ) ≤ 2 * l + 1 := Nat.lt_succ_iff.mp t.isLt
  have hsum : ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2 ≤
      4 * (compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := by
    calc ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2
        ≤ 2 * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ) +
          2 * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ) :=
          add_le_add (PPoly_sq_bound l t hl ht) (QPoly_sq_bound l t hl ht)
      _ = 4 * (compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := by ring
  have hmul : ((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) ≤
      4 * (((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := by
    have hnn : 0 ≤ ((2 * l + 1).choose (t : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2)
        ≤ ((2 * l + 1).choose (t : ℕ) : ℝ) * (4 * (compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum hnn
      _ = 4 * (((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := by ring
  have hch := choose_mul_compProd_le hl t
  calc ((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2)
      ≤ 4 * (((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) := hmul
    _ ≤ 4 * (4 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ))) :=
        mul_le_mul_of_nonneg_left hch (by norm_num)
    _ = 16 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by ring

private lemma harmonic_sq_sum_bound (N : ℕ) :
    ∑ k ∈ Finset.range N, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    cases N with
    | zero => simp
    | succ N =>
      have htele : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) =
          1 - 1 / ((n + 1 : ℕ) : ℝ) := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn =>
          rw [Finset.sum_range_succ, ihn]
          push_cast; ring
      have hsub : ∑ k ∈ Finset.range (N + 2), 1 / ((k + 1 : ℕ) : ℝ) ^ 2 ≤
          1 + ∑ k ∈ Finset.range (N + 1), (1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ)) := by
        rw [Finset.sum_range_succ']
        simp only [zero_add]
        have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
        rw [h1, add_comm]
        refine add_le_add_right (Finset.sum_le_sum fun k _ => ?_) 1
        have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        have hk2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
        have hdiff : 1 / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 2 : ℕ) : ℝ) =
            1 / (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by
          field_simp [hk1.ne', hk2.ne']; push_cast; ring
        rw [hdiff]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hle : ((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) ^ 2 := by
          have : (k + 1 : ℝ) ≤ (k + 2 : ℝ) := by linarith
          push_cast; nlinarith
        simpa [Nat.add_assoc] using hle
      rw [htele] at hsub
      have hnn : 0 ≤ 1 / ((N + 2 : ℕ) : ℝ) := by positivity
      linarith

lemma lemma_C_4 (l t : ℕ) :
    ∑ m ∈ Finset.range l,
        (t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) ≤ 72 := by
  have hpoint : ∀ m ∈ Finset.range l,
      (t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) ≤
        4 / ((2 * m + 1 : ℕ) : ℝ) ^ 2 + 16 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by
    intro m _
    by_cases hcase : 4 * m + 4 ≤ t
    · have ht_pos : (0 : ℝ) < (t : ℝ) := by
        exact_mod_cast (by omega : 0 < t)
      have hge : (t : ℝ) ≤ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) := by
        have hle : ((2 * m + 2 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 2 * m + 2 ≤ t)
        have h2 : 2 * ((2 * m + 2 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 2 * (2 * m + 2) ≤ t)
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        linarith
      have hsq : (t : ℝ) ^ 2 ≤ 4 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by
        nlinarith [ht_pos, hge]
      have hden1 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have hden2 : (0 : ℝ) < (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by positivity
      have hle1 : (t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) ≤
          4 / ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ (mul_pos hden1 hden2) hden1]
        nlinarith [hsq, hden1]
      linarith [show (0 : ℝ) ≤ 16 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 from by positivity]
    · have hlt : t < 4 * m + 4 := Nat.lt_of_not_ge hcase
      have hle : (t : ℝ) ≤ 4 * ((2 * m + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : t ≤ 4 * (2 * m + 1))
      have hsq : (t : ℝ) ^ 2 ≤ 16 * ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by
        have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
        nlinarith
      have hden1 : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have hden2 : (0 : ℝ) < (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by positivity
      have hle2 : (t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) ≤
          16 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by
        rw [div_le_div_iff₀ (mul_pos hden1 hden2) hden2]
        nlinarith [hsq, hden2]
      linarith [show (0 : ℝ) ≤ 4 / ((2 * m + 1 : ℕ) : ℝ) ^ 2 from by positivity]
  have hsum1 : ∑ m ∈ Finset.range l, 4 / ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤ 8 := by
    have hle : ∑ m ∈ Finset.range l, 4 / ((2 * m + 1 : ℕ) : ℝ) ^ 2 ≤
        4 * ∑ m ∈ Finset.range l, 1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun m _ => ?_
      rw [mul_one_div]
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      have : ((m + 1 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ 2 * m + 1)
      nlinarith [show (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) from by positivity]
    linarith [harmonic_sq_sum_bound l]
  have hsum2 : ∑ m ∈ Finset.range l, 16 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 ≤ 64 := by
    let S₁ := (Finset.range l).filter fun m => 2 * m + 2 ≤ t
    let S₂ := (Finset.range l).filter fun m => t < 2 * m + 2
    have hpart : ∑ m ∈ Finset.range l, 1 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 =
        (∑ m ∈ S₁, 1 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) +
        (∑ m ∈ S₂, 1 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) := by
      have hS2_eq : S₂ = (Finset.range l).filter fun m => ¬(2 * m + 2 ≤ t) := by
        ext m; simp only [S₂, Finset.mem_filter, Finset.mem_range]; omega
      rw [hS2_eq]
      exact (Finset.sum_filter_add_sum_filter_not (Finset.range l) (fun m => 2 * m + 2 ≤ t) _).symm
    have hS1 : ∑ m ∈ S₁, 1 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 ≤ 2 := by
      have hrew : ∑ m ∈ S₁, 1 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 =
          ∑ m ∈ S₁, 1 / (((t - (2 * m + 2) + 1 : ℕ) : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm' : 2 * m + 2 ≤ t := (Finset.mem_filter.mp hm).2
        have hle : ((2 * m + 2 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hm'
        rw [abs_of_nonneg (sub_nonneg.mpr hle)]
        push_cast [Nat.cast_sub hm']
        ring_nf
      rw [hrew]
      have hinj : Set.InjOn (fun m => t - (2 * m + 2)) (S₁ : Set ℕ) := by
        intro m₁ hm₁ m₂ hm₂ h
        have h1 := (Finset.mem_filter.mp hm₁).2
        have h2 := (Finset.mem_filter.mp hm₂).2
        dsimp at h; omega
      have hsub : S₁.image (fun m => t - (2 * m + 2)) ⊆ Finset.range (t + 1) := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
        have hm' := (Finset.mem_filter.mp hm).2
        rw [Finset.mem_range]; omega
      have hle_sum : (∑ m ∈ S₁, 1 / (((t - (2 * m + 2) + 1 : ℕ) : ℝ) ^ 2)) ≤
          ∑ k ∈ Finset.range (t + 1), 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
        rw [← Finset.sum_image (f := fun k => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) hinj]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      exact hle_sum.trans (harmonic_sq_sum_bound (t + 1))
    have hS2 : ∑ m ∈ S₂, 1 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 ≤ 2 := by
      have hrew : ∑ m ∈ S₂, 1 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 =
          ∑ m ∈ S₂, 1 / ((((2 * m + 2) - t + 1 : ℕ) : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm' : t < 2 * m + 2 := (Finset.mem_filter.mp hm).2
        have hlt : (t : ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by exact_mod_cast hm'
        rw [abs_of_neg (sub_neg.mpr hlt), neg_sub]
        push_cast [Nat.cast_sub hm'.le]
        ring_nf
      rw [hrew]
      have hinj : Set.InjOn (fun m => (2 * m + 2) - t) (S₂ : Set ℕ) := by
        intro m₁ hm₁ m₂ hm₂ h
        have h1 := (Finset.mem_filter.mp hm₁).2
        have h2 := (Finset.mem_filter.mp hm₂).2
        dsimp at h; omega
      have hsub : S₂.image (fun m => (2 * m + 2) - t) ⊆ Finset.range (2 * l + 3) := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
        have hm1 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
        have hm2 := (Finset.mem_filter.mp hm).2
        rw [Finset.mem_range]; omega
      have hle_sum : (∑ m ∈ S₂, 1 / ((((2 * m + 2) - t + 1 : ℕ) : ℝ) ^ 2)) ≤
          ∑ k ∈ Finset.range (2 * l + 3), 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
        rw [← Finset.sum_image (f := fun k => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) hinj]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      exact hle_sum.trans (harmonic_sq_sum_bound (2 * l + 3))
    have hmul16 : ∑ m ∈ Finset.range l, 16 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 =
        16 * ∑ m ∈ Finset.range l, 1 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by ring
    rw [hmul16, hpart]
    linarith
  calc ∑ m ∈ Finset.range l,
        (t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2)
      ≤ ∑ m ∈ Finset.range l,
          (4 / ((2 * m + 1 : ℕ) : ℝ) ^ 2 + 16 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) :=
        Finset.sum_le_sum hpoint
    _ = (∑ m ∈ Finset.range l, 4 / ((2 * m + 1 : ℕ) : ℝ) ^ 2) +
        (∑ m ∈ Finset.range l, 16 / (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) := Finset.sum_add_distrib
    _ ≤ 72 := by linarith

lemma CPoly_sum_pointwise_bound {l : ℕ} (hl : 1 ≤ l) (t : Fin (2 * l + 1 + 1)) :
    ((2 * l + 1).choose (t : ℕ) : ℝ) *
        ∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2 ≤
      2304 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by
  have ht : (t : ℕ) ≤ 2 * l + 1 := Nat.lt_succ_iff.mp t.isLt
  have hterm : ∀ m ∈ Finset.range l,
      ((2 * l + 1).choose (t : ℕ) : ℝ) * ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2 ≤
        (32 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ))) *
          ((t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2)) := by
    intro m hm
    have hml : m < l := Finset.mem_range.mp hm
    have hD := DPoly_sq_bound hml ht
    have hC_sq : ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2 =
        ((DPoly m l).eval (t : ℝ)) ^ 2 * ((t : ℝ) ^ 2 / ((2 * m + 1 : ℕ) : ℝ) ^ 2) := by
      simp only [CPoly, Polynomial.eval_mul, Polynomial.eval_X]
      ring
    have hch := choose_mul_compProd_le hl t
    have hch_pos : 0 ≤ ((2 * l + 1).choose (t : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht_nn : 0 ≤ (t : ℝ) ^ 2 / ((2 * m + 1 : ℕ) : ℝ) ^ 2 := by positivity
    calc ((2 * l + 1).choose (t : ℕ) : ℝ) * ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2
        = ((2 * l + 1).choose (t : ℕ) : ℝ) * ((DPoly m l).eval (t : ℝ)) ^ 2 *
            ((t : ℝ) ^ 2 / ((2 * m + 1 : ℕ) : ℝ) ^ 2) := by rw [hC_sq]; ring
      _ ≤ ((2 * l + 1).choose (t : ℕ) : ℝ) *
            (8 * (compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ)) /
              (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) *
            ((t : ℝ) ^ 2 / ((2 * m + 1 : ℕ) : ℝ) ^ 2) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD hch_pos) ht_nn
      _ = (8 * (((2 * l + 1).choose (t : ℕ) : ℝ) * compProd (2 * l) (t : ℕ) / ((2 * l).factorial : ℝ))) *
            ((t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2)) := by
          have hfac_ne : ((2 * l).factorial : ℝ) ≠ 0 := by positivity
          have hm_ne : ((2 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have ha_ne : 1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)| ≠ 0 := by positivity
          field_simp [hfac_ne, hm_ne, ha_ne]
      _ ≤ (8 * (4 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)))) *
            ((t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hch (by norm_num)) (by positivity)
      _ = _ := by ring
  rw [Finset.mul_sum]
  calc ∑ m ∈ Finset.range l,
        ((2 * l + 1).choose (t : ℕ) : ℝ) * ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2
      ≤ ∑ m ∈ Finset.range l,
          (32 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ))) *
            ((t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = (32 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ))) *
          ∑ m ∈ Finset.range l,
            (t : ℝ) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) ^ 2 * (1 + |(t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)|) ^ 2) := by
        rw [← Finset.mul_sum]
    _ ≤ (32 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ))) * 72 :=
        mul_le_mul_of_nonneg_left (lemma_C_4 l t) (by positivity)
    _ = 2304 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by ring

lemma WVec_energy_bound :
    ∃ C_core : ℝ, 0 < C_core ∧ ∀ n' M l : ℕ, 1 ≤ M → l ≤ M → 2 * l + 1 ≤ n' →
      ∀ A : ExactSupports n' (2 * l + 1),
        (2 : ℝ) ^ (-(n' : ℤ)) * ∑ S : Qubits n', ∑ c : Fin (M + 1),
          (WVec M l (intersectionIndex A S) c) ^ 2 ≤ C_core * Real.log (2 * M + 1) := by
  obtain ⟨H, hH_pos, hH⟩ := pointwise_correction_bound_to_log_energy
  refine ⟨max (4 / Real.log 3) (2336 * H), ?_, ?_⟩
  · have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    exact lt_max_of_lt_left (div_pos (by norm_num) hlog3)
  · intro n' M l hM hlM hle A
    have hdisj : ∀ a : Fin (2 * l + 1 + 1), ∀ c : Fin (M + 1),
        (WVec M l a c) ^ 2 = (LVec M l a c) ^ 2 + (UVec M l a c) ^ 2 := by
      intro a c
      by_cases ha : l < (a : ℕ)
      · rw [WVec, LVec_eq_zero_of_gt ha c]; ring
      · rw [WVec, UVec_eq_zero_of_le (Nat.le_of_not_gt ha) c]; ring
    have hexact :
        (2 : ℝ) ^ (-(n' : ℤ)) * ∑ S : Qubits n', ∑ c : Fin (M + 1),
          (WVec M l (intersectionIndex A S) c) ^ 2 =
        ∑ t : Fin (2 * l + 1 + 1), ((2 * l + 1).choose (t : ℕ) : ℝ) *
          ∑ c : Fin (M + 1), (((pVecPoly M l c).eval (t : ℝ)) ^ 2 + ((qVecPoly M l c).eval (t : ℝ)) ^ 2) := by
      rw [Finset.sum_comm]
      have hswap : (2 : ℝ) ^ (-(n' : ℤ)) * ∑ c : Fin (M + 1), ∑ S : Qubits n',
            (WVec M l (intersectionIndex A S) c) ^ 2 =
          ∑ c : Fin (M + 1), (2 : ℝ) ^ (-(n' : ℤ)) * ∑ S : Qubits n',
            (WVec M l (intersectionIndex A S) c) ^ 2 := Finset.mul_sum _ _ _
      rw [hswap]
      have hc : ∀ c : Fin (M + 1),
          (2 : ℝ) ^ (-(n' : ℤ)) * ∑ S : Qubits n', (WVec M l (intersectionIndex A S) c) ^ 2 =
          ∑ t : Fin (2 * l + 1 + 1), ((2 * l + 1).choose (t : ℕ) : ℝ) *
            (((pVecPoly M l c).eval (t : ℝ)) ^ 2 + ((qVecPoly M l c).eval (t : ℝ)) ^ 2) := by
        intro c
        rw [normalized_intersection_sum n' (2 * l + 1) hle A (fun a => (WVec M l a c) ^ 2)]
        have hrew : (∑ a : Fin (2 * l + 1 + 1), ((2 * l + 1).choose (a : ℕ) : ℝ) * (WVec M l a c) ^ 2) =
            ∑ a : Fin (2 * l + 1 + 1), ((2 * l + 1).choose (a : ℕ) : ℝ) *
              ((LVec M l a c) ^ 2 + (UVec M l a c) ^ 2) := by
          refine Finset.sum_congr rfl fun a _ => by rw [hdisj a c]
        rw [hrew]
        exact lemma_4_2_two_channel (2 * l + 1)
          (fun t => (pVecPoly M l c).eval (t : ℝ))
          (fun t => (qVecPoly M l c).eval (t : ℝ))
      rw [Finset.sum_congr rfl fun c _ => hc c, Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.mul_sum]
    rw [hexact]
    have hcoord_le : ∀ t : Fin (2 * l + 1 + 1),
        ∑ c : Fin (M + 1), (((pVecPoly M l c).eval (t : ℝ)) ^ 2 + ((qVecPoly M l c).eval (t : ℝ)) ^ 2) ≤
          2 * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) +
            ∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2 := by
      intro t
      rw [Fin.sum_univ_succ]
      have h0 : ((pVecPoly M l 0).eval (t : ℝ)) ^ 2 + ((qVecPoly M l 0).eval (t : ℝ)) ^ 2 =
          ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2 := by
        simp [pVecPoly, qVecPoly]
      rw [h0]
      have hrest : ∑ j : Fin M,
          (((pVecPoly M l j.succ).eval (t : ℝ)) ^ 2 + ((qVecPoly M l j.succ).eval (t : ℝ)) ^ 2) ≤
          (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) +
            ∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2 := by
        have hpt : ∀ j : Fin M,
            ((pVecPoly M l j.succ).eval (t : ℝ)) ^ 2 + ((qVecPoly M l j.succ).eval (t : ℝ)) ^ 2 ≤
              (if (j : ℕ) < l then ((CPoly j l).eval (t : ℝ) / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 else 0) +
              (if (j : ℕ) = l then ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2 else 0) := by
          intro j
          simp only [pVecPoly, qVecPoly, Fin.cases_succ]
          by_cases hj1 : (j : ℕ) < l
          · have hne : (j : ℕ) ≠ l := Nat.ne_of_lt hj1
            by_cases hev : Even (j : ℕ)
            · simp [hj1, hne, hev, div_eq_mul_inv, mul_pow]; exact le_of_eq (by ring)
            · simp [hj1, hne, hev, div_eq_mul_inv, mul_pow]; exact le_of_eq (by ring)
          · by_cases hj2 : (j : ℕ) = l
            · by_cases hl_ev : Even l
              · simp [hj2, hl_ev]; exact sq_nonneg _
              · simp [hj2, hl_ev]; exact sq_nonneg _
            · simp [hj1, hj2]
        calc ∑ j : Fin M, (((pVecPoly M l j.succ).eval (t : ℝ)) ^ 2 + ((qVecPoly M l j.succ).eval (t : ℝ)) ^ 2)
            ≤ ∑ j : Fin M,
                ((if (j : ℕ) < l then ((CPoly j l).eval (t : ℝ) / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 else 0) +
                 (if (j : ℕ) = l then ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2 else 0)) :=
              Finset.sum_le_sum fun j _ => hpt j
          _ = (∑ j : Fin M, if (j : ℕ) < l then ((CPoly j l).eval (t : ℝ) / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 else 0) +
              (∑ j : Fin M, if (j : ℕ) = l then ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2 else 0) :=
              Finset.sum_add_distrib
          _ ≤ (∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2) +
              (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) := by
              refine add_le_add ?_ ?_
              · let Slt : Finset (Fin M) := (Finset.univ : Finset (Fin M)).filter fun j => (j : ℕ) < l
                have hfilt : (∑ j : Fin M, if (j : ℕ) < l then ((CPoly j l).eval (t : ℝ) / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 else 0) =
                    ∑ j ∈ Slt, ((CPoly (j : ℕ) l).eval (t : ℝ) / ((2 * (j : ℕ) + 1 : ℕ) : ℝ)) ^ 2 := by
                  rw [Finset.sum_filter]
                have hinj : Set.InjOn Fin.val (Slt : Set (Fin M)) := fun _ _ _ _ h => Fin.ext h
                have hsub : Slt.image Fin.val ⊆ Finset.range l := by
                  intro m hm
                  rcases Finset.mem_image.mp hm with ⟨j, hj, rfl⟩
                  exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
                rw [hfilt, ← Finset.sum_image (f := fun m => ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2) hinj]
                exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
              · by_cases hlM_lt : l < M
                · rw [Finset.sum_eq_single ⟨l, hlM_lt⟩]
                  · simp
                  · intro j _ hne
                    have : (j : ℕ) ≠ l := fun h => hne (Fin.ext h)
                    simp [this]
                  · intro hnot; exact False.elim (hnot (Finset.mem_univ _))
                · have h0sum : (∑ j : Fin M, if (j : ℕ) = l then
                      ((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2 else 0) = 0 := by
                    refine Finset.sum_eq_zero fun j _ => ?_
                    have : (j : ℕ) ≠ l := by have := j.isLt; omega
                    simp [this]
                  rw [h0sum]
                  positivity
          _ = (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) +
              ∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2 := add_comm _ _
      linarith
    have hstep : ∑ t : Fin (2 * l + 1 + 1), ((2 * l + 1).choose (t : ℕ) : ℝ) *
          ∑ c : Fin (M + 1), (((pVecPoly M l c).eval (t : ℝ)) ^ 2 + ((qVecPoly M l c).eval (t : ℝ)) ^ 2) ≤
        ∑ t : Fin (2 * l + 1 + 1), ((2 * l + 1).choose (t : ℕ) : ℝ) *
          (2 * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) +
            ∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2) := by
      refine Finset.sum_le_sum fun t _ => ?_
      exact mul_le_mul_of_nonneg_left (hcoord_le t) (Nat.cast_nonneg _)
    have hlogM_pos : 0 < Real.log ((2 * M + 1 : ℕ) : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < 2 * M + 1)
    by_cases hl0 : l = 0
    · subst hl0
      have hP0 : PPoly 0 = Polynomial.C (1 / Real.sqrt 2) := by
        unfold PPoly pPolyRaw
        simp [rootSetP]
      have hQ0 : QPoly 0 = Polynomial.C (1 / Real.sqrt 2) := by
        unfold QPoly qPolyRaw
        simp [rootSetQ]
      have hval4 : (∑ t : Fin (2 * 0 + 1 + 1), ((2 * 0 + 1).choose (t : ℕ) : ℝ) *
          (2 * (((PPoly 0).eval (t : ℝ)) ^ 2 + ((QPoly 0).eval (t : ℝ)) ^ 2) +
            ∑ m ∈ Finset.range 0, ((CPoly m 0).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2)) = 4 := by
        simp only [mul_zero, zero_add, Finset.range_zero, Finset.sum_empty, add_zero, hP0, hQ0,
          Polynomial.eval_C]
        rw [Fin.sum_univ_two]
        simp
        norm_num
      have hlog3_le : Real.log 3 ≤ Real.log ((2 * M + 1 : ℕ) : ℝ) := by
        refine Real.log_le_log (by norm_num) ?_
        exact_mod_cast (by omega : 3 ≤ 2 * M + 1)
      have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have h4 : (4 : ℝ) ≤ (4 / Real.log 3) * Real.log ((2 * M + 1 : ℕ) : ℝ) := by
        calc (4 : ℝ) = (4 / Real.log 3) * Real.log 3 := by field_simp [hlog3_pos.ne']
          _ ≤ (4 / Real.log 3) * Real.log ((2 * M + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hlog3_le (by positivity)
      have hmax : (4 / Real.log 3) * Real.log ((2 * M + 1 : ℕ) : ℝ) ≤
          max (4 / Real.log 3) (2336 * H) * Real.log (2 * M + 1 : ℝ) := by
        have hle := mul_le_mul_of_nonneg_right (le_max_left (4 / Real.log 3) (2336 * H)) hlogM_pos.le
        simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hle
      exact hstep.trans (le_of_eq hval4 |>.trans (h4.trans hmax))
    · have hl1 : 1 ≤ l := Nat.pos_of_ne_zero hl0
      have hr3 : 3 ≤ 2 * l + 1 := by omega
      have hpt : ∀ t : Fin (2 * l + 1 + 1),
          ((2 * l + 1).choose (t : ℕ) : ℝ) *
            (2 * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) +
              ∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2) ≤
            2336 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by
        intro t
        have h1 := PQ_pointwise_bound hl1 t
        have h2 := CPoly_sum_pointwise_bound hl1 t
        calc ((2 * l + 1).choose (t : ℕ) : ℝ) *
              (2 * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2) +
                ∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2)
            = 2 * (((2 * l + 1).choose (t : ℕ) : ℝ) * (((PPoly l).eval (t : ℝ)) ^ 2 + ((QPoly l).eval (t : ℝ)) ^ 2)) +
              ((2 * l + 1).choose (t : ℕ) : ℝ) *
                ∑ m ∈ Finset.range l, ((CPoly m l).eval (t : ℝ) / ((2 * m + 1 : ℕ) : ℝ)) ^ 2 := by ring
          _ ≤ 2 * (16 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ))) +
              2304 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
          _ = 2336 * ((2 * l + 1 : ℕ) : ℝ) / (((t : ℕ) + 1 : ℕ) * ((2 * l + 1) - (t : ℕ) + 1 : ℕ)) := by ring
      have hlog_bnd := hH (2 * l + 1) hr3 2336 (by norm_num) _ hpt
      have hlog_le : Real.log ((2 * l + 1 : ℕ) : ℝ) ≤ Real.log ((2 * M + 1 : ℕ) : ℝ) := by
        refine Real.log_le_log (by positivity) ?_
        exact_mod_cast (by omega : 2 * l + 1 ≤ 2 * M + 1)
      have hfinal : 2336 * H * Real.log ((2 * l + 1 : ℕ) : ℝ) ≤
          max (4 / Real.log 3) (2336 * H) * Real.log (2 * (M : ℝ) + 1) := by
        calc 2336 * H * Real.log ((2 * l + 1 : ℕ) : ℝ)
            ≤ 2336 * H * Real.log ((2 * M + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hlog_le (by positivity)
          _ ≤ max (4 / Real.log 3) (2336 * H) * Real.log ((2 * M + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hlogM_pos.le
          _ = max (4 / Real.log 3) (2336 * H) * Real.log (2 * (M : ℝ) + 1) := by
              push_cast; ring
      exact hstep.trans (hlog_bnd.trans hfinal)

/-! ### Step 5: Odd-cardinality (n+1)-variable lift and Gram PSD -/

lemma gram_posSemidef {ι : Type*} [Fintype ι] {d : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (v₁ v₂ : ι → Fin d → ℝ) :
    Matrix.PosSemidef (Matrix.of fun A B : ι => c * (∑ j : Fin d, v₁ A j * v₁ B j + ∑ j : Fin d, v₂ A j * v₂ B j)) := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext A B
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    refine congrArg (c * ·) (congrArg₂ (· + ·) ?_ ?_) <;>
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro x
    have hquad : ∀ v : ι → Fin d → ℝ,
        ∑ j : Fin d, (∑ A : ι, x A * v A j) ^ 2 =
          ∑ A : ι, ∑ B : ι, ∑ j : Fin d, x A * (v A j * v B j) * x B := by
      intro v
      have hexp : ∀ j : Fin d, (∑ A : ι, x A * v A j) ^ 2 =
          ∑ A : ι, ∑ B : ι, x A * (v A j * v B j) * x B := by
        intro j
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun B _ => by ring
      simp_rw [hexp]
      calc (∑ j : Fin d, ∑ A : ι, ∑ B : ι, x A * (v A j * v B j) * x B)
          = ∑ A : ι, ∑ j : Fin d, ∑ B : ι, x A * (v A j * v B j) * x B := Finset.sum_comm
        _ = ∑ A : ι, ∑ B : ι, ∑ j : Fin d, x A * (v A j * v B j) * x B :=
            Finset.sum_congr rfl fun A _ => Finset.sum_comm
    have hrew : star x ⬝ᵥ
          (Matrix.of fun A B : ι => c * (∑ j : Fin d, v₁ A j * v₁ B j + ∑ j : Fin d, v₂ A j * v₂ B j)).mulVec x =
        c * (∑ j : Fin d, (∑ A : ι, x A * v₁ A j) ^ 2 + ∑ j : Fin d, (∑ A : ι, x A * v₂ A j) ^ 2) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
      calc (∑ A : ι, x A * ∑ B : ι, c * (∑ j : Fin d, v₁ A j * v₁ B j + ∑ j : Fin d, v₂ A j * v₂ B j) * x B)
          = ∑ A : ι, c * ∑ B : ι, ∑ j : Fin d,
              (x A * (v₁ A j * v₁ B j) * x B + x A * (v₂ A j * v₂ B j) * x B) := by
            refine Finset.sum_congr rfl fun A _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun B _ => ?_
            rw [← Finset.sum_add_distrib]
            have hmul : ∀ S : ℝ, x A * (c * S * x B) = c * (S * (x A * x B)) := fun S => by ring
            rw [hmul, Finset.sum_mul]
            congr 1
            refine Finset.sum_congr rfl fun j _ => by ring
        _ = c * ∑ A : ι, ∑ B : ι, ∑ j : Fin d,
              (x A * (v₁ A j * v₁ B j) * x B + x A * (v₂ A j * v₂ B j) * x B) := by
            rw [← Finset.mul_sum]
        _ = c * (∑ j : Fin d, (∑ A : ι, x A * v₁ A j) ^ 2 + ∑ j : Fin d, (∑ A : ι, x A * v₂ A j) ^ 2) := by
            congr 1
            rw [hquad v₁, hquad v₂]
            simp only [Finset.sum_add_distrib]
    rw [hrew]
    exact mul_nonneg hc (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

def liftOdd {n k : ℕ} (A : BoundedSupports n k) : Finset (Fin (n + 1)) :=
  if Odd A.1.card then A.1.map Fin.castSuccEmb
  else insert (Fin.last n) (A.1.map Fin.castSuccEmb)

lemma last_not_mem_map_castSucc {n : ℕ} (A : Finset (Fin n)) :
    Fin.last n ∉ A.map Fin.castSuccEmb := by
  intro h
  rcases Finset.mem_map.mp h with ⟨i, _, hi⟩
  simp only [Fin.castSuccEmb_apply] at hi
  have hlt : (i.castSucc : ℕ) < (Fin.last n : ℕ) := Fin.castSucc_lt_last i
  rw [hi] at hlt
  exact (lt_irrefl _ hlt).elim

lemma liftOdd_mem_castSucc {n k : ℕ} (A : BoundedSupports n k) (i : Fin n) :
    i.castSucc ∈ liftOdd A ↔ i ∈ A.1 := by
  unfold liftOdd
  split_ifs
  · simp only [Finset.mem_map, Fin.castSuccEmb_apply]
    constructor
    · rintro ⟨j, hj, hji⟩
      have : j = i := Fin.castSucc_injective n hji
      subst this; exact hj
    · intro hi; exact ⟨i, hi, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_map, Fin.castSuccEmb_apply]
    constructor
    · rintro (hlast | ⟨j, hj, hji⟩)
      · exfalso
        have hlt : (i.castSucc : ℕ) < (Fin.last n : ℕ) := Fin.castSucc_lt_last i
        rw [hlast] at hlt
        exact lt_irrefl _ hlt
      · have : j = i := Fin.castSucc_injective n hji
        subst this; exact hj
    · intro hi; exact Or.inr ⟨i, hi, rfl⟩

lemma liftOdd_injective {n k : ℕ} : Function.Injective (@liftOdd n k) := by
  intro A B h
  apply Subtype.ext
  ext i
  have := congrArg (fun S => i.castSucc ∈ S) h
  simpa [liftOdd_mem_castSucc] using this

lemma liftOdd_card {n k : ℕ} (A : BoundedSupports n k) :
    Odd (liftOdd A).card ∧ (liftOdd A).card ≤ 2 * (k / 2) + 1 := by
  unfold liftOdd
  have hcardA := A.2.2
  split_ifs with hodd
  · rw [Finset.card_map]
    refine ⟨hodd, ?_⟩
    rcases hodd with ⟨m, hm⟩
    rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
    · have : k / 2 = q := by omega
      omega
    · have : k / 2 = q := by omega
      omega
  · rw [Finset.card_insert_of_notMem (last_not_mem_map_castSucc A.1), Finset.card_map]
    rw [Nat.not_odd_iff_even] at hodd
    rcases hodd with ⟨m, hm⟩
    refine ⟨⟨m, by omega⟩, ?_⟩
    rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
    · have : k / 2 = q := by omega
      omega
    · have : k / 2 = q := by omega
      omega

def layerOf {n k : ℕ} (A : BoundedSupports n k) : ℕ :=
  ((liftOdd A).card - 1) / 2

lemma liftOdd_card_eq {n k : ℕ} (A : BoundedSupports n k) :
    (liftOdd A).card = 2 * layerOf A + 1 ∧ layerOf A ≤ k / 2 := by
  have ⟨⟨m, hm⟩, hle⟩ := liftOdd_card A
  have hl : layerOf A = m := by unfold layerOf; rw [hm]; omega
  rw [hl, hm]
  exact ⟨rfl, by omega⟩

lemma liftOdd_majorityBit_snoc_true {n k : ℕ} (A : BoundedSupports n k) (x : Qubits n) :
    majorityBit (liftOdd A) (Fin.snoc x true) = majorityBit A.1 x := by
  have hmap_filt : ((A.1.map Fin.castSuccEmb).filter fun j => (Fin.snoc x true : Qubits (n + 1)) j = true).card =
      (A.1.filter fun i => x i = true).card := by
    have hset : (A.1.map Fin.castSuccEmb).filter (fun j => (Fin.snoc x true : Qubits (n + 1)) j = true) =
        (A.1.filter fun i => x i = true).map Fin.castSuccEmb := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_map, Fin.castSuccEmb_apply]
      constructor
      · rintro ⟨⟨i, hi, rfl⟩, hx⟩
        exact ⟨i, ⟨hi, by simpa [Fin.snoc_castSucc] using hx⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hx⟩, rfl⟩
        exact ⟨⟨i, hi, rfl⟩, by simpa [Fin.snoc_castSucc] using hx⟩
    rw [hset, Finset.card_map]
  unfold liftOdd majorityBit
  simp only [decide_eq_decide]
  split_ifs with hodd
  · rw [Finset.card_map, hmap_filt]
  · have hnot : Fin.last n ∉ A.1.map Fin.castSuccEmb := last_not_mem_map_castSucc A.1
    rw [Finset.card_insert_of_notMem hnot, Finset.card_map]
    have hfilt : (insert (Fin.last n) (A.1.map Fin.castSuccEmb)).filter
          (fun j => (Fin.snoc x true : Qubits (n + 1)) j = true) =
        insert (Fin.last n) ((A.1.map Fin.castSuccEmb).filter fun j => (Fin.snoc x true : Qubits (n + 1)) j = true) := by
      rw [Finset.filter_insert, if_pos (by simp [Fin.snoc_last])]
    have hnotf : Fin.last n ∉ (A.1.map Fin.castSuccEmb).filter
          (fun j => (Fin.snoc x true : Qubits (n + 1)) j = true) :=
      fun h => hnot (Finset.mem_filter.mp h).1
    rw [hfilt, Finset.card_insert_of_notMem hnotf, hmap_filt]
    rw [Nat.not_odd_iff_even] at hodd
    rcases hodd with ⟨m, hm⟩
    rw [hm]
    omega

lemma liftOdd_majorityBit_snoc_false {n k : ℕ} (A : BoundedSupports n k) (x : Qubits n) :
    majorityBit (liftOdd A) (Fin.snoc (fun i => !(x i)) false) = !(majorityBit A.1 x) := by
  have hmap_filt : ((A.1.map Fin.castSuccEmb).filter
        fun j => (Fin.snoc (fun i => !(x i)) false : Qubits (n + 1)) j = true).card =
      A.1.card - (A.1.filter fun i => x i = true).card := by
    have hset : (A.1.map Fin.castSuccEmb).filter
          (fun j => (Fin.snoc (fun i => !(x i)) false : Qubits (n + 1)) j = true) =
        (A.1.filter fun i => !(x i) = true).map Fin.castSuccEmb := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_map, Fin.castSuccEmb_apply]
      constructor
      · rintro ⟨⟨i, hi, rfl⟩, hx⟩
        exact ⟨i, ⟨hi, by simpa [Fin.snoc_castSucc] using hx⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hx⟩, rfl⟩
        exact ⟨⟨i, hi, rfl⟩, by simpa [Fin.snoc_castSucc] using hx⟩
    rw [hset, Finset.card_map]
    have hsum := Finset.card_filter_add_card_filter_not (s := A.1) (p := fun i => x i = true)
    have h1 : (A.1.filter fun i => !(x i) = true) = A.1.filter fun i => ¬(x i = true) := by
      ext i; simp
    rw [h1]; omega
  unfold liftOdd majorityBit
  have hle_A : (A.1.filter fun i => x i = true).card ≤ A.1.card := Finset.card_filter_le _ _
  split_ifs with hodd
  · rw [Finset.card_map, hmap_filt]
    rcases hodd with ⟨m, hm⟩
    rw [hm] at hle_A ⊢
    by_cases hlt : 2 * (A.1.filter fun i => x i = true).card < 2 * m + 1 <;> simp [hlt] <;> omega
  · have hnot : Fin.last n ∉ A.1.map Fin.castSuccEmb := last_not_mem_map_castSucc A.1
    rw [Finset.card_insert_of_notMem hnot, Finset.card_map]
    have hfilt : (insert (Fin.last n) (A.1.map Fin.castSuccEmb)).filter
          (fun j => (Fin.snoc (fun i => !(x i)) false : Qubits (n + 1)) j = true) =
        (A.1.map Fin.castSuccEmb).filter
          (fun j => (Fin.snoc (fun i => !(x i)) false : Qubits (n + 1)) j = true) := by
      rw [Finset.filter_insert, if_neg (by simp [Fin.snoc_last])]
    rw [hfilt, hmap_filt]
    rw [Nat.not_odd_iff_even] at hodd
    rcases hodd with ⟨m, hm⟩
    rw [hm] at hle_A ⊢
    by_cases hlt : 2 * (A.1.filter fun i => x i = true).card < m + m <;> simp [hlt] <;> omega

def snocSplitEquiv (n : ℕ) : Qubits n ⊕ Qubits n ≃ Qubits (n + 1) where
  toFun := Sum.elim (fun x => Fin.snoc x true) (fun x => Fin.snoc (fun i => !(x i)) false)
  invFun S' :=
    if S' (Fin.last n) then Sum.inl (fun i => S' i.castSucc)
    else Sum.inr (fun i => !(S' i.castSucc))
  left_inv x := by
    rcases x with x | x
    · simp only [Sum.elim_inl, Fin.snoc_last, ↓reduceIte, Fin.snoc_castSucc]
    · simp only [Sum.elim_inr, Fin.snoc_last, Bool.false_eq_true, ↓reduceIte, Fin.snoc_castSucc, Bool.not_not]
  right_inv S' := by
    by_cases h : S' (Fin.last n) = true
    · simp only [h, ↓reduceIte, Sum.elim_inl]
      ext j
      refine Fin.lastCases ?_ ?_ j
      · simp [Fin.snoc_last, h]
      · intro i; simp [Fin.snoc_castSucc]
    · have hf : S' (Fin.last n) = false := Bool.eq_false_iff.mpr h
      dsimp
      rw [if_neg h]
      dsimp
      ext j
      refine Fin.lastCases ?_ ?_ j
      · simp [Fin.snoc_last, hf]
      · intro i; simp [Fin.snoc_castSucc]

end Aux_w_maj_sdp

open QuantumLTF.Majority QAlgorithms

theorem solution : ∃ C : ℝ, 0<C ∧ ∀ n k : ℕ, 2≤k → k≤n → ∃ X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ, DualFeasible (fun A : BoundedSupports n k => A.1) X ∧ DualCostAtMost X (C*Real.log k) := by
  obtain ⟨C_core, hC_pos, hC_bound⟩ := Aux_w_maj_sdp.WVec_energy_bound
  refine ⟨2 * C_core, by positivity, ?_⟩
  intro n k hk2 hkn
  let M := k / 2
  have hM1 : 1 ≤ M := by dsimp [M]; omega
  let v : Qubits (n + 1) → BoundedSupports n k → Fin (M + 1) → ℝ := fun S' A c =>
    Aux_w_maj_sdp.WVec M (Aux_w_maj_sdp.layerOf A)
      ⟨((Aux_w_maj_sdp.liftOdd A).filter fun i => S' i).card, by
        have h1 := Finset.card_filter_le (s := Aux_w_maj_sdp.liftOdd A) (p := fun i => S' i)
        have h2 := (Aux_w_maj_sdp.liftOdd_card_eq A).1
        omega⟩ c
  let X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ := fun x A B =>
    (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
      (∑ c : Fin (M + 1), v (Fin.snoc x true) A c * v (Fin.snoc x true) B c +
       ∑ c : Fin (M + 1), v (Fin.snoc (fun i => !(x i)) false) A c * v (Fin.snoc (fun i => !(x i)) false) B c)
  refine ⟨X, ?_, ?_⟩
  · constructor
    · intro x
      exact Aux_w_maj_sdp.gram_posSemidef ((2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))) (by positivity)
        (v (Fin.snoc x true)) (v (Fin.snoc (fun i => !(x i)) false))
    · intro A B hne
      have hne_lift : Aux_w_maj_sdp.liftOdd A ≠ Aux_w_maj_sdp.liftOdd B :=
        fun h => hne (Aux_w_maj_sdp.liftOdd_injective h)
      have hsplit : (∑ x : Qubits n,
          if majorityBit A.1 x ≠ majorityBit B.1 x then X x A B else 0) =
          ∑ S' : Qubits (n + 1),
            if majorityBit (Aux_w_maj_sdp.liftOdd A) S' ≠ majorityBit (Aux_w_maj_sdp.liftOdd B) S' then
              (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) * ∑ c : Fin (M + 1), v S' A c * v S' B c
            else 0 := by
        rw [← Fintype.sum_equiv (Aux_w_maj_sdp.snocSplitEquiv n) _ _ (fun z => rfl)]
        rw [Fintype.sum_sum_type]
        have h1 : (∑ x : Qubits n,
            if majorityBit (Aux_w_maj_sdp.liftOdd A) (Aux_w_maj_sdp.snocSplitEquiv n (Sum.inl x)) ≠
               majorityBit (Aux_w_maj_sdp.liftOdd B) (Aux_w_maj_sdp.snocSplitEquiv n (Sum.inl x)) then
              (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
                ∑ c : Fin (M + 1), v (Aux_w_maj_sdp.snocSplitEquiv n (Sum.inl x)) A c *
                  v (Aux_w_maj_sdp.snocSplitEquiv n (Sum.inl x)) B c
            else 0) =
            ∑ x : Qubits n, if majorityBit A.1 x ≠ majorityBit B.1 x then
              (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) * ∑ c : Fin (M + 1), v (Fin.snoc x true) A c * v (Fin.snoc x true) B c
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          refine if_congr ?_ ?_ rfl
          · dsimp [Aux_w_maj_sdp.snocSplitEquiv]
            rw [Aux_w_maj_sdp.liftOdd_majorityBit_snoc_true A x,
              Aux_w_maj_sdp.liftOdd_majorityBit_snoc_true B x]
          · dsimp [Aux_w_maj_sdp.snocSplitEquiv]
        have h2 : (∑ x : Qubits n,
            if majorityBit (Aux_w_maj_sdp.liftOdd A) (Aux_w_maj_sdp.snocSplitEquiv n (Sum.inr x)) ≠
               majorityBit (Aux_w_maj_sdp.liftOdd B) (Aux_w_maj_sdp.snocSplitEquiv n (Sum.inr x)) then
              (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
                ∑ c : Fin (M + 1), v (Aux_w_maj_sdp.snocSplitEquiv n (Sum.inr x)) A c *
                  v (Aux_w_maj_sdp.snocSplitEquiv n (Sum.inr x)) B c
            else 0) =
            ∑ x : Qubits n, if majorityBit A.1 x ≠ majorityBit B.1 x then
              (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
                ∑ c : Fin (M + 1), v (Fin.snoc (fun i => !(x i)) false) A c *
                  v (Fin.snoc (fun i => !(x i)) false) B c
            else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          refine if_congr ?_ ?_ rfl
          · dsimp [Aux_w_maj_sdp.snocSplitEquiv]
            rw [Aux_w_maj_sdp.liftOdd_majorityBit_snoc_false A x,
              Aux_w_maj_sdp.liftOdd_majorityBit_snoc_false B x]
            cases majorityBit A.1 x <;> cases majorityBit B.1 x <;> simp
          · dsimp [Aux_w_maj_sdp.snocSplitEquiv]
        rw [h1, h2, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h : majorityBit A.1 x ≠ majorityBit B.1 x
        · simp [h, X]; ring
        · simp [h]
      rw [hsplit]
      exact Aux_w_maj_sdp.odd_cross_moment_identity (Aux_w_maj_sdp.liftOdd_card_eq A).2
        (Aux_w_maj_sdp.liftOdd_card_eq B).2 (Aux_w_maj_sdp.liftOdd A) (Aux_w_maj_sdp.liftOdd B)
        (Aux_w_maj_sdp.liftOdd_card_eq A).1 (Aux_w_maj_sdp.liftOdd_card_eq B).1 hne_lift
  · intro A
    have hsplit : (∑ x : Qubits n, X x A A) =
        (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
          ∑ S' : Qubits (n + 1), ∑ c : Fin (M + 1), (v S' A c) ^ 2 := by
      rw [Finset.mul_sum]
      rw [← Fintype.sum_equiv (Aux_w_maj_sdp.snocSplitEquiv n) _ _ (fun z => rfl)]
      rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      dsimp [X, Aux_w_maj_sdp.snocSplitEquiv]
      simp_rw [sq]
      ring
    rw [hsplit]
    let A_ex : ExactSupports (n + 1) (2 * Aux_w_maj_sdp.layerOf A + 1) :=
      ⟨Aux_w_maj_sdp.liftOdd A, (Aux_w_maj_sdp.liftOdd_card_eq A).1⟩
    have hle_n : 2 * Aux_w_maj_sdp.layerOf A + 1 ≤ n + 1 := by
      have hlayer := (Aux_w_maj_sdp.liftOdd_card_eq A).2
      omega
    have hcore := hC_bound (n + 1) M (Aux_w_maj_sdp.layerOf A) hM1
      (Aux_w_maj_sdp.liftOdd_card_eq A).2 hle_n A_ex
    push_cast at hcore
    have hrew_v : (∑ S' : Qubits (n + 1), ∑ c : Fin (M + 1), (v S' A c) ^ 2) =
        ∑ S' : Qubits (n + 1), ∑ c : Fin (M + 1),
          (Aux_w_maj_sdp.WVec M (Aux_w_maj_sdp.layerOf A) (intersectionIndex A_ex S') c) ^ 2 := by
      rfl
    rw [hrew_v]
    have hk1 : 2 * M + 1 ≤ k + 1 := by
      dsimp [M]; omega
    have hk_sq : 2 * M + 1 ≤ k ^ 2 := by
      have hk_prod : k + 1 ≤ k * k := by nlinarith
      calc 2 * M + 1 ≤ k + 1 := hk1
        _ ≤ k * k := hk_prod
        _ = k ^ 2 := by ring
    have hlog_le : Real.log (2 * (M : ℝ) + 1) ≤ 2 * Real.log (k : ℝ) := by
      have h1 : (2 * (M : ℝ) + 1) ≤ ((k : ℝ) ^ 2) := by
        exact_mod_cast hk_sq
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h2
      simpa using h2
    calc (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
          ∑ S' : Qubits (n + 1), ∑ c : Fin (M + 1),
            (Aux_w_maj_sdp.WVec M (Aux_w_maj_sdp.layerOf A) (intersectionIndex A_ex S') c) ^ 2
        ≤ C_core * Real.log (2 * (M : ℝ) + 1) := hcore
      _ ≤ C_core * (2 * Real.log (k : ℝ)) := mul_le_mul_of_nonneg_left hlog_le hC_pos.le
      _ = 2 * C_core * Real.log (k : ℝ) := by ring
