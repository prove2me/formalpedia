-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.coupled_transducer_410
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T06:02:54.390618+00:00
-- url     : https://prove2.me/submissions/af03bfb5-d7a1-4a6d-9719-cf864ad1f8a1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_as_character_sum
import Theorems.Thm_QuantumLTF_Majority_krawtchouk_weighted_orthogonality
import Theorems.Thm_QuantumLTF_Majority_lemma_4_2_two_channel
import Theorems.Thm_QuantumLTF_Majority_normalized_intersection_sum
import Theorems.Thm_QuantumLTF_Majority_pointwise_correction_bound_to_log_energy
import Definitions.Def_QuantumLTF_Membership_Supplement_coupledOp410

set_option autoImplicit false

namespace Thm410Algebra

open QAlgorithms QuantumLTF.Majority QuantumLTF.Membership.Supplement.CoupledOp410

/-! ### Section 1: Krawtchouk identities and polynomial orthogonality -/

section KrawtchoukAndMod4

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

private lemma natDegree_prod_X_sub_C (k : ℕ) (f : ℕ → ℝ) :
    (∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (f i))).natDegree = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmon : (∏ i ∈ Finset.range k, (Polynomial.X - Polynomial.C (f i))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
    rw [Finset.prod_range_succ, Polynomial.natDegree_mul hmon.ne_zero (Polynomial.monic_X_sub_C _).ne_zero,
      ih, Polynomial.natDegree_X_sub_C]

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
  have hP1_deg : P₁.natDegree = j := natDegree_prod_X_sub_C j (fun i => (i : ℝ))
  have hQ2_deg : Q₂.natDegree = u - j := natDegree_prod_X_sub_C (u - j) (fun i => (r : ℝ) - (i : ℝ))
  have hneg1 : (-1 : Polynomial ℝ) = Polynomial.C (-1 : ℝ) := by simp
  have hP2_eq : (∏ i ∈ Finset.range (u - j), (Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ))) =
      Polynomial.C ((-1 : ℝ) ^ (u - j)) * Q₂ := by
    have hfac : ∀ i : ℕ, Polynomial.C (r : ℝ) - Polynomial.X - Polynomial.C (i : ℝ) =
        (-1 : Polynomial ℝ) * (Polynomial.X - Polynomial.C ((r : ℝ) - (i : ℝ))) := fun i => by
      simp only [map_sub]; ring
    simp_rw [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, hneg1, ← map_pow]
    rfl
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
    rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hjf huf) hu]
    rw [← hchR]
    ring
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
  let e₁ : Fin a ≃ A₁ := A₁.equivFin.symm
  let e₀ : Fin (r - a) ≃ A₀ := (A₀.equivFin.trans (finCongr hA₀_card)).symm
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
        dsimp only [φ] at hij; rw [dif_pos hi, dif_pos hj] at hij; exact hij
      have h'' := e₁.injective (Subtype.ext h')
      exact Fin.ext (congrArg (Fin.val : Fin a → ℕ) h'')
    · exfalso
      have h1 := (hφ_S i).mpr hi
      rw [hij] at h1
      exact hj ((hφ_S j).mp h1)
    · exfalso
      have h1 := (hφ_S j).mpr hj
      rw [← hij] at h1
      exact hi ((hφ_S i).mp h1)
    · have h' : (e₀ ⟨i - a, by omega⟩).1 = (e₀ ⟨j - a, by omega⟩).1 := by
        dsimp only [φ] at hij; rw [dif_neg hi, dif_neg hj] at hij; exact hij
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

lemma rootSetP_disjoint_rootSetQ (m : ℕ) : Disjoint (rootSetP m) (rootSetQ m) := by
  rw [Finset.disjoint_left]
  intro x hxP hxQ
  simp only [rootSetP, rootSetQ, Finset.mem_filter] at hxP hxQ
  omega

lemma rootSetP_union_rootSetQ (m : ℕ) : rootSetP m ∪ rootSetQ m = Finset.Icc 1 (2 * m) := by
  ext x
  simp only [Finset.mem_union, rootSetP, rootSetQ, Finset.mem_filter, Finset.mem_Icc]
  omega

lemma card_rootSetP_and_Q (m : ℕ) : (rootSetP m).card = m ∧ (rootSetQ m).card = m := by
  induction m with
  | zero => simp [rootSetP, rootSetQ]
  | succ m ih =>
    rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hP_step : rootSetP (k + k + 1) = insert (2 * (k + k) + 1) (rootSetP (k + k)) := by
        ext x
        simp only [Finset.mem_insert, rootSetP, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hQ_step : rootSetQ (k + k + 1) = insert (2 * (k + k) + 2) (rootSetQ (k + k)) := by
        ext x
        simp only [Finset.mem_insert, rootSetQ, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hnotP : 2 * (k + k) + 1 ∉ rootSetP (k + k) := by
        simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; omega
      have hnotQ : 2 * (k + k) + 2 ∉ rootSetQ (k + k) := by
        simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; omega
      exact ⟨by rw [hP_step, Finset.card_insert_of_notMem hnotP, ih.1],
             by rw [hQ_step, Finset.card_insert_of_notMem hnotQ, ih.2]⟩
    · have hP_step : rootSetP (2 * k + 1 + 1) = insert (2 * (2 * k + 1) + 2) (rootSetP (2 * k + 1)) := by
        ext x
        simp only [Finset.mem_insert, rootSetP, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hQ_step : rootSetQ (2 * k + 1 + 1) = insert (2 * (2 * k + 1) + 1) (rootSetQ (2 * k + 1)) := by
        ext x
        simp only [Finset.mem_insert, rootSetQ, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hnotP : 2 * (2 * k + 1) + 2 ∉ rootSetP (2 * k + 1) := by
        simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; omega
      have hnotQ : 2 * (2 * k + 1) + 1 ∉ rootSetQ (2 * k + 1) := by
        simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; omega
      exact ⟨by rw [hP_step, Finset.card_insert_of_notMem hnotP, ih.1],
             by rw [hQ_step, Finset.card_insert_of_notMem hnotQ, ih.2]⟩

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

lemma pPolyRaw_mul_qPolyRaw_eval_top (m : ℕ) :
    (pPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ) * (qPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ) =
      ((2 * m).factorial : ℝ) := by
  unfold pPolyRaw qPolyRaw
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [← Finset.prod_union (rootSetP_disjoint_rootSetQ m), rootSetP_union_rootSetQ]
  have hbij : (∏ r ∈ Finset.Icc 1 (2 * m), (((2 * m + 1 : ℕ) : ℝ) - (r : ℝ))) =
      ∏ v ∈ Finset.Icc 1 (2 * m), (v : ℝ) := by
    refine Finset.prod_bij (fun r _ => 2 * m + 1 - r)
      (fun r hr => by simp only [Finset.mem_Icc] at hr ⊢; omega)
      (fun r₁ r₂ hr₁ hr₂ h => by simp only [Finset.mem_Icc] at hr₁ hr₂; omega)
      (fun v hv => ⟨2 * m + 1 - v, by simp only [Finset.mem_Icc] at hv ⊢; omega, by
        simp only [Finset.mem_Icc] at hv; omega⟩)
      (fun r hr => by
        simp only [Finset.mem_Icc] at hr
        rw [Nat.cast_sub (by omega : r ≤ 2 * m + 1)])
  rw [hbij, prod_Icc_eq_factorial]

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

lemma PPoly_mul_QPoly_eval_top (m : ℕ) :
    (PPoly m).eval ((2 * m + 1 : ℕ) : ℝ) * (QPoly m).eval ((2 * m + 1 : ℕ) : ℝ) = 1 / 2 := by
  unfold PPoly QPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have hp := pPolyRaw_eval_zero_ne m
  have hq := qPolyRaw_eval_zero_ne m
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hfac : ((2 * m).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * m))
  have htop := pPolyRaw_mul_qPolyRaw_eval_top m
  have hzero := pPolyRaw_mul_qPolyRaw_eval_zero m
  calc (1 / (Real.sqrt 2 * (pPolyRaw m).eval 0) * (pPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ)) *
        (1 / (Real.sqrt 2 * (qPolyRaw m).eval 0) * (qPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ))
      = ((pPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ) * (qPolyRaw m).eval ((2 * m + 1 : ℕ) : ℝ)) /
          ((Real.sqrt 2 ^ 2) * ((pPolyRaw m).eval 0 * (qPolyRaw m).eval 0)) := by ring
    _ = ((2 * m).factorial : ℝ) / (2 * ((2 * m).factorial : ℝ)) := by rw [htop, hs, hzero]
    _ = 1 / 2 := by field_simp [hfac]

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

lemma rootSetP_mono {m l : ℕ} (hml : m ≤ l) : rootSetP m ⊆ rootSetP l := by
  intro r hr
  simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
  omega

lemma rootSetQ_mono {m l : ℕ} (hml : m ≤ l) : rootSetQ m ⊆ rootSetQ l := by
  intro r hr
  simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc] at hr ⊢
  omega

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

lemma choose_mul_compProd_le {l : ℕ} (_hl : 1 ≤ l) (t : Fin (2 * l + 1 + 1)) :
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
        rw [div_eq_div_iff hfac_pos.ne' (mul_ne_zero htR hrtR)]
        calc (r.choose (t : ℕ) : ℝ) * ((((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ)) *
                (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ))
            = (r.choose (t : ℕ) : ℝ) * (((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ) *
                (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by ring
          _ = (r : ℝ) * ((2 * l).factorial : ℝ) := hcast
      change (r.choose (t : ℕ) : ℝ) * ((((t : ℕ) - 1).factorial : ℝ) * ((2 * l - (t : ℕ)).factorial : ℝ)) / ((2 * l).factorial : ℝ) ≤ _
      rw [hreal]
      have hden1 : (((t : ℕ) + 1 : ℕ) : ℝ) ≤ 2 * ((t : ℕ) : ℝ) := by
        exact_mod_cast (by omega : (t : ℕ) + 1 ≤ 2 * (t : ℕ))
      have hden2 : ((r - (t : ℕ) + 1 : ℕ) : ℝ) ≤ 2 * ((r - (t : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (by omega : r - (t : ℕ) + 1 ≤ 2 * (r - (t : ℕ)))
      have ht_pos : (0 : ℝ) < ((t : ℕ) : ℝ) := by positivity
      have hrt_pos : (0 : ℝ) < ((r - (t : ℕ) : ℕ) : ℝ) := by positivity
      have hden_pos : (0 : ℝ) < (((t : ℕ) + 1 : ℕ) : ℝ) * ((r - (t : ℕ) + 1 : ℕ) : ℝ) := by positivity
      have hmul : (((t : ℕ) + 1 : ℕ) : ℝ) * ((r - (t : ℕ) + 1 : ℕ) : ℝ) ≤
          4 * (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by
        calc (((t : ℕ) + 1 : ℕ) : ℝ) * ((r - (t : ℕ) + 1 : ℕ) : ℝ)
            ≤ (2 * ((t : ℕ) : ℝ)) * (2 * ((r - (t : ℕ) : ℕ) : ℝ)) :=
              mul_le_mul hden1 hden2 (Nat.cast_nonneg _) (by positivity)
          _ = 4 * (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) := by ring
      have hdiv1 : (r : ℝ) / (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ)) =
          (4 * (r : ℝ)) / (4 * (((t : ℕ) : ℝ) * ((r - (t : ℕ) : ℕ) : ℝ))) := by
        rw [div_eq_div_iff (mul_pos ht_pos hrt_pos).ne' (by positivity)]; ring
      rw [hdiv1]
      exact div_le_div_of_nonneg_left (by positivity) hden_pos hmul

private lemma prod_erase_union {A B : Finset ℕ} (hdisj : Disjoint A B) (t : ℕ) (f : ℕ → ℝ) :
    (∏ u ∈ (A ∪ B).erase t, f u) = (∏ u ∈ A.erase t, f u) * (∏ u ∈ B.erase t, f u) := by
  have heq : (A ∪ B).erase t = A.erase t ∪ B.erase t := by
    ext x; simp only [Finset.mem_erase, Finset.mem_union]; tauto
  rw [heq, Finset.prod_union (hdisj.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))]

private lemma block4_real (x : ℝ) (hx : x < 0 ∨ 3 < x) :
    x ^ 2 * (x - 3) ^ 2 ≤ |x| * |x - 1| * |x - 2| * |x - 3| := by
  have hx03 : 0 < x * (x - 3) := by
    rcases hx with h | h
    · exact mul_pos_of_neg_of_neg h (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have hx12 : 0 < (x - 1) * (x - 2) := by
    rcases hx with h | h
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have hle : x * (x - 3) ≤ (x - 1) * (x - 2) := by linarith
  have h1 : x ^ 2 * (x - 3) ^ 2 = (x * (x - 3)) * (x * (x - 3)) := by ring
  have h2 : |x| * |x - 1| * |x - 2| * |x - 3| = (x * (x - 3)) * ((x - 1) * (x - 2)) := by
    calc |x| * |x - 1| * |x - 2| * |x - 3|
        = (|x| * |x - 3|) * (|x - 1| * |x - 2|) := by ring
      _ = |x * (x - 3)| * |(x - 1) * (x - 2)| := by rw [← abs_mul, ← abs_mul]
      _ = (x * (x - 3)) * ((x - 1) * (x - 2)) := by rw [abs_of_pos hx03, abs_of_pos hx12]
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hle hx03.le

private lemma block4_ineq (a t : ℕ) :
    (∏ u ∈ ({a, a + 3} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) then (2 : ℝ) else 1) *
        (∏ u ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = a
  · subst h0
    have hL : ({t, t + 3} : Finset ℕ).erase t = {t + 3} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
    have hR : ({t, t + 1, t + 2, t + 3} : Finset ℕ).erase t = {t + 1, t + 2, t + 3} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
    have hmem : t ∈ ({t, t + 1, t + 2, t + 3} : Finset ℕ) := by
      simp only [Finset.mem_insert, true_or]
    rw [hL, hR, if_pos hmem, Finset.prod_singleton,
      Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    have h1 : (t : ℝ) - ((t : ℝ) + 1) = -1 := by ring
    have h2 : (t : ℝ) - ((t : ℝ) + 2) = -2 := by ring
    have h3 : (t : ℝ) - ((t : ℝ) + 3) = -3 := by ring
    rw [h1, h2, h3]; norm_num
  · by_cases h1 : t = a + 1
    · subst h1
      have hL : ({a, a + 3} : Finset ℕ).erase (a + 1) = {a, a + 3} := by
        ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
      have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 1) = {a, a + 2, a + 3} := by
        ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
      have hmem : a + 1 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
        simp only [Finset.mem_insert, true_or, or_true]
      rw [hL, hR, if_pos hmem,
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton,
        Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
        Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      have e1 : ((a : ℝ) + 1) - (a : ℝ) = 1 := by ring
      have e2 : ((a : ℝ) + 1) - ((a : ℝ) + 2) = -1 := by ring
      have e3 : ((a : ℝ) + 1) - ((a : ℝ) + 3) = -2 := by ring
      rw [e1, e2, e3]; norm_num
    · by_cases h2 : t = a + 2
      · subst h2
        have hL : ({a, a + 3} : Finset ℕ).erase (a + 2) = {a, a + 3} := by
          ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
        have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 2) = {a, a + 1, a + 3} := by
          ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
        have hmem : a + 2 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
          simp only [Finset.mem_insert, true_or, or_true]
        rw [hL, hR, if_pos hmem,
          Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton,
          Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
          Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
        simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
        have e1 : ((a : ℝ) + 2) - (a : ℝ) = 2 := by ring
        have e2 : ((a : ℝ) + 2) - ((a : ℝ) + 1) = 1 := by ring
        have e3 : ((a : ℝ) + 2) - ((a : ℝ) + 3) = -1 := by ring
        rw [e1, e2, e3]; norm_num
      · by_cases h3 : t = a + 3
        · subst h3
          have hL : ({a, a + 3} : Finset ℕ).erase (a + 3) = {a} := by
            ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
          have hR : ({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 3) = {a, a + 1, a + 2} := by
            ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
          have hmem : a + 3 ∈ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
          rw [hL, hR, if_pos hmem, Finset.prod_singleton,
            Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
          simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
          have e1 : ((a : ℝ) + 3) - (a : ℝ) = 3 := by ring
          have e2 : ((a : ℝ) + 3) - ((a : ℝ) + 1) = 2 := by ring
          have e3 : ((a : ℝ) + 3) - ((a : ℝ) + 2) = 1 := by ring
          rw [e1, e2, e3]; norm_num
        · have hnotL : t ∉ ({a, a + 3} : Finset ℕ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]; omega
          have hnotR : t ∉ ({a, a + 1, a + 2, a + 3} : Finset ℕ) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]; omega
          rw [Finset.erase_eq_of_notMem hnotL, Finset.erase_eq_of_notMem hnotR, if_neg hnotR, one_mul,
            Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton,
            Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.prod_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
          simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
          have hlt_or_gt : t < a ∨ a + 3 < t := by omega
          have hx : (t : ℝ) - (a : ℝ) < 0 ∨ 3 < (t : ℝ) - (a : ℝ) := by
            rcases hlt_or_gt with hlt | hgt
            · left; exact sub_neg.mpr (Nat.cast_lt.mpr hlt)
            · right
              have hlt' : ((a + 3 : ℕ) : ℝ) < (t : ℝ) := Nat.cast_lt.mpr hgt
              rw [Nat.cast_add, Nat.cast_ofNat] at hlt'
              linarith
          have hb := block4_real ((t : ℝ) - (a : ℝ)) hx
          simp only [sub_add_eq_sub_sub, mul_assoc] at hb ⊢
          exact hb

private lemma pair2Left_ineq (t : ℕ) :
    (∏ u ∈ ({2} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t = 0 then (2 : ℝ) else 1) * (∏ u ∈ ({1, 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = 0
  · subst h0; norm_num
  · by_cases h1 : t = 1
    · subst h1
      have hL : ({2} : Finset ℕ).erase 1 = {2} := by decide
      have hR : ({1, 2} : Finset ℕ).erase 1 = {2} := by decide
      rw [hL, hR, if_neg h0, one_mul, Finset.prod_singleton, Finset.prod_singleton]
      norm_num
    · by_cases h2 : t = 2
      · subst h2
        have hL : ({2} : Finset ℕ).erase 2 = ∅ := by decide
        have hR : ({1, 2} : Finset ℕ).erase 2 = {1} := by decide
        rw [hL, hR, if_neg h0, one_mul, Finset.prod_empty, Finset.prod_singleton]
        norm_num
      · have hL : ({2} : Finset ℕ).erase t = {2} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_singleton]; omega
        have hR : ({1, 2} : Finset ℕ).erase t = {1, 2} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        rw [hL, hR, if_neg h0, one_mul, Finset.prod_singleton,
          Finset.prod_insert (by decide), Finset.prod_singleton]
        simp only [Nat.cast_ofNat, Nat.cast_one]
        have ht1 : (0 : ℝ) < (t : ℝ) - 1 := by
          have : (1 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 1 < t)
          linarith
        have ht2 : (0 : ℝ) < (t : ℝ) - 2 := by
          have : (2 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 2 < t)
          linarith
        rw [abs_of_pos ht1, abs_of_pos ht2, sq]
        exact mul_le_mul_of_nonneg_right (by linarith) ht2.le

private lemma pair2Right_ineq (a t : ℕ) (ht : t ≤ a + 2) :
    (∏ u ∈ ({a} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) ≤
      (if t = a + 2 then (2 : ℝ) else 1) * (∏ u ∈ ({a, a + 1} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) := by
  by_cases h0 : t = a
  · subst h0
    have hL : ({t} : Finset ℕ).erase t = ∅ := Finset.erase_singleton t
    have hR : ({t, t + 1} : Finset ℕ).erase t = {t + 1} := by
      ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
    rw [hL, hR, if_neg (by omega), one_mul, Finset.prod_empty, Finset.prod_singleton]
    simp only [Nat.cast_add, Nat.cast_one, sub_add_cancel_left, abs_neg, abs_one, le_refl]
  · by_cases h1 : t = a + 1
    · subst h1
      have hL : ({a} : Finset ℕ).erase (a + 1) = {a} := by
        refine Finset.erase_eq_of_notMem ?_
        simp only [Finset.mem_singleton]; omega
      have hR : ({a, a + 1} : Finset ℕ).erase (a + 1) = {a} := by
        ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; omega
      rw [hL, hR, if_neg (by omega), one_mul, Finset.prod_singleton, Finset.prod_singleton]
      simp only [Nat.cast_add, Nat.cast_one]
      have e : (a : ℝ) + 1 - (a : ℝ) = 1 := by ring
      rw [e]; norm_num
    · by_cases h2 : t = a + 2
      · subst h2
        have hL : ({a} : Finset ℕ).erase (a + 2) = {a} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_singleton]; omega
        have hR : ({a, a + 1} : Finset ℕ).erase (a + 2) = {a, a + 1} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        rw [hL, hR, if_pos rfl, Finset.prod_singleton,
          Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
        simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
        have e1 : (a : ℝ) + 2 - (a : ℝ) = 2 := by ring
        have e2 : (a : ℝ) + 2 - ((a : ℝ) + 1) = 1 := by ring
        rw [e1, e2]; norm_num
      · have hlt : t < a := by omega
        have hL : ({a} : Finset ℕ).erase t = {a} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_singleton]; omega
        have hR : ({a, a + 1} : Finset ℕ).erase t = {a, a + 1} := by
          refine Finset.erase_eq_of_notMem ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]; omega
        rw [hL, hR, if_neg h2, one_mul, Finset.prod_singleton,
          Finset.prod_insert (by simp only [Finset.mem_singleton]; omega), Finset.prod_singleton]
        simp only [Nat.cast_add, Nat.cast_one]
        have hneg1 : (t : ℝ) - (a : ℝ) < 0 := sub_neg.mpr (Nat.cast_lt.mpr hlt)
        have hneg2 : (t : ℝ) - ((a : ℝ) + 1) < 0 := by linarith
        rw [abs_of_neg hneg1, abs_of_neg hneg2]
        have hsq : ((t : ℝ) - (a : ℝ)) ^ 2 = ((a : ℝ) - (t : ℝ)) * ((a : ℝ) - (t : ℝ)) := by ring
        have hprod : -((t : ℝ) - (a : ℝ)) * -((t : ℝ) - ((a : ℝ) + 1)) =
            ((a : ℝ) - (t : ℝ)) * ((a : ℝ) - (t : ℝ) + 1) := by ring
        rw [hsq, hprod]
        exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)

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
    have h4a : 4 * j + 1 + 1 = 4 * j + 2 := by omega
    have h4b : 4 * j + 1 + 2 = 4 * j + 3 := by omega
    have h4c : 4 * j + 1 + 3 = 4 * j + 4 := by omega
    rw [h4a, h4b, h4c] at hb4
    have hmul := mul_le_mul ih hb4 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
          (if t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ) then (2 : ℝ) else 1) =
        if t ∈ Finset.Icc 1 (4 * j) ∪ {4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} then (2 : ℝ) else 1 := by
      simp only [Finset.mem_union]
      by_cases hA : t ∈ Finset.Icc 1 (4 * j) <;>
        by_cases hB : t ∈ ({4 * j + 1, 4 * j + 2, 4 * j + 3, 4 * j + 4} : Finset ℕ)
      · exfalso; exact Finset.disjoint_left.mp hdisj_Icc hA hB
      · rw [if_pos hA, if_neg hB, if_pos (Or.inl hA), mul_one]
      · rw [if_neg hA, if_pos hB, if_pos (Or.inr hB), one_mul]
      · rw [if_neg hA, if_neg hB, if_neg (fun h => h.elim hA hB), one_mul]
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
    have h2a : 4 * j + 1 + 1 = 4 * j + 2 := by omega
    have h2b : 4 * j + 1 + 2 = 4 * j + 3 := by omega
    rw [h2a, h2b] at h2
    have hmul := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
          (if t = 4 * j + 3 then (2 : ℝ) else 1) ≤ 2 := by
      by_cases hA : t ∈ Finset.Icc 1 (4 * j) <;> by_cases hB : t = 4 * j + 3
      · exfalso; simp only [Finset.mem_Icc] at hA; omega
      · rw [if_pos hA, if_neg hB, mul_one]
      · rw [if_neg hA, if_pos hB, one_mul]
      · rw [if_neg hA, if_neg hB, mul_one]; norm_num
    have hnn : 0 ≤ (∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
        ∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)| :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    calc (∏ u ∈ (rootSetP (2 * j)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j + 1} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ Finset.Icc 1 (4 * j) then (2 : ℝ) else 1) *
            (if t = 4 * j + 3 then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 1, 4 * j + 2} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          hmul.trans_eq (by ring)
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
      ext x; simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]; omega
    have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
    have hins : insert 0 (Finset.Icc 3 2) = {0} := by decide
    rw [hQ, hIcc, hins]
    have hp := pair2Left_ineq t
    have hmem : (t ∈ ({0} : Finset ℕ)) ↔ t = 0 := Finset.mem_singleton
    simp only [hmem]
    exact hp
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
    have h4a : 4 * j + 3 + 1 = 4 * j + 4 := by omega
    have h4b : 4 * j + 3 + 2 = 4 * j + 5 := by omega
    have h4c : 4 * j + 3 + 3 = 4 * j + 6 := by omega
    rw [h4a, h4b, h4c] at hb4
    have hmul := mul_le_mul ih hb4 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
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
      · rw [if_pos hA, if_neg hB, if_pos (Or.inl hA), mul_one]
      · rw [if_neg hA, if_pos hB, if_pos (Or.inr hB), one_mul]
      · rw [if_neg hA, if_neg hB, if_neg (fun h => h.elim hA hB), one_mul]
    calc (∏ u ∈ (rootSetQ (2 * j + 1)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j + 3, 4 * j + 6} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ insert 0 (Finset.Icc 3 (4 * j + 2)) then (2 : ℝ) else 1) *
            (if t ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ) then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j + 3, 4 * j + 4, 4 * j + 5, 4 * j + 6} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          hmul.trans_eq (by ring)
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
    have h2a : 4 * j' + 3 + 1 = 4 * j' + 4 := by omega
    have h2b : 4 * j' + 3 + 2 = 4 * j' + 5 := by omega
    rw [h2a, h2b] at h2
    have hmul := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun _ _ => abs_nonneg _))
    have hfac : (if t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) then (2 : ℝ) else 1) *
          (if t = 4 * j' + 5 then (2 : ℝ) else 1) ≤ 2 := by
      by_cases hA : t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) <;> by_cases hB : t = 4 * j' + 5
      · exfalso; simp only [Finset.mem_insert, Finset.mem_Icc] at hA; omega
      · rw [if_pos hA, if_neg hB, mul_one]
      · rw [if_neg hA, if_pos hB, one_mul]
      · rw [if_neg hA, if_neg hB, mul_one]; norm_num
    have hnn : 0 ≤ (∏ u ∈ (Finset.Icc 1 (4 * j' + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
        ∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)| :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)
    calc (∏ u ∈ (rootSetQ (2 * j' + 1)).erase t, ((t : ℝ) - (u : ℝ)) ^ 2) *
          ∏ u ∈ ({4 * j' + 3} : Finset ℕ).erase t, ((t : ℝ) - (u : ℝ)) ^ 2
        ≤ ((if t ∈ insert 0 (Finset.Icc 3 (4 * j' + 2)) then (2 : ℝ) else 1) *
            (if t = 4 * j' + 5 then (2 : ℝ) else 1)) *
          ((∏ u ∈ (Finset.Icc 1 (4 * j' + 2)).erase t, |(t : ℝ) - (u : ℝ)|) *
            ∏ u ∈ ({4 * j' + 3, 4 * j' + 4} : Finset ℕ).erase t, |(t : ℝ) - (u : ℝ)|) :=
          hmul.trans_eq (by ring)
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
    have hnot : 0 ∉ rootSetP l := by
      simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [Finset.erase_eq_of_notMem hnot, compProd_zero] at hP
    unfold pPolyRaw
    rw [Polynomial.eval_prod, ← Finset.prod_pow]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_zero] at hP ⊢
    exact hP
  have hq0 : ((qPolyRaw l).eval 0) ^ 2 ≤ 2 * ((2 * l).factorial : ℝ) := by
    have hQ := rootSetQ_bound l 0 hl (by omega)
    have hnot : 0 ∉ rootSetQ l := by
      simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; omega
    rw [Finset.erase_eq_of_notMem hnot, compProd_zero] at hQ
    unfold qPolyRaw
    rw [Polynomial.eval_prod, ← Finset.prod_pow]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_zero] at hQ ⊢
    exact hQ
  have hmul : ((pPolyRaw l).eval 0) ^ 2 * ((qPolyRaw l).eval 0) ^ 2 = (((2 * l).factorial : ℝ) ^ 2) := by
    calc ((pPolyRaw l).eval 0) ^ 2 * ((qPolyRaw l).eval 0) ^ 2
        = ((pPolyRaw l).eval 0 * (qPolyRaw l).eval 0) ^ 2 := by ring
      _ = ((2 * l).factorial : ℝ) ^ 2 := by rw [pPolyRaw_mul_qPolyRaw_eval_zero l]
  have hfac_pos : (0 : ℝ) < ((2 * l).factorial : ℝ) := by positivity
  have hp_pos : 0 < ((pPolyRaw l).eval 0) ^ 2 := sq_pos_of_ne_zero (pPolyRaw_eval_zero_ne l)
  have hq_pos : 0 < ((qPolyRaw l).eval 0) ^ 2 := sq_pos_of_ne_zero (qPolyRaw_eval_zero_ne l)
  constructor
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h1 := mul_le_mul_of_nonneg_left hq0 hp_pos.le
    rw [hmul, sq] at h1
    have h2 : ((2 * l).factorial : ℝ) * ((2 * l).factorial : ℝ) ≤
        ((pPolyRaw l).eval 0 ^ 2 * 2) * ((2 * l).factorial : ℝ) := by linarith
    exact le_of_mul_le_mul_right h2 hfac_pos
  · rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h1 := mul_le_mul_of_nonneg_right hp0 hq_pos.le
    rw [hmul, sq] at h1
    have h2 : ((2 * l).factorial : ℝ) * ((2 * l).factorial : ℝ) ≤
        ((qPolyRaw l).eval 0 ^ 2 * 2) * ((2 * l).factorial : ℝ) := by linarith
    exact le_of_mul_le_mul_right h2 hfac_pos

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

lemma CPoly_eval_root_of_ne {m l t : ℕ} (hml : m < l) (ht_ne : t ≠ 2 * m + 2) :
    (CPoly m l).eval (t : ℝ) =
      ((t : ℝ) / ((t : ℝ) - ((2 * m + 2 : ℕ) : ℝ))) *
        (if Even m then QPoly l else PPoly l).eval (t : ℝ) := by
  have heq := congrArg (Polynomial.eval (t : ℝ)) (linear_mul_DPoly hml)
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heq
  have hne : (t : ℝ) - ((2 * m + 2 : ℕ) : ℝ) ≠ 0 := by
    intro h
    apply ht_ne
    exact_mod_cast sub_eq_zero.mp h
  have hD : (DPoly m l).eval (t : ℝ) =
      (if Even m then QPoly l else PPoly l).eval (t : ℝ) / ((t : ℝ) - ((2 * m + 2 : ℕ) : ℝ)) := by
    rw [eq_div_iff hne]
    linarith [heq]
  simp only [CPoly, Polynomial.eval_mul, Polynomial.eval_X, hD]
  ring

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

/-! ### Odd-cardinality (n+1)-variable lift -/

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

end KrawtchoukAndMod4

/-! ### Section 2: LSB encoding, two-level matrices, and Appendix C.5.2 block unitaries -/

section TransducerAlgebra410

/-! ### Vector / matrix action helpers -/

lemma act_one_vec {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) ψ = ψ := by
  ext y; simp [act]

lemma act_add {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ + φ) = act U ψ + act U φ := by
  ext y; simp [act, Matrix.mulVec_add]

lemma act_smul {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act U (c • ψ) = c • act U ψ := by
  ext y; simp [act, Matrix.mulVec_smul]

lemma act_sum {ι κ : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) :
    act U (∑ x ∈ s, f x) = ∑ x ∈ s, act U (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext y; simp [act]
  | insert a s ha ih => rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext y; simp [act, Matrix.mulVec_mulVec]

lemma act_ket_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (z : ι) :
    act U (ket z) = ∑ y : ι, (U y z) • ket y := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single z]
  · simp only [↓reduceIte, mul_one]
    rw [Finset.sum_eq_single y] <;> simp (config := { contextual := true }) [eq_comm]
  · intro u _ hu; simp [hu]
  · simp

lemma pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliX,
    Matrix.of_apply]
  cases a <;> cases b <;> norm_num

lemma pauliZ_mem_unitaryGroup : pauliZ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Fintype.sum_bool, pauliZ,
    Matrix.diagonal_apply]
  cases a <;> cases b <;> norm_num

lemma hadamard_mem_unitaryGroup : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hHs : star hadamard = hadamard := by
    ext a b; cases a <;> cases b <;> simp [hadamard, Matrix.star_apply, Complex.conj_ofReal]
  rw [hHs, hadamard_mul_self]

lemma hadamardN_mul_self (n : ℕ) : hadamardN n * hadamardN n = 1 := by
  ext y z
  have h2 : (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) =
      ((2 : ℂ)⁻¹) ^ n := by
    rw [← Complex.ofReal_mul, ← sq, ← pow_mul, mul_comm n 2, pow_mul, inv_pow,
      Real.sq_sqrt (by norm_num)]
    push_cast
    rfl
  have hdot : ∀ i : Qubits n, xor (dotBits i y) (dotBits i z) = dotBits i (y + z) := by
    intro i
    simp only [dotBits]
    change (∑ k, (i k && y k)) + (∑ k, (i k && z k)) = ∑ k, (i k && (y + z) k)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply]
    cases i k <;> cases y k <;> cases z k <;> rfl
  have hsum : ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) =
      if y = z then (2 ^ n : ℂ) else 0 := by
    by_cases hyz : y = z
    · subst hyz
      have h0 : ∀ k, (y + y) k = false := fun k => by simp only [Pi.add_apply]; cases y k <;> rfl
      have hdot0 : ∀ i : Qubits n, dotBits i (y + y) = false := fun i => by
        simp only [dotBits, h0, Bool.and_false]
        exact (Finset.sum_const_zero (s := Finset.univ) : (∑ _ : Fin n, (0 : Bool)) = 0)
      simp [hdot0]
    · rw [if_neg hyz]
      have hne : ∃ r : Fin n, (y + z) r = true := by
        by_contra hc
        push Not at hc
        apply hyz
        funext r
        have hr := hc r
        revert hr
        simp only [Pi.add_apply]
        cases y r <;> cases z r <;> decide
      obtain ⟨r, hr⟩ := hne
      let flip : Qubits n ≃ Qubits n :=
        { toFun := fun i => Function.update i r (!(i r))
          invFun := fun i => Function.update i r (!(i r))
          left_inv := fun i => by funext k; by_cases hk : k = r <;> simp [Function.update, hk]
          right_inv := fun i => by funext k; by_cases hk : k = r <;> simp [Function.update, hk] }
      have hflip : ∀ i : Qubits n, dotBits (flip i) (y + z) = !(dotBits i (y + z)) := by
        intro i
        simp only [dotBits]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
          ← Finset.add_sum_erase (Finset.univ) (fun k => i k && (y + z) k) (Finset.mem_univ r)]
        have hrest : ∑ k ∈ Finset.univ.erase r, (flip i k && (y + z) k) =
            ∑ k ∈ Finset.univ.erase r, (i k && (y + z) k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkr : k ≠ r := (Finset.mem_erase.mp hk).1
          simp [flip, Function.update_of_ne hkr]
        rw [hrest]
        have hhead : (flip i r && (y + z) r) = !(i r && (y + z) r) := by
          simp [flip, hr]
        rw [hhead]
        cases (i r && (y + z) r) <;> cases (∑ k ∈ Finset.univ.erase r, (i k && (y + z) k)) <;> decide
      have hpair : ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) =
          ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) :=
        Fintype.sum_equiv flip _ _ fun _ => rfl
      have hneg : ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) =
          - ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hflip i]
        cases dotBits i (y + z) <;> simp
      have h2s : (2 : ℂ) * ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) = 0 := by
        calc (2 : ℂ) * ∑ i : Qubits n, _
            = ∑ i : Qubits n, _ + ∑ i : Qubits n, _ := two_mul _
          _ = ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) +
              ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) := by rw [hpair]
          _ = 0 := by rw [hneg, add_neg_cancel]
      exact (mul_eq_zero.mp h2s).resolve_left (by norm_num)
  simp only [Matrix.mul_apply, hadamardN, Matrix.of_apply, Matrix.one_apply]
  have hterm : ∀ i : Qubits n,
      (if dotBits i y then -(((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) else (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ)) *
      (if dotBits z i then -(((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) else (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ)) =
      ((2 : ℂ)⁻¹) ^ n * (if dotBits i (y + z) then (-1 : ℂ) else 1) := by
    intro i
    have hdz : dotBits z i = dotBits i z := by simp only [dotBits, Bool.and_comm]
    rw [hdz, ← hdot i]
    cases dotBits i y <;> cases dotBits i z <;> simp [← h2]
  simp_rw [hterm, ← Finset.mul_sum, hsum]
  by_cases hyz : y = z
  · simp [hyz, inv_pow, pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)]
  · simp [hyz]

lemma hadamardN_mem_unitaryGroup (n : ℕ) :
    hadamardN n ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, hadamardN_star, hadamardN_mul_self]

noncomputable def uniformSubsetKet (n : ℕ) (A : Finset (Fin n)) (t : ℕ) :
    EuclideanSpace ℂ (Qubits n) :=
  ∑ T ∈ A.powersetCard t, ket (fun i : Fin n => decide (i ∈ T))

lemma uniformSubsetKet_zero (n : ℕ) (A : Finset (Fin n)) :
    uniformSubsetKet n A 0 = zeroKet n := by
  simp [uniformSubsetKet, zeroKet, Finset.powersetCard_zero]

lemma uniformSubsetKet_self {n : ℕ} (A : Finset (Fin n)) :
    uniformSubsetKet n A A.card = ket (fun i : Fin n => decide (i ∈ A)) := by
  simp [uniformSubsetKet, Finset.powersetCard_self]

lemma hammingWeight_indicator {n : ℕ} (T : Finset (Fin n)) :
    hammingWeight (fun i : Fin n => decide (i ∈ T)) = T.card := by
  simp [hammingWeight]

private lemma dotBits_indicator_eq_bool_sum {n : ℕ} (T : Finset (Fin n)) (S : Qubits n) :
    (if dotBits (fun i => decide (i ∈ T)) S then (-1 : ℂ) else 1) =
      (-1 : ℂ) ^ ((T.filter fun i => S i).card) := by
  have hsum : dotBits (fun i => decide (i ∈ T)) S =
      decide (Odd ((T.filter fun i => S i).card)) := by
    unfold dotBits
    have hbool : ∀ (s : Finset (Fin n)),
        (∑ k ∈ s, (decide (k ∈ T) && S k)) = decide (Odd ((s.filter fun k => k ∈ T ∧ S k = true).card)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, ih]
        by_cases hcond : a ∈ T ∧ S a = true
        · have hnot : a ∉ s.filter (fun k => k ∈ T ∧ S k = true) := fun h => ha (Finset.mem_filter.mp h).1
          rw [Finset.filter_insert, if_pos hcond, Finset.card_insert_of_notMem hnot]
          have hbit : (decide (a ∈ T) && S a) = true := by simp [hcond.1, hcond.2]
          rw [hbit]
          by_cases hodd : Odd ((s.filter fun k => k ∈ T ∧ S k = true).card)
          · have hnotodd : ¬ Odd ((s.filter fun k => k ∈ T ∧ S k = true).card + 1) := by
              rcases hodd with ⟨m, hm⟩; rw [hm]; exact Nat.not_odd_iff_even.mpr ⟨m + 1, by omega⟩
            simp [hodd, hnotodd]; rfl
          · have hodd' : Odd ((s.filter fun k => k ∈ T ∧ S k = true).card + 1) := by
              rw [Nat.not_odd_iff_even] at hodd
              rcases hodd with ⟨m, hm⟩; rw [hm]; exact ⟨m, by omega⟩
            simp [hodd, hodd']; rfl
        · rw [Finset.filter_insert, if_neg hcond]
          have hbit : (decide (a ∈ T) && S a) = false := by
            by_cases haT : a ∈ T <;> by_cases hSa : S a = true <;> simp_all
          rw [hbit]
          change false + decide (Odd _) = decide (Odd _)
          cases decide (Odd ((s.filter fun k => k ∈ T ∧ S k = true).card)) <;> rfl
    have hfilt : Finset.univ.filter (fun k => k ∈ T ∧ S k = true) = T.filter fun i => S i := by
      ext k; simp
    rw [hbool Finset.univ, hfilt]
  rw [hsum]
  rcases Nat.even_or_odd ((T.filter fun i => S i).card) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hnot : ¬ Odd (m + m) := Nat.not_odd_iff_even.mpr ⟨m, rfl⟩
    rw [hm, decide_eq_false hnot, if_neg Bool.false_ne_true, ← two_mul, pow_mul]
    norm_num
  · have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
    rw [hm, decide_eq_true hodd, if_pos rfl, pow_add, pow_mul]
    norm_num

lemma act_hadamardN_chiVec {n : ℕ} (T : Finset (Fin n)) :
    act (hadamardN n)
        (WithLp.toLp 2 fun S : Qubits n =>
          (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (-1 : ℂ) ^ ((T.filter fun i => S i).card)) =
      ket (fun i : Fin n => decide (i ∈ T)) := by
  let indT : Qubits n := fun i => decide (i ∈ T)
  have hcol : (WithLp.toLp 2 fun S : Qubits n =>
        (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) * (-1 : ℂ) ^ ((T.filter fun i => S i).card)) =
      WithLp.toLp 2 fun S : Qubits n => hadamardN n S indT := by
    ext S
    simp only [hadamardN, Matrix.of_apply]
    rw [← dotBits_indicator_eq_bool_sum T S]
    split_ifs <;> ring
  rw [hcol]
  ext j
  change (hadamardN n * hadamardN n) j indT = ket indT j
  rw [hadamardN_mul_self]
  simp [ket, Matrix.one_apply, PiLp.single_apply]

lemma act_hadamardN_krawtchouk_combo {n' m : ℕ} (A : Finset (Fin n')) (hA : A.card = 2 * m + 1)
    (c : Fin (2 * m + 2) → ℝ) :
    act (hadamardN n')
        (WithLp.toLp 2 fun S : Qubits n' =>
          (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
            ∑ t : Fin (2 * m + 2),
              (krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) * (c t : ℂ)) =
      ∑ t : Fin (2 * m + 2), (c t : ℂ) • uniformSubsetKet n' A t.1 := by
  let chiVec : Finset (Fin n') → EuclideanSpace ℂ (Qubits n') := fun T =>
    WithLp.toLp 2 fun S : Qubits n' =>
      (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) * (-1 : ℂ) ^ ((T.filter fun i => S i).card)
  have hvec_eq :
      (WithLp.toLp 2 fun S : Qubits n' =>
        (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
          ∑ t : Fin (2 * m + 2),
            (krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) * (c t : ℂ)) =
      ∑ t : Fin (2 * m + 2), (c t : ℂ) • ∑ T ∈ A.powersetCard t.1, chiVec T := by
    ext S
    have hk := krawtchouk_eq_powersetCard_sum A hA
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      chiVec]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hkt : (krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) =
        ∑ T ∈ A.powersetCard t.1, (-1 : ℂ) ^ ((T.filter fun i => S i).card) := by
      have hktZ := hk t S
      exact_mod_cast hktZ
    change (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
          ((krawtchouk (2 * m + 1) t (intersectionIndex ⟨A, hA⟩ S) : ℂ) * (c t : ℂ)) =
        (c t : ℂ) * ∑ T ∈ A.powersetCard t.1,
          (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) * (-1 : ℂ) ^ ((T.filter fun i => S i).card)
    rw [hkt, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => by ring
  rw [hvec_eq, act_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [act_smul, act_sum]
  congr 1
  unfold uniformSubsetKet
  refine Finset.sum_congr rfl fun T _ => act_hadamardN_chiVec T

/-! ### Explicit two-level & diagonal sign blocks of Appendix C.5.2 -/

private lemma twoLevelMat_apply {ι : Type*} [DecidableEq ι] (u v : ι) (huv : u ≠ v)
    (M2 : Matrix Bool Bool ℂ) (r c : ι) :
    twoLevelMat u v huv M2 r c =
      if r = u then if c = u then M2 false false else if c = v then M2 false true else 0
      else if r = v then if c = u then M2 true false else if c = v then M2 true true else 0
      else if c = r then 1 else 0 := by
  unfold twoLevelMat
  rw [Matrix.of_apply]
  by_cases hru : r = u <;> by_cases hrv : r = v <;>
    by_cases hcu : c = u <;> by_cases hcv : c = v <;>
    simp_all [huv.symm]

private lemma twoLevelMat_congr_right {ι : Type*} [DecidableEq ι] (u v₁ v₂ : ι) (hv : v₁ = v₂)
    (h1 : u ≠ v₁) (h2 : u ≠ v₂) (M2 : Matrix Bool Bool ℂ) :
    twoLevelMat u v₁ h1 M2 = twoLevelMat u v₂ h2 M2 := by
  subst hv; rfl

lemma twoLevelMat_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι) (huv : u ≠ v) (M2 : Matrix Bool Bool ℂ) (hM2 : M2 ∈ Matrix.unitaryGroup Bool ℂ) :
    twoLevelMat u v huv M2 ∈ Matrix.unitaryGroup ι ℂ := by
  have hm := Matrix.mem_unitaryGroup_iff.mp hM2
  have hentry : ∀ b₁ b₂ : Bool,
      M2 b₁ false * starRingEnd ℂ (M2 b₂ false) + M2 b₁ true * starRingEnd ℂ (M2 b₂ true) =
        if b₁ = b₂ then (1 : ℂ) else 0 := by
    intro b₁ b₂
    have h := congrFun (congrFun hm b₁) b₂
    simpa [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_bool, Matrix.one_apply, add_comm] using h
  rw [Matrix.mem_unitaryGroup_iff]
  ext r c
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply]
  have hv_mem : v ∈ (Finset.univ : Finset ι).erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u),
    ← Finset.add_sum_erase ((Finset.univ : Finset ι).erase u) _ hv_mem]
  have hrest_zero : ∀ s : ι, s ∈ ((Finset.univ : Finset ι).erase u).erase v →
      twoLevelMat u v huv M2 r s * star (twoLevelMat u v huv M2 c s) =
        if r ≠ u ∧ r ≠ v ∧ s = r ∧ c = r then (1 : ℂ) else 0 := by
    intro s hs
    have hsv : s ≠ v := (Finset.mem_erase.mp hs).1
    have hsu : s ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
    by_cases hsr : r ≠ u ∧ r ≠ v ∧ s = r
    · rcases hsr with ⟨hru, hrv, hsr_eq⟩
      subst hsr_eq
      by_cases hcr : c = s
      · subst hcr
        simp [twoLevelMat_apply, hru, hrv]
      · simp [twoLevelMat_apply, hru, hrv, hcr, Ne.symm hcr]
    · simp only [twoLevelMat_apply]
      by_cases hru : r = u
      · simp [hru, hsu, hsv]
      · by_cases hrv : r = v
        · simp [hrv, hsu, hsv]
        · have hne : s ≠ r := fun h => hsr ⟨hru, hrv, h⟩
          simp [hru, hrv, hne]
  have hsum_rest : ∑ s ∈ ((Finset.univ : Finset ι).erase u).erase v,
      twoLevelMat u v huv M2 r s * star (twoLevelMat u v huv M2 c s) =
      if r ≠ u ∧ r ≠ v ∧ c = r then (1 : ℂ) else 0 := by
    rw [Finset.sum_congr rfl fun s hs => hrest_zero s hs]
    by_cases hr : r ≠ u ∧ r ≠ v ∧ c = r
    · rcases hr with ⟨hru, hrv, rfl⟩
      rw [if_pos ⟨hru, hrv, rfl⟩, Finset.sum_eq_single c]
      · simp [hru, hrv]
      · intro s _ hsc; simp [hsc]
      · intro hnot
        exfalso; apply hnot
        exact Finset.mem_erase.mpr ⟨hrv, Finset.mem_erase.mpr ⟨hru, Finset.mem_univ c⟩⟩
    · rw [if_neg hr]
      refine Finset.sum_eq_zero fun s _ => ?_
      split_ifs with h
      · exact False.elim (hr ⟨h.1, h.2.1, h.2.2.2⟩)
      · rfl
  rw [hsum_rest]
  by_cases hru : r = u
  · by_cases hcu : c = u
    · rw [hru, hcu]
      simp only [twoLevelMat_apply, huv.symm, ↓reduceIte, ne_eq, not_true_eq_false, false_and,
        RCLike.star_def]
      simpa using hentry false false
    · by_cases hcv : c = v
      · rw [hru, hcv]
        simp only [twoLevelMat_apply, huv, huv.symm, ↓reduceIte, ne_eq, not_true_eq_false,
          false_and, RCLike.star_def]
        simpa using hentry false true
      · rw [hru]
        simp [twoLevelMat_apply, huv.symm, hcu, hcv, Ne.symm hcu, Ne.symm hcv]
  · by_cases hrv : r = v
    · by_cases hcu : c = u
      · rw [hrv, hcu]
        simp only [twoLevelMat_apply, huv.symm, ↓reduceIte, ne_eq, not_true_eq_false,
          false_and, RCLike.star_def]
        simpa using hentry true false
      · by_cases hcv : c = v
        · rw [hrv, hcv]
          simp only [twoLevelMat_apply, huv.symm, ↓reduceIte, ne_eq, not_true_eq_false,
            false_and, RCLike.star_def]
          simpa using hentry true true
        · rw [hrv]
          simp [twoLevelMat_apply, huv.symm, hcu, hcv, Ne.symm hcu, Ne.symm hcv]
    · by_cases hcu : c = u
      · rw [hcu]
        simp [twoLevelMat_apply, huv.symm, hru, hrv, Ne.symm hru, Ne.symm hrv]
      · by_cases hcv : c = v
        · rw [hcv]
          simp [twoLevelMat_apply, huv.symm, hru, hrv, Ne.symm hru, Ne.symm hrv]
        · by_cases hcr : c = r
          · rw [hcr]
            simp [twoLevelMat_apply, hru, hrv, Ne.symm hru, Ne.symm hrv]
          · simp [twoLevelMat_apply, hru, hrv, hcu, hcv, hcr, Ne.symm hru, Ne.symm hrv, Ne.symm hcr]

lemma act_twoLevelMat_ket_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι) (huv : u ≠ v) (M2 : Matrix Bool Bool ℂ) :
    act (twoLevelMat u v huv M2) (ket u) = M2 false false • ket u + M2 true false • ket v := by
  rw [act_ket_eq]
  have h1 : ∀ y : ι, twoLevelMat u v huv M2 y u =
      (if y = u then M2 false false else if y = v then M2 true false else 0) := by
    intro y
    by_cases hyu : y = u
    · simp [twoLevelMat_apply, hyu]
    · by_cases hyv : y = v
      · simp [twoLevelMat_apply, hyv, huv.symm]
      · simp [twoLevelMat_apply, hyu, hyv, Ne.symm hyu]
  simp_rw [h1]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u)]
  have hv_mem : v ∈ (Finset.univ : Finset ι).erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩
  rw [← Finset.add_sum_erase ((Finset.univ : Finset ι).erase u) _ hv_mem]
  have hrest : ∑ x ∈ ((Finset.univ : Finset ι).erase u).erase v,
      (if x = u then M2 false false else if x = v then M2 true false else 0) • ket x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
    have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp [hxu, hxv]
  rw [hrest, add_zero]
  simp [huv.symm]

lemma act_twoLevelMat_ket_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι) (huv : u ≠ v) (M2 : Matrix Bool Bool ℂ) :
    act (twoLevelMat u v huv M2) (ket v) = M2 false true • ket u + M2 true true • ket v := by
  rw [act_ket_eq]
  have h1 : ∀ y : ι, twoLevelMat u v huv M2 y v =
      (if y = u then M2 false true else if y = v then M2 true true else 0) := by
    intro y
    by_cases hyu : y = u
    · simp [twoLevelMat_apply, hyu, huv.symm]
    · by_cases hyv : y = v
      · simp [twoLevelMat_apply, hyv, huv.symm]
      · simp [twoLevelMat_apply, hyu, hyv, Ne.symm hyv]
  simp_rw [h1]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u)]
  have hv_mem : v ∈ (Finset.univ : Finset ι).erase u := Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩
  rw [← Finset.add_sum_erase ((Finset.univ : Finset ι).erase u) _ hv_mem]
  have hrest : ∑ x ∈ ((Finset.univ : Finset ι).erase u).erase v,
      (if x = u then M2 false true else if x = v then M2 true true else 0) • ket x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
    have hxu : x ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    simp [hxu, hxv]
  rw [hrest, add_zero]
  simp [huv.symm]

lemma act_twoLevelMat_ket_other {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v w : ι) (huv : u ≠ v) (hwu : w ≠ u) (hwv : w ≠ v) (M2 : Matrix Bool Bool ℂ) :
    act (twoLevelMat u v huv M2) (ket w) = ket w := by
  rw [act_ket_eq]
  rw [Finset.sum_eq_single w]
  · simp [twoLevelMat_apply, hwu, hwv]
  · intro y _ hyw
    by_cases hyu : y = u
    · simp [twoLevelMat_apply, hyu, hwu, hwv]
    · by_cases hyv : y = v
      · simp [twoLevelMat_apply, hyv, huv.symm, hwu, hwv]
      · simp [twoLevelMat_apply, hyu, hyv, hyw.symm]
  · intro hnot; exact absurd (Finset.mem_univ w) hnot

lemma diagSign410_mul_star (M t : ℕ) (v : Qubits (qW M)) :
    diagSign410 M t v * star (diagSign410 M t v) = 1 := by
  unfold diagSign410
  dsimp only
  split_ifs with h0 h1 h2 h3
  · simp
  · simp [← pow_add, ← two_mul, pow_mul]
  · simp
  · simp [← pow_add, ← two_mul, pow_mul]
  · simp [← pow_add, ← two_mul, pow_mul]

lemma D_mat410_mem_unitaryGroup (M t : ℕ) :
    D_mat410 M t ∈ Matrix.unitaryGroup (Qubits (qW M)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext u v
  simp only [D_mat410, Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl, Finset.sum_eq_single u]
    · simp only [↓reduceIte]; exact diagSign410_mul_star M t u
    · intro x _ hxu; simp [Ne.symm hxu]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg huv]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hux : u = x
    · rw [← hux]; simp [Ne.symm huv]
    · simp [hux]

lemma act_D_mat410_ket (M t : ℕ) (v : Qubits (qW M)) :
    act (D_mat410 M t) (ket v) = diagSign410 M t v • ket v := by
  rw [act_ket_eq, Finset.sum_eq_single v]
  · simp [D_mat410]
  · intro y _ hy; simp [D_mat410, hy]
  · intro h; exact absurd (Finset.mem_univ v) h

lemma rhoJ_ne_zero (j : ℕ) : rhoJ j ≠ 0 := by
  have hmul := PPoly_mul_QPoly_eval_top j
  unfold rhoJ
  split_ifs <;> intro h
  · have hp : (PPoly j).eval ((2 * j + 1 : ℕ) : ℝ) = 0 := by linarith
    rw [hp, zero_mul] at hmul
    norm_num at hmul
  · have hq : (QPoly j).eval ((2 * j + 1 : ℕ) : ℝ) = 0 := by linarith
    rw [hq, mul_zero] at hmul
    norm_num at hmul

lemma AJ_sq_eq (j : ℕ) : AJ j ^ 2 = 1 + BJ j ^ 2 := by
  have hrho : rhoJ j ≠ 0 := rhoJ_ne_zero j
  unfold AJ BJ
  field_simp [hrho]
  ring

lemma AJ_ne_zero (j : ℕ) : AJ j ≠ 0 := by
  intro h
  have hsq := AJ_sq_eq j
  rw [h, zero_pow (by norm_num)] at hsq
  nlinarith [sq_nonneg (BJ j)]

lemma R2J_mem_unitaryGroup (j : ℕ) : R2J j ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hAne : (AJ j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (AJ_ne_zero j)
  have hsq : (AJ j : ℂ) ^ 2 = (BJ j : ℂ) ^ 2 + 1 := by
    exact_mod_cast (show AJ j ^ 2 = BJ j ^ 2 + 1 by linarith [AJ_sq_eq j])
  ext r c
  cases r <;> cases c <;>
    simp only [R2J, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Fintype.sum_bool,
      Matrix.one_apply, RCLike.star_def, map_div₀, map_one, map_neg, Complex.conj_ofReal,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
  · field_simp [hAne]; linear_combination -hsq
  · field_simp [hAne]; ring
  · field_simp [hAne]; ring
  · field_simp [hAne]; linear_combination -hsq

lemma alphaM_sq_eq (M : ℕ) : alphaM M ^ 2 = 1 + betaM M ^ 2 := by
  have hmul := PPoly_mul_QPoly_eval_top M
  have hpow : ((-1 : ℝ) ^ (M + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold alphaM betaM
  rw [div_pow, div_pow, hs]
  have hsqPQ : (((-1 : ℝ) ^ (M + 1)) * ((PPoly M).eval ((2 * M + 1 : ℕ) : ℝ) + (QPoly M).eval ((2 * M + 1 : ℕ) : ℝ))) ^ 2 =
      2 + ((PPoly M).eval ((2 * M + 1 : ℕ) : ℝ) - (QPoly M).eval ((2 * M + 1 : ℕ) : ℝ)) ^ 2 := by
    calc (((-1 : ℝ) ^ (M + 1)) * ((PPoly M).eval ((2 * M + 1 : ℕ) : ℝ) + (QPoly M).eval ((2 * M + 1 : ℕ) : ℝ))) ^ 2
        = (((-1 : ℝ) ^ (M + 1)) ^ 2) * ((PPoly M).eval ((2 * M + 1 : ℕ) : ℝ) + (QPoly M).eval ((2 * M + 1 : ℕ) : ℝ)) ^ 2 := by ring
      _ = ((PPoly M).eval ((2 * M + 1 : ℕ) : ℝ) + (QPoly M).eval ((2 * M + 1 : ℕ) : ℝ)) ^ 2 := by rw [hpow, one_mul]
      _ = 2 + ((PPoly M).eval ((2 * M + 1 : ℕ) : ℝ) - (QPoly M).eval ((2 * M + 1 : ℕ) : ℝ)) ^ 2 := by
          linear_combination 4 * hmul
  rw [hsqPQ]
  ring

lemma alphaM_ne_zero (M : ℕ) : alphaM M ≠ 0 := by
  intro h
  have hsq := alphaM_sq_eq M
  rw [h, zero_pow (by norm_num)] at hsq
  nlinarith [sq_nonneg (betaM M)]

lemma R2Top_mem_unitaryGroup (M : ℕ) : R2Top M ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hAne : (alphaM M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (alphaM_ne_zero M)
  have hsq : (alphaM M : ℂ) ^ 2 = (betaM M : ℂ) ^ 2 + 1 := by
    exact_mod_cast (show alphaM M ^ 2 = betaM M ^ 2 + 1 by linarith [alphaM_sq_eq M])
  ext r c
  cases r <;> cases c <;>
    simp only [R2Top, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Fintype.sum_bool,
      Matrix.one_apply, RCLike.star_def, map_div₀, map_one, map_neg, Complex.conj_ofReal,
      ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
  · field_simp [hAne]; linear_combination -hsq
  · field_simp [hAne]; ring
  · field_simp [hAne]; ring
  · field_simp [hAne]; linear_combination -hsq

lemma R_mat410_mem_unitaryGroup (M t : ℕ) :
    R_mat410 M t ∈ Matrix.unitaryGroup (Qubits (qW M)) ℂ := by
  unfold R_mat410
  split_ifs with ht0 hodd htop
  · exact twoLevelMat_mem_unitaryGroup _ _ _ _ pauliX_mem_unitaryGroup
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _
      (twoLevelMat_mem_unitaryGroup _ _ _ _ hadamard_mem_unitaryGroup)
      (twoLevelMat_mem_unitaryGroup _ _ _ _ (R2J_mem_unitaryGroup (t / 2))))
      (twoLevelMat_mem_unitaryGroup _ _ _ _ hadamard_mem_unitaryGroup)
  · exact twoLevelMat_mem_unitaryGroup _ _ _ _ (R2Top_mem_unitaryGroup M)
  · exact Submonoid.one_mem _

lemma U_op410_mem_unitaryGroup (M t : ℕ) :
    U_op410 M t ∈ Matrix.unitaryGroup (Qubits (qW M)) ℂ := by
  unfold U_op410
  split_ifs
  · exact Submonoid.one_mem _
  · exact Submonoid.mul_mem _ (R_mat410_mem_unitaryGroup M t) (D_mat410_mem_unitaryGroup M t)

/-! ### Section 3: Transducer action of `U_op410` on coupled vectors `aVec, bVec` -/

noncomputable def vecW (M : ℕ) (v : Fin (M + 1) → ℝ) : EuclideanSpace ℂ (Qubits (qW M)) :=
  ∑ c : Fin (M + 1), (v c : ℂ) • ket (modeKet M (c.1 + 1))

private lemma hadamard_ket_false_true :
    act hadamard (ket false) = ((Real.sqrt 2)⁻¹ : ℂ) • ket false + ((Real.sqrt 2)⁻¹ : ℂ) • ket true ∧
    act hadamard (ket true) = ((Real.sqrt 2)⁻¹ : ℂ) • ket false - ((Real.sqrt 2)⁻¹ : ℂ) • ket true := by
  constructor
  · ext b; cases b <;> simp [act, hadamard, ket]
  · ext b; cases b <;> simp [act, hadamard, ket, sub_eq_add_neg]

private lemma twoLevel_hadamard_comb (M j : ℕ) (hj : j < M) (u v : ℂ) :
    let H12 := twoLevelMat (modeKet M 1) (modeKet M (2 + j))
      (modeKet_ne M 1 (2 + j) (by omega) (by omega) (by omega)) hadamard
    act H12 (u • ket (modeKet M 1) + v • ket (modeKet M (2 + j))) =
      ((u + v) / Real.sqrt 2) • ket (modeKet M 1) +
        ((u - v) / Real.sqrt 2) • ket (modeKet M (2 + j)) := by
  intro H12
  rw [act_add, act_smul, act_smul, act_twoLevelMat_ket_left, act_twoLevelMat_ket_right]
  simp only [hadamard, Matrix.of_apply, Bool.false_and, Bool.true_and, Bool.and_self,
    Bool.false_eq_true, ↓reduceIte]
  have hs : ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) = 1 / (Real.sqrt 2 : ℂ) := by
    rw [inv_eq_one_div]
  simp_rw [hs]
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  have hr1 : u * (1 / (Real.sqrt 2 : ℂ)) + v * (1 / (Real.sqrt 2 : ℂ)) = (u + v) / (Real.sqrt 2 : ℂ) := by ring
  have hr2 : u * (1 / (Real.sqrt 2 : ℂ)) + v * -(1 / (Real.sqrt 2 : ℂ)) = (u - v) / (Real.sqrt 2 : ℂ) := by ring
  calc (u * (1 / (Real.sqrt 2 : ℂ))) • ket (modeKet M 1) + (u * (1 / (Real.sqrt 2 : ℂ))) • ket (modeKet M (2 + j)) +
        ((v * (1 / (Real.sqrt 2 : ℂ))) • ket (modeKet M 1) + (v * -(1 / (Real.sqrt 2 : ℂ))) • ket (modeKet M (2 + j)))
      = (u * (1 / (Real.sqrt 2 : ℂ)) + v * (1 / (Real.sqrt 2 : ℂ))) • ket (modeKet M 1) +
        (u * (1 / (Real.sqrt 2 : ℂ)) + v * -(1 / (Real.sqrt 2 : ℂ))) • ket (modeKet M (2 + j)) := by
          simp only [add_smul]; abel
    _ = ((u + v) / (Real.sqrt 2 : ℂ)) • ket (modeKet M 1) +
        ((u - v) / (Real.sqrt 2 : ℂ)) • ket (modeKet M (2 + j)) := by rw [hr1, hr2]

private lemma aVec_zero_eq (M m : ℕ) :
    aVec M m 0 0 = 0 ∧ bVec M m 0 0 = 1 ∧
      ∀ j : Fin M,
        (-1 : ℝ) ^ (j.1 + 1) * aVec M m 0 j.succ = bVec M m 0 j.succ := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp [aVec, pVecPoly, qVecPoly, PPoly_eval_zero, QPoly_eval_zero]
  · simp only [bVec, Fin.val_zero, pow_zero, one_mul, Nat.cast_zero, pVecPoly, qVecPoly,
      Fin.cases_zero, PPoly_eval_zero, QPoly_eval_zero]
    field_simp [hs]
    linarith
  · intro j
    simp only [aVec, bVec, Fin.val_zero, pow_zero, one_mul, Nat.cast_zero, pVecPoly, qVecPoly,
      Fin.cases_succ]
    by_cases hjlt : (j : ℕ) < m
    · have hne : (j : ℕ) ≠ m := Nat.ne_of_lt hjlt
      by_cases hjev : Even (j : ℕ) <;> simp [hjlt, hne, hjev, CPoly_eval_zero]
    · by_cases hjeq : (j : ℕ) = m
      · by_cases hjev : Even (j : ℕ)
        · have hm_ev : Even m := hjeq ▸ hjev
          have hm_pow : (-1 : ℝ) ^ (m + 1) = -1 := by
            rcases hm_ev with ⟨k, hk⟩
            rw [hk, ← two_mul, pow_add, pow_mul]
            norm_num
          simp [hjeq, hm_ev, hm_pow]
          ring
        · have hm_odd : Odd m := Nat.not_even_iff_odd.mp (hjeq ▸ hjev)
          have hm_not_ev : ¬ Even m := hjeq ▸ hjev
          have hm_pow : (-1 : ℝ) ^ (m + 1) = 1 := by
            rcases hm_odd with ⟨k, hk⟩
            rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) from by omega, pow_mul]
            norm_num
          simp [hjeq, hm_not_ev, hm_pow]
      · simp [hjlt, hjeq]

lemma act_U_op410_zero {M m : ℕ} (hmM : m ≤ M) :
    act (U_op410 M 0) (ket (modeKet M 0) + vecW M (aVec M m 0)) = vecW M (bVec M m 0) := by
  have _ := hmM
  have ⟨ha0, hb0, haj⟩ := aVec_zero_eq M m
  have hD_0 : act (D_mat410 M 0) (ket (modeKet M 0)) = ket (modeKet M 0) := by
    rw [act_D_mat410_ket]
    have hbit0 : bitsToNatLSB (modeKet M 0) = 0 := bitsToNatLSB_modeKet M 0 (by omega)
    simp [diagSign410, hbit0]
  have hD_w : act (D_mat410 M 0) (vecW M (aVec M m 0)) =
      ∑ j : Fin M, (bVec M m 0 j.succ : ℂ) • ket (modeKet M (2 + j.1)) := by
    unfold vecW
    rw [Fin.sum_univ_succ, ha0, Complex.ofReal_zero, zero_smul, zero_add, act_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [act_smul, act_D_mat410_ket, smul_smul]
    have hj_nat : bitsToNatLSB (modeKet M (j.succ.1 + 1)) = 2 + j.1 := by
      rw [bitsToNatLSB_modeKet M (j.succ.1 + 1) (by have := j.isLt; simp only [Fin.val_succ]; omega)]
      simp only [Fin.val_succ]
      omega
    have hj_gt : ¬ 2 + j.1 ≤ 1 := by omega
    have hdiag : diagSign410 M 0 (modeKet M (j.succ.1 + 1)) = (-1 : ℂ) ^ (j.1 + 1) := by
      simp only [diagSign410, ↓reduceIte, hj_nat, hj_gt]
      rw [show 2 + j.1 + 1 = (j.1 + 1) + 2 from by omega, pow_add]
      norm_num
    rw [hdiag]
    have hcoef : (aVec M m 0 j.succ : ℂ) * (-1 : ℂ) ^ (j.1 + 1) = (bVec M m 0 j.succ : ℂ) := by
      have hr : (-1 : ℝ) ^ (j.1 + 1) * aVec M m 0 j.succ = bVec M m 0 j.succ := haj j
      exact_mod_cast (by linarith [mul_comm ((-1 : ℝ) ^ (j.1 + 1)) (aVec M m 0 j.succ)] :
        aVec M m 0 j.succ * (-1 : ℝ) ^ (j.1 + 1) = bVec M m 0 j.succ)
    rw [hcoef]
    have hid : j.succ.1 + 1 = 2 + j.1 := by simp; omega
    rw [hid]
  have hU0 : U_op410 M 0 = R_mat410 M 0 * D_mat410 M 0 := by
    simp [U_op410]
  rw [hU0, act_mul, act_add, hD_0, hD_w, act_add, act_sum]
  have hR_0 : act (R_mat410 M 0) (ket (modeKet M 0)) = ket (modeKet M 1) := by
    simp only [R_mat410, ↓reduceIte]
    rw [act_twoLevelMat_ket_left]
    simp [pauliX]
  have hR_j : ∀ j : Fin M,
      act (R_mat410 M 0) ((bVec M m 0 j.succ : ℂ) • ket (modeKet M (2 + j.1))) =
        (bVec M m 0 j.succ : ℂ) • ket (modeKet M (2 + j.1)) := by
    intro j
    rw [act_smul]
    congr 1
    simp only [R_mat410, ↓reduceIte]
    exact act_twoLevelMat_ket_other (modeKet M 0) (modeKet M 1) (modeKet M (2 + j.1))
      _ (modeKet_ne M (2 + j.1) 0 (by omega) (by omega) (by omega))
      (modeKet_ne M (2 + j.1) 1 (by omega) (by omega) (by omega)) pauliX
  rw [hR_0, Finset.sum_congr rfl fun j _ => hR_j j]
  unfold vecW
  rw [Fin.sum_univ_succ, hb0, Complex.ofReal_one, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hid : j.succ.1 + 1 = 2 + j.1 := by simp; omega
  rw [hid]

private lemma mod4_of_even_half {t h : ℕ} (ht : t = 2 * h ∨ t = 2 * h + 1) (hh : Even h) :
    t % 4 = 0 ∨ t % 4 = 1 := by
  rcases hh with ⟨k, rfl⟩
  omega

private lemma mod4_of_odd_half {t h : ℕ} (ht : t = 2 * h ∨ t = 2 * h + 1) (hh : Odd h) :
    t % 4 = 2 ∨ t % 4 = 3 := by
  rcases hh with ⟨k, rfl⟩
  omega

private lemma diag_interior_star_coeff {M m : ℕ} (t : Fin (2 * m + 2)) (ht1 : 1 ≤ t.1) (ht2 : t.1 ≤ 2 * m) :
    (-1 : ℝ) ^ (t.1 / 2) * aVec M m t 0 = bVec M m t 0 := by
  have ht_decomp : t.1 = 2 * (t.1 / 2) ∨ t.1 = 2 * (t.1 / 2) + 1 := by omega
  rcases Nat.even_or_odd (t.1 / 2) with hh | hh
  · have hmod := mod4_of_even_half ht_decomp hh
    have hp0 : (PPoly m).eval (t.1 : ℝ) = 0 :=
      PPoly_eval_root (by simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨ht1, ht2⟩, hmod⟩)
    have hpow : (-1 : ℝ) ^ (t.1 / 2) = 1 := by rcases hh with ⟨k, hk⟩; rw [hk, ← two_mul, pow_mul]; norm_num
    simp [aVec, bVec, pVecPoly, qVecPoly, hp0, hpow]
  · have hmod := mod4_of_odd_half ht_decomp hh
    have hq0 : (QPoly m).eval (t.1 : ℝ) = 0 :=
      QPoly_eval_root (by simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨ht1, ht2⟩, hmod⟩)
    have hpow : (-1 : ℝ) ^ (t.1 / 2) = -1 := by rcases hh with ⟨k, hk⟩; rw [hk, pow_add, pow_mul]; norm_num
    simp [aVec, bVec, pVecPoly, qVecPoly, hq0, hpow]
    ring

private lemma diag_le_top_coord_coeff {M m : ℕ} (t : Fin (2 * m + 2)) (ht1 : 1 ≤ t.1) (_ht2 : t.1 ≤ 2 * m + 1)
    (i : Fin M) (hi_eq : i.1 = m → t.1 ≤ 2 * m) :
    (-1 : ℝ) ^ min i.1 (t.1 / 2) * aVec M m t i.succ = bVec M m t i.succ := by
  let h := t.1 / 2
  have ht_decomp : t.1 = 2 * h ∨ t.1 = 2 * h + 1 := by dsimp [h]; omega
  by_cases him : (i : ℕ) < m
  · by_cases hi_ev : Even (i : ℕ)
    · have hp : (pVecPoly M m i.succ).eval (t.1 : ℝ) = 0 := by
        simp [pVecPoly, Fin.cases_succ, him, hi_ev, Nat.not_odd_iff_even.mpr hi_ev, Nat.ne_of_lt him]
      have ha_eq_b : aVec M m t i.succ = bVec M m t i.succ := by
        simp [aVec, bVec, hp]
      rw [ha_eq_b]
      by_cases hih : i.1 ≤ h
      · have hmin : min i.1 h = i.1 := Nat.min_eq_left hih
        have hpow : (-1 : ℝ) ^ i.1 = 1 := by
          rcases hi_ev with ⟨k, hk⟩; rw [hk, ← two_mul, pow_mul]; norm_num
        change (-1 : ℝ) ^ min i.1 h * bVec M m t i.succ = bVec M m t i.succ
        rw [hmin, hpow, one_mul]
      · have hhi : h < i.1 := Nat.lt_of_not_ge hih
        have hmin : min i.1 h = h := Nat.min_eq_right hhi.le
        rcases Nat.even_or_odd h with hh | hh
        · have hpow : (-1 : ℝ) ^ h = 1 := by
            rcases hh with ⟨k, hk⟩; rw [hk, ← two_mul, pow_mul]; norm_num
          change (-1 : ℝ) ^ min i.1 h * bVec M m t i.succ = bVec M m t i.succ
          rw [hmin, hpow, one_mul]
        · have ht_lt : t.1 < 2 * i.1 + 2 := by dsimp [h] at hhi; omega
          have hmod := mod4_of_odd_half ht_decomp hh
          have hq0 : (QPoly m).eval (t.1 : ℝ) = 0 :=
            QPoly_eval_root (by simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨ht1, by omega⟩, hmod⟩)
          have hC0 : (CPoly i.1 m).eval (t.1 : ℝ) = 0 := by
            rw [CPoly_eval_root_of_ne him (by omega), if_pos hi_ev, hq0, mul_zero]
          have hbv : bVec M m t i.succ = 0 := by
            simp [bVec, hp, qVecPoly, Fin.cases_succ, him, hi_ev, hC0]
          rw [hbv, mul_zero]
    · have hi_odd : Odd (i : ℕ) := Nat.not_even_iff_odd.mp hi_ev
      have hq : (qVecPoly M m i.succ).eval (t.1 : ℝ) = 0 := by
        simp [qVecPoly, Fin.cases_succ, him, hi_ev, Nat.ne_of_lt him]
      have ha_eq_neg_b : aVec M m t i.succ = -(bVec M m t i.succ) := by
        simp [aVec, bVec, hq]; ring
      by_cases hih : i.1 ≤ h
      · have hmin : min i.1 h = i.1 := Nat.min_eq_left hih
        have hpow : (-1 : ℝ) ^ i.1 = -1 := by
          rcases hi_odd with ⟨k, hk⟩; rw [hk, pow_add, pow_mul]; norm_num
        change (-1 : ℝ) ^ min i.1 h * aVec M m t i.succ = bVec M m t i.succ
        rw [hmin, hpow, ha_eq_neg_b]
        ring
      · have hhi : h < i.1 := Nat.lt_of_not_ge hih
        have hmin : min i.1 h = h := Nat.min_eq_right hhi.le
        rcases Nat.even_or_odd h with hh | hh
        · have ht_lt : t.1 < 2 * i.1 + 2 := by dsimp [h] at hhi; omega
          have hmod := mod4_of_even_half ht_decomp hh
          have hp0 : (PPoly m).eval (t.1 : ℝ) = 0 :=
            PPoly_eval_root (by simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨ht1, by omega⟩, hmod⟩)
          have hC0 : (CPoly i.1 m).eval (t.1 : ℝ) = 0 := by
            rw [CPoly_eval_root_of_ne him (by omega), if_neg hi_ev, hp0, mul_zero]
          have hbv : bVec M m t i.succ = 0 := by
            simp [bVec, hq, pVecPoly, Fin.cases_succ, him, hi_odd, Polynomial.eval_mul, hC0]
          rw [ha_eq_neg_b, hbv, neg_zero, mul_zero]
        · have hpow : (-1 : ℝ) ^ h = -1 := by
            rcases hh with ⟨k, hk⟩; rw [hk, pow_add, pow_mul]; norm_num
          change (-1 : ℝ) ^ min i.1 h * aVec M m t i.succ = bVec M m t i.succ
          rw [hmin, hpow, ha_eq_neg_b]
          ring
  · by_cases hieq : (i : ℕ) = m
    · have ht2m : t.1 ≤ 2 * m := hi_eq hieq
      have hhm : h ≤ m := by dsimp [h]; omega
      have hmin : min i.1 h = h := by rw [hieq]; exact Nat.min_eq_right hhm
      change (-1 : ℝ) ^ min i.1 h * aVec M m t i.succ = bVec M m t i.succ
      rw [hmin]
      by_cases hm_ev : Even m
      · have hp : (pVecPoly M m i.succ).eval (t.1 : ℝ) = (PPoly m).eval (t.1 : ℝ) := by
          simp [pVecPoly, Fin.cases_succ, hieq, hm_ev]
        have hq : (qVecPoly M m i.succ).eval (t.1 : ℝ) = 0 := by
          simp [qVecPoly, Fin.cases_succ, hieq, hm_ev, Nat.not_odd_iff_even.mpr hm_ev]
        rcases Nat.even_or_odd h with hh | hh
        · have hmod := mod4_of_even_half ht_decomp hh
          have hp0 : (PPoly m).eval (t.1 : ℝ) = 0 :=
            PPoly_eval_root (by simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨ht1, ht2m⟩, hmod⟩)
          simp [aVec, bVec, hp, hq, hp0]
        · have hpow : (-1 : ℝ) ^ h = -1 := by
            rcases hh with ⟨k, hk⟩; rw [hk, pow_add, pow_mul]; norm_num
          simp [aVec, bVec, hp, hq, hpow]
          ring
      · have hm_odd : Odd m := Nat.not_even_iff_odd.mp hm_ev
        have hp : (pVecPoly M m i.succ).eval (t.1 : ℝ) = 0 := by
          simp [pVecPoly, Fin.cases_succ, hieq, hm_ev]
        have hq : (qVecPoly M m i.succ).eval (t.1 : ℝ) = (QPoly m).eval (t.1 : ℝ) := by
          simp [qVecPoly, Fin.cases_succ, hieq, hm_ev, hm_odd]
        rcases Nat.even_or_odd h with hh | hh
        · have hpow : (-1 : ℝ) ^ h = 1 := by
            rcases hh with ⟨k, hk⟩; rw [hk, ← two_mul, pow_mul]; norm_num
          simp [aVec, bVec, hp, hq, hpow]
        · have hmod := mod4_of_odd_half ht_decomp hh
          have hq0 : (QPoly m).eval (t.1 : ℝ) = 0 :=
            QPoly_eval_root (by simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨ht1, ht2m⟩, hmod⟩)
          simp [aVec, bVec, hp, hq, hq0]
    · have hp : (pVecPoly M m i.succ).eval (t.1 : ℝ) = 0 := by
        simp [pVecPoly, Fin.cases_succ, (by omega : ¬ (i : ℕ) < m), hieq]
      have hq : (qVecPoly M m i.succ).eval (t.1 : ℝ) = 0 := by
        simp [qVecPoly, Fin.cases_succ, (by omega : ¬ (i : ℕ) < m), hieq]
      simp [aVec, bVec, hp, hq]

private lemma act_D_mat410_vecW_top_or_int {M m : ℕ} (t : Fin (2 * m + 2)) (ht1 : 1 ≤ t.1) :
    act (D_mat410 M t.1) (vecW M (aVec M m t)) =
      ((-1 : ℂ) ^ (t.1 / 2) * (aVec M m t 0 : ℂ)) • ket (modeKet M 1) +
        ∑ j : Fin M, ((-1 : ℂ) ^ min j.1 (t.1 / 2) * (aVec M m t j.succ : ℂ)) • ket (modeKet M (2 + j.1)) := by
  unfold vecW
  rw [Fin.sum_univ_succ, act_add, act_smul, act_D_mat410_ket, act_sum]
  simp only [Fin.val_zero, zero_add]
  have ht0 : t.1 ≠ 0 := by omega
  have hbit1 : bitsToNatLSB (modeKet M 1) = 1 := bitsToNatLSB_modeKet M 1 (by omega)
  have hdiag1 : diagSign410 M t.1 (modeKet M 1) = (-1 : ℂ) ^ (t.1 / 2) := by
    simp [diagSign410, ht0, hbit1]
  rw [hdiag1, smul_smul, mul_comm (aVec M m t 0 : ℂ)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [act_smul, act_D_mat410_ket, smul_smul]
  have hidx : j.succ.1 + 1 = 2 + j.1 := by simp only [Fin.val_succ]; omega
  rw [hidx]
  have hbitj : bitsToNatLSB (modeKet M (2 + j.1)) = 2 + j.1 :=
    bitsToNatLSB_modeKet M (2 + j.1) (by omega)
  have hj1 : 2 + j.1 ≠ 1 := by omega
  have hdiagj : diagSign410 M t.1 (modeKet M (2 + j.1)) = (-1 : ℂ) ^ min j.1 (t.1 / 2) := by
    simp [diagSign410, ht0, hbitj, hj1]
  rw [hdiagj, mul_comm (aVec M m t j.succ : ℂ)]

private lemma bVec_antisymm_interior {M m : ℕ} (hmM : m ≤ M) {j : ℕ} (hjm : j < m) :
    bVec M m ⟨2 * j + 1, by omega⟩ ⟨j + 1, by omega⟩ =
      -bVec M m ⟨2 * j + 1, by omega⟩ 0 := by
  have hjM : j < M := lt_of_lt_of_le hjm hmM
  let t : Fin (2 * m + 2) := ⟨2 * j + 1, by omega⟩
  have hpow : (-1 : ℝ) ^ (2 * j + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
  have hpt_odd : ∀ hm : Even j, (PPoly m).eval ((2 * j + 1 : ℕ) : ℝ) = 0 := fun hj => by
    apply PPoly_eval_root
    simp only [rootSetP, Finset.mem_filter, Finset.mem_Icc]
    rcases hj with ⟨k, rfl⟩
    omega
  have hqt_odd : ∀ hm : ¬ Even j, (QPoly m).eval ((2 * j + 1 : ℕ) : ℝ) = 0 := fun hj => by
    apply QPoly_eval_root
    simp only [rootSetQ, Finset.mem_filter, Finset.mem_Icc]
    rcases Nat.not_even_iff_odd.mp hj with ⟨k, hk⟩
    omega
  change bVec M m ⟨2 * j + 1, by omega⟩ (⟨j, hjM⟩ : Fin M).succ = -bVec M m ⟨2 * j + 1, by omega⟩ 0
  unfold bVec pVecPoly qVecPoly
  simp only [Fin.cases_succ, Fin.cases_zero]
  have hne : j ≠ m := Nat.ne_of_lt hjm
  have hCp := CPoly_eval_endpoint hjm
  rw [hpow]
  by_cases hj : Even j
  · have hp0 := hpt_odd hj
    simp only [hj, ↓reduceIte] at hCp
    have hpj : (if j < m ∧ ¬ Even j then Polynomial.C (1 / ((2 * j + 1 : ℕ) : ℝ)) * CPoly j m
        else if j = m ∧ Even j then PPoly m else 0).eval ((2 * j + 1 : ℕ) : ℝ) = 0 := by
      simp [hjm, hne, hj]
    have hqj : (if j < m ∧ Even j then Polynomial.C (1 / ((2 * j + 1 : ℕ) : ℝ)) * CPoly j m
        else if j = m ∧ ¬ Even j then QPoly m else 0).eval ((2 * j + 1 : ℕ) : ℝ) =
        -((QPoly m).eval ((2 * j + 1 : ℕ) : ℝ)) := by
      simp only [hjm, hj, and_self, ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_C]
      calc (1 / ((2 * j + 1 : ℕ) : ℝ)) * (CPoly j m).eval ((2 * j + 1 : ℕ) : ℝ)
          = (CPoly j m).eval ((2 * j + 1 : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ) := by ring
        _ = -((QPoly m).eval ((2 * j + 1 : ℕ) : ℝ)) := hCp
    rw [hpj, hqj, hp0]
    ring
  · have hq0 := hqt_odd hj
    simp only [hj, ↓reduceIte] at hCp
    have hpj : (if j < m ∧ ¬ Even j then Polynomial.C (1 / ((2 * j + 1 : ℕ) : ℝ)) * CPoly j m
        else if j = m ∧ Even j then PPoly m else 0).eval ((2 * j + 1 : ℕ) : ℝ) =
        -((PPoly m).eval ((2 * j + 1 : ℕ) : ℝ)) := by
      simp only [hjm, hj, not_false_eq_true, and_self, ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_C]
      calc (1 / ((2 * j + 1 : ℕ) : ℝ)) * (CPoly j m).eval ((2 * j + 1 : ℕ) : ℝ)
          = (CPoly j m).eval ((2 * j + 1 : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ) := by ring
        _ = -((PPoly m).eval ((2 * j + 1 : ℕ) : ℝ)) := hCp
    have hqj : (if j < m ∧ Even j then Polynomial.C (1 / ((2 * j + 1 : ℕ) : ℝ)) * CPoly j m
        else if j = m ∧ ¬ Even j then QPoly m else 0).eval ((2 * j + 1 : ℕ) : ℝ) = 0 := by
      simp [hjm, hne, hj]
    rw [hpj, hqj, hq0]
    ring

lemma act_U_op410_interior {M m : ℕ} (hmM : m ≤ M) (t : Fin (2 * m + 2))
    (ht1 : 1 ≤ t.1) (ht2 : t.1 ≤ 2 * m) :
    act (U_op410 M t.1) (vecW M (aVec M m t)) = vecW M (bVec M m t) := by
  have hle_top : ¬ 2 * M + 1 < t.1 := by omega
  rw [U_op410, if_neg hle_top, act_mul, act_D_mat410_vecW_top_or_int t ht1]
  have hD_b : ((-1 : ℂ) ^ (t.1 / 2) * (aVec M m t 0 : ℂ)) • ket (modeKet M 1) +
        ∑ j : Fin M, ((-1 : ℂ) ^ min j.1 (t.1 / 2) * (aVec M m t j.succ : ℂ)) • ket (modeKet M (2 + j.1)) =
      vecW M (bVec M m t) := by
    have h0 : (-1 : ℂ) ^ (t.1 / 2) * (aVec M m t 0 : ℂ) = (bVec M m t 0 : ℂ) := by
      exact_mod_cast diag_interior_star_coeff t ht1 ht2
    have hj : ∀ j : Fin M,
        (-1 : ℂ) ^ min j.1 (t.1 / 2) * (aVec M m t j.succ : ℂ) = (bVec M m t j.succ : ℂ) := fun j => by
      exact_mod_cast diag_le_top_coord_coeff t ht1 (by omega) j (fun _ => ht2)
    rw [h0]
    unfold vecW
    rw [Fin.sum_univ_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hidx : j.succ.1 + 1 = 2 + j.1 := by simp; omega
    rw [hj j, hidx]
  rw [hD_b]
  have ht0 : t.1 ≠ 0 := by omega
  by_cases hodd : Odd t.1
  · let j := t.1 / 2
    have hj_def : t.1 = 2 * j + 1 := by
      rcases hodd with ⟨k, hk⟩
      dsimp [j]
      omega
    have hjm : j < m := by omega
    have hjM : j < M := lt_of_lt_of_le hjm hmM
    let jFin : Fin M := ⟨j, hjM⟩
    let H12 := twoLevelMat (modeKet M 1) (modeKet M (2 + j))
      (modeKet_ne M 1 (2 + j) (by omega) (by omega) (by omega)) hadamard
    let R01 := twoLevelMat (modeKet M 0) (modeKet M 1)
      (modeKet_ne M 0 1 (by omega) (by omega) (by omega)) (R2J j)
    have hR : R_mat410 M t.1 = H12 * R01 * H12 := by
      unfold R_mat410
      rw [if_neg ht0, dif_pos ⟨hodd, hjM⟩]
    rw [hR]
    have hvec_split : vecW M (bVec M m t) =
        ((bVec M m t 0 : ℂ) • ket (modeKet M 1) +
          (bVec M m t jFin.succ : ℂ) • ket (modeKet M (2 + j))) +
        ∑ i ∈ Finset.univ.erase jFin, (bVec M m t i.succ : ℂ) • ket (modeKet M (2 + i.1)) := by
      unfold vecW
      rw [Fin.sum_univ_succ, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ jFin)]
      simp only [Fin.val_zero, zero_add]
      have hidx : jFin.succ.1 + 1 = 2 + j := by simp only [Fin.val_succ, jFin]; omega
      rw [hidx]
      have hsum_idx : ∑ i ∈ Finset.univ.erase jFin, (bVec M m t i.succ : ℂ) • ket (modeKet M (i.succ.1 + 1)) =
          ∑ i ∈ Finset.univ.erase jFin, (bVec M m t i.succ : ℂ) • ket (modeKet M (2 + i.1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hid : i.succ.1 + 1 = 2 + i.1 := by simp only [Fin.val_succ]; omega
        rw [hid]
      rw [hsum_idx]
      abel
    have hanti : bVec M m t jFin.succ = -bVec M m t 0 := by
      have ht_eq : t = ⟨2 * j + 1, by omega⟩ := Fin.ext hj_def
      have hj_eq : jFin.succ = ⟨j + 1, by omega⟩ := Fin.ext (by simp [jFin])
      rw [ht_eq, hj_eq]
      exact bVec_antisymm_interior hmM hjm
    have hantiC : (bVec M m t jFin.succ : ℂ) = -(bVec M m t 0 : ℂ) := by
      exact_mod_cast hanti
    have hH_pair : act H12 ((bVec M m t 0 : ℂ) • ket (modeKet M 1) +
          (bVec M m t jFin.succ : ℂ) • ket (modeKet M (2 + j))) =
        ((bVec M m t 0 : ℂ) * Real.sqrt 2) • ket (modeKet M (2 + j)) := by
      rw [twoLevel_hadamard_comb M j hjM, hantiC]
      have hadd0 : ((bVec M m t 0 : ℂ) + -(bVec M m t 0 : ℂ)) / Real.sqrt 2 = 0 := by ring
      have hsne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt 2 ≠ 0)
      have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
      have hsub : ((bVec M m t 0 : ℂ) - -(bVec M m t 0 : ℂ)) / Real.sqrt 2 =
          (bVec M m t 0 : ℂ) * Real.sqrt 2 := by
        field_simp [hsne]; rw [hsq]; ring
      rw [hadd0, zero_smul, zero_add, hsub]
    have hR01_pair : act R01 (((bVec M m t 0 : ℂ) * Real.sqrt 2) • ket (modeKet M (2 + j))) =
        ((bVec M m t 0 : ℂ) * Real.sqrt 2) • ket (modeKet M (2 + j)) := by
      rw [act_smul]
      congr 1
      exact act_twoLevelMat_ket_other (modeKet M 0) (modeKet M 1) (modeKet M (2 + j))
        _ (modeKet_ne M (2 + j) 0 (by omega) (by omega) (by omega))
        (modeKet_ne M (2 + j) 1 (by omega) (by omega) (by omega)) (R2J j)
    have hH_pair_back : act H12 (((bVec M m t 0 : ℂ) * Real.sqrt 2) • ket (modeKet M (2 + j))) =
        (bVec M m t 0 : ℂ) • ket (modeKet M 1) +
          (bVec M m t jFin.succ : ℂ) • ket (modeKet M (2 + j)) := by
      have h0 := twoLevel_hadamard_comb M j hjM 0 ((bVec M m t 0 : ℂ) * Real.sqrt 2)
      rw [zero_smul, zero_add] at h0
      rw [h0, hantiC]
      have hsne : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : Real.sqrt 2 ≠ 0)
      have hc1 : (0 + (bVec M m t 0 : ℂ) * Real.sqrt 2) / Real.sqrt 2 = (bVec M m t 0 : ℂ) := by
        field_simp [hsne]; ring
      have hc2 : (0 - (bVec M m t 0 : ℂ) * Real.sqrt 2) / Real.sqrt 2 = -(bVec M m t 0 : ℂ) := by
        field_simp [hsne]; ring
      rw [hc1, hc2]
    have hfix_other : ∀ (U : Matrix (Qubits (qW M)) (Qubits (qW M)) ℂ)
        (hfix : ∀ i ∈ Finset.univ.erase jFin, act U (ket (modeKet M (2 + i.1))) = ket (modeKet M (2 + i.1))),
        act U (∑ i ∈ Finset.univ.erase jFin, (bVec M m t i.succ : ℂ) • ket (modeKet M (2 + i.1))) =
          ∑ i ∈ Finset.univ.erase jFin, (bVec M m t i.succ : ℂ) • ket (modeKet M (2 + i.1)) := by
      intro U hfix
      rw [act_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [act_smul, hfix i hi]
    have hH12_fix : ∀ i ∈ Finset.univ.erase jFin, act H12 (ket (modeKet M (2 + i.1))) = ket (modeKet M (2 + i.1)) := by
      intro i hi
      have hine : i ≠ jFin := (Finset.mem_erase.mp hi).1
      have hne_nat : 2 + i.1 ≠ 2 + j := fun h => hine (Fin.ext (by simp [jFin]; omega))
      exact act_twoLevelMat_ket_other (modeKet M 1) (modeKet M (2 + j)) (modeKet M (2 + i.1))
        _ (modeKet_ne M (2 + i.1) 1 (by omega) (by omega) (by omega))
        (modeKet_ne M (2 + i.1) (2 + j) (by omega) (by omega) hne_nat) hadamard
    have hR01_fix : ∀ i ∈ Finset.univ.erase jFin, act R01 (ket (modeKet M (2 + i.1))) = ket (modeKet M (2 + i.1)) := by
      intro i _
      exact act_twoLevelMat_ket_other (modeKet M 0) (modeKet M 1) (modeKet M (2 + i.1))
        _ (modeKet_ne M (2 + i.1) 0 (by omega) (by omega) (by omega))
        (modeKet_ne M (2 + i.1) 1 (by omega) (by omega) (by omega)) (R2J j)
    rw [hvec_split, act_mul, act_mul, act_add, hH_pair, hfix_other H12 hH12_fix,
      act_add, hR01_pair, hfix_other R01 hR01_fix, act_add, hH_pair_back, hfix_other H12 hH12_fix,
      ← hvec_split]
  · have htop : ¬ (1 ≤ M ∧ t.1 = 2 * M + 1) := by intro h; omega
    have hR : R_mat410 M t.1 = 1 := by
      simp [R_mat410, ht0, hodd, htop]
    rw [hR, act_one_vec]

lemma act_U_op410_top {M m : ℕ} (hM : 1 ≤ M) (hmM : m ≤ M) :
    act (U_op410 M (2 * m + 1)) (vecW M (aVec M m ⟨2 * m + 1, by omega⟩)) =
      ket (modeKet M 0) + vecW M (bVec M m ⟨2 * m + 1, by omega⟩) := by
  let t : Fin (2 * m + 2) := ⟨2 * m + 1, by omega⟩
  have ht1 : 1 ≤ t.1 := by dsimp [t]; omega
  have ht2 : t.1 ≤ 2 * m + 1 := by dsimp [t]; omega
  have hle_top : ¬ 2 * M + 1 < t.1 := by dsimp [t]; omega
  change act (U_op410 M t.1) (vecW M (aVec M m t)) = ket (modeKet M 0) + vecW M (bVec M m t)
  rw [U_op410, if_neg hle_top, act_mul, act_D_mat410_vecW_top_or_int t ht1]
  have hj_eq : ∀ j : Fin M, j.1 ≠ m →
      (-1 : ℂ) ^ min j.1 (t.1 / 2) * (aVec M m t j.succ : ℂ) = (bVec M m t j.succ : ℂ) := fun j hne => by
    exact_mod_cast diag_le_top_coord_coeff t ht1 ht2 j (fun he => absurd he hne)
  have hpow_t : (-1 : ℝ) ^ t.1 = -1 := by
    change (-1 : ℝ) ^ (2 * m + 1) = -1; rw [pow_add, pow_mul]; norm_num
  have hhalf : t.1 / 2 = m := by dsimp [t]; omega
  have hodd_t : Odd t.1 := ⟨m, rfl⟩
  have ht0 : t.1 ≠ 0 := by omega
  have hsne : Real.sqrt 2 ≠ 0 := by positivity
  have hsneC : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast hsne
  by_cases hm_lt : m < M
  · let mFin : Fin M := ⟨m, hm_lt⟩
    let H12 := twoLevelMat (modeKet M 1) (modeKet M (2 + m))
      (modeKet_ne M 1 (2 + m) (by omega) (by omega) (by omega)) hadamard
    let R01 := twoLevelMat (modeKet M 0) (modeKet M 1)
      (modeKet_ne M 0 1 (by omega) (by omega) (by omega)) (R2J m)
    have hR : R_mat410 M t.1 = H12 * R01 * H12 := by
      have hj_lt : t.1 / 2 < M := by rw [hhalf]; exact hm_lt
      have hH12_eq : ∀ h1, twoLevelMat (modeKet M 1) (modeKet M (2 + t.1 / 2)) h1 hadamard = H12 :=
        fun h1 => twoLevelMat_congr_right _ _ _ (congrArg (fun k => modeKet M (2 + k)) hhalf) h1 _ hadamard
      unfold R_mat410
      rw [if_neg ht0, dif_pos ⟨hodd_t, hj_lt⟩]
      dsimp only
      rw [hH12_eq, hhalf]
    have hsplit_after :
        ((-1 : ℂ) ^ (t.1 / 2) * (aVec M m t 0 : ℂ)) • ket (modeKet M 1) +
          ∑ j : Fin M, ((-1 : ℂ) ^ min j.1 (t.1 / 2) * (aVec M m t j.succ : ℂ)) • ket (modeKet M (2 + j.1)) =
        (((-1 : ℂ) ^ m * (aVec M m t 0 : ℂ)) • ket (modeKet M 1) +
          ((-1 : ℂ) ^ m * (aVec M m t mFin.succ : ℂ)) • ket (modeKet M (2 + m))) +
        ∑ j ∈ Finset.univ.erase mFin, (bVec M m t j.succ : ℂ) • ket (modeKet M (2 + j.1)) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ mFin)]
      have hmin_m : min mFin.1 (t.1 / 2) = m := by simp [mFin, hhalf]
      have hmFin_val : mFin.1 = m := rfl
      rw [hmin_m, hhalf, hmFin_val]
      have hrest : ∑ x ∈ Finset.univ.erase mFin,
            ((-1 : ℂ) ^ min x.1 m * (aVec M m t x.succ : ℂ)) • ket (modeKet M (2 + x.1)) =
          ∑ x ∈ Finset.univ.erase mFin, (bVec M m t x.succ : ℂ) • ket (modeKet M (2 + x.1)) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hne : x.1 ≠ m := fun h => (Finset.mem_erase.mp hx).1 (Fin.ext h)
        have hxeq := hj_eq x hne
        rw [hhalf] at hxeq
        rw [hxeq]
      rw [hrest]
      change (((-1 : ℂ) ^ m * (aVec M m t 0 : ℂ)) • ket (modeKet M 1)) +
          (((-1 : ℂ) ^ m * (aVec M m t mFin.succ : ℂ)) • ket (modeKet M (2 + m)) + _) = _
      abel
    have hPQ := PPoly_mul_QPoly_eval_top m
    set Pval : ℝ := (PPoly m).eval ((2 * m + 1 : ℕ) : ℝ)
    set Qval : ℝ := (QPoly m).eval ((2 * m + 1 : ℕ) : ℝ)
    have h2PQ : 2 * Pval * Qval = 1 := by
      calc 2 * Pval * Qval = 2 * (Pval * Qval) := mul_assoc _ _ _
        _ = 2 * (1 / 2) := by rw [hPQ]
        _ = 1 := by norm_num
    have ha_star : aVec M m t 0 = (-Qval - Pval) / Real.sqrt 2 := by
      simp [aVec, pVecPoly, qVecPoly, hpow_t, Pval, Qval, t]
    have hb_star : bVec M m t 0 = (Pval - Qval) / Real.sqrt 2 := by
      simp [bVec, pVecPoly, qVecPoly, hpow_t, Pval, Qval, t]; ring
    have hplus_A : ((-1 : ℝ) ^ m * aVec M m t 0 + (-1 : ℝ) ^ m * aVec M m t mFin.succ) / Real.sqrt 2 = AJ m ∧
        ((-1 : ℝ) ^ m * aVec M m t 0 - (-1 : ℝ) ^ m * aVec M m t mFin.succ) / Real.sqrt 2 =
          (bVec M m t 0 - bVec M m t mFin.succ) / Real.sqrt 2 ∧
        (bVec M m t 0 + bVec M m t mFin.succ) / Real.sqrt 2 = BJ m := by
      have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hrho_ne : rhoJ m ≠ 0 := rhoJ_ne_zero m
      by_cases hm_ev : Even m
      · have hpow_m : (-1 : ℝ) ^ m = 1 := by
          rcases hm_ev with ⟨k, rfl⟩; rw [← two_mul, pow_mul]; norm_num
        have ham : aVec M m t mFin.succ = -Pval / Real.sqrt 2 := by
          simp [aVec, pVecPoly, qVecPoly, Fin.cases_succ, show mFin.1 = m from rfl, hm_ev,
            Nat.not_odd_iff_even.mpr hm_ev, hpow_t, Pval, t]
        have hbm : bVec M m t mFin.succ = Pval / Real.sqrt 2 := by
          simp [bVec, pVecPoly, qVecPoly, Fin.cases_succ, show mFin.1 = m from rfl, hm_ev,
            Nat.not_odd_iff_even.mpr hm_ev, hpow_t, Pval, t]
        have hrho : rhoJ m = 2 * Pval := by simp [rhoJ, hm_ev, Pval]
        have hrho_Q : rhoJ m * Qval = 1 := by rw [hrho]; exact h2PQ
        have hrho_inv : (rhoJ m)⁻¹ = Qval := by
          calc (rhoJ m)⁻¹ = (rhoJ m)⁻¹ * 1 := (mul_one _).symm
            _ = (rhoJ m)⁻¹ * (rhoJ m * Qval) := by rw [hrho_Q]
            _ = ((rhoJ m)⁻¹ * rhoJ m) * Qval := (mul_assoc _ _ _).symm
            _ = 1 * Qval := by rw [inv_mul_cancel₀ hrho_ne]
            _ = Qval := one_mul _
        refine ⟨?_, ?_, ?_⟩
        · unfold AJ; rw [hrho_inv, hrho, ha_star, ham, hpow_m]
          field_simp [hsne]; rw [hsq]; ring
        · rw [ha_star, ham, hb_star, hbm, hpow_m]
          field_simp [hsne]; ring
        · unfold BJ; rw [hrho_inv, hrho, hb_star, hbm]
          field_simp [hsne]; rw [hsq]; ring
      · have hm_odd : Odd m := Nat.not_even_iff_odd.mp hm_ev
        have hpow_m : (-1 : ℝ) ^ m = -1 := by
          rcases hm_odd with ⟨k, rfl⟩; rw [pow_add, pow_mul]; norm_num
        have ham : aVec M m t mFin.succ = -Qval / Real.sqrt 2 := by
          simp [aVec, pVecPoly, qVecPoly, Fin.cases_succ, show mFin.1 = m from rfl, hm_ev, hm_odd,
            hpow_t, Qval, t]
        have hbm : bVec M m t mFin.succ = -Qval / Real.sqrt 2 := by
          simp [bVec, pVecPoly, qVecPoly, Fin.cases_succ, show mFin.1 = m from rfl, hm_ev, hm_odd,
            hpow_t, Qval, t]
        have hrho : rhoJ m = -2 * Qval := by simp [rhoJ, hm_ev, Qval]
        have hrho_P : rhoJ m * (-Pval) = 1 := by
          rw [hrho]
          calc -2 * Qval * -Pval = 2 * Pval * Qval := by ring
            _ = 1 := h2PQ
        have hrho_inv : (rhoJ m)⁻¹ = -Pval := by
          calc (rhoJ m)⁻¹ = (rhoJ m)⁻¹ * 1 := (mul_one _).symm
            _ = (rhoJ m)⁻¹ * (rhoJ m * (-Pval)) := by rw [hrho_P]
            _ = ((rhoJ m)⁻¹ * rhoJ m) * (-Pval) := (mul_assoc _ _ _).symm
            _ = 1 * (-Pval) := by rw [inv_mul_cancel₀ hrho_ne]
            _ = -Pval := one_mul _
        refine ⟨?_, ?_, ?_⟩
        · unfold AJ; rw [hrho_inv, hrho, ha_star, ham, hpow_m]
          field_simp [hsne]; rw [hsq]; ring
        · rw [ha_star, ham, hb_star, hbm, hpow_m]
          field_simp [hsne]; ring
        · unfold BJ; rw [hrho_inv, hrho, hb_star, hbm]
          field_simp [hsne]; rw [hsq]; ring
    have hH1 : act H12 (((-1 : ℂ) ^ m * (aVec M m t 0 : ℂ)) • ket (modeKet M 1) +
          ((-1 : ℂ) ^ m * (aVec M m t mFin.succ : ℂ)) • ket (modeKet M (2 + m))) =
        (AJ m : ℂ) • ket (modeKet M 1) +
          (((bVec M m t 0 : ℂ) - (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2) • ket (modeKet M (2 + m)) := by
      rw [twoLevel_hadamard_comb M m hm_lt]
      have e1 : (((-1 : ℂ) ^ m * (aVec M m t 0 : ℂ)) + ((-1 : ℂ) ^ m * (aVec M m t mFin.succ : ℂ))) / Real.sqrt 2 =
          (AJ m : ℂ) := by exact_mod_cast hplus_A.1
      have e2 : (((-1 : ℂ) ^ m * (aVec M m t 0 : ℂ)) - ((-1 : ℂ) ^ m * (aVec M m t mFin.succ : ℂ))) / Real.sqrt 2 =
          ((bVec M m t 0 : ℂ) - (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2 := by
        exact_mod_cast hplus_A.2.1
      rw [e1, e2]
    have hR01_act : act R01 ((AJ m : ℂ) • ket (modeKet M 1) +
          (((bVec M m t 0 : ℂ) - (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2) • ket (modeKet M (2 + m))) =
        ket (modeKet M 0) +
          ((BJ m : ℂ) • ket (modeKet M 1) +
            (((bVec M m t 0 : ℂ) - (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2) • ket (modeKet M (2 + m))) := by
      rw [act_add, act_smul, act_smul, act_twoLevelMat_ket_right,
        act_twoLevelMat_ket_other _ _ _ _
          (modeKet_ne M (2 + m) 0 (by omega) (by omega) (by omega))
          (modeKet_ne M (2 + m) 1 (by omega) (by omega) (by omega))]
      have hAne : (AJ m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (AJ_ne_zero m)
      have hc1 : (AJ m : ℂ) * R2J m false true = 1 := by
        simp only [R2J, Matrix.of_apply]
        norm_cast
        exact mul_div_cancel₀ _ (AJ_ne_zero m)
      have hc2 : (AJ m : ℂ) * R2J m true true = (BJ m : ℂ) := by
        simp only [R2J, Matrix.of_apply]
        norm_cast
        exact mul_div_cancel₀ _ (AJ_ne_zero m)
      rw [smul_add, smul_smul, smul_smul, hc1, hc2, one_smul]
      abel
    have hH2 : act H12 (ket (modeKet M 0) +
          ((BJ m : ℂ) • ket (modeKet M 1) +
            (((bVec M m t 0 : ℂ) - (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2) • ket (modeKet M (2 + m)))) =
        ket (modeKet M 0) +
          ((bVec M m t 0 : ℂ) • ket (modeKet M 1) +
            (bVec M m t mFin.succ : ℂ) • ket (modeKet M (2 + m))) := by
      rw [act_add, act_twoLevelMat_ket_other _ _ _ _
        (modeKet_ne M 0 1 (by omega) (by omega) (by omega))
        (modeKet_ne M 0 (2 + m) (by omega) (by omega) (by omega)),
        twoLevel_hadamard_comb M m hm_lt]
      have hB_eq : (BJ m : ℂ) = ((bVec M m t 0 : ℂ) + (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2 := by
        exact_mod_cast hplus_A.2.2.symm
      rw [hB_eq]
      have hsqC : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num)
      have ec1 : (((bVec M m t 0 : ℂ) + (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2 +
            ((bVec M m t 0 : ℂ) - (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2) / Real.sqrt 2 =
          (bVec M m t 0 : ℂ) := by
        field_simp [hsneC]; rw [hsqC]; ring
      have ec2 : (((bVec M m t 0 : ℂ) + (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2 -
            ((bVec M m t 0 : ℂ) - (bVec M m t mFin.succ : ℂ)) / Real.sqrt 2) / Real.sqrt 2 =
          (bVec M m t mFin.succ : ℂ) := by
        field_simp [hsneC]; rw [hsqC]; ring
      rw [ec1, ec2]
    have hfix_other : ∀ (U : Matrix (Qubits (qW M)) (Qubits (qW M)) ℂ)
        (hfix : ∀ j ∈ Finset.univ.erase mFin, act U (ket (modeKet M (2 + j.1))) = ket (modeKet M (2 + j.1))),
        act U (∑ j ∈ Finset.univ.erase mFin, (bVec M m t j.succ : ℂ) • ket (modeKet M (2 + j.1))) =
          ∑ j ∈ Finset.univ.erase mFin, (bVec M m t j.succ : ℂ) • ket (modeKet M (2 + j.1)) := by
      intro U hfix
      rw [act_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [act_smul, hfix j hj]
    have hH12_fix : ∀ j ∈ Finset.univ.erase mFin, act H12 (ket (modeKet M (2 + j.1))) = ket (modeKet M (2 + j.1)) := by
      intro j hj
      have hjne : j ≠ mFin := (Finset.mem_erase.mp hj).1
      have hne_nat : 2 + j.1 ≠ 2 + m := fun h => hjne (Fin.ext (by simp [mFin]; omega))
      exact act_twoLevelMat_ket_other (modeKet M 1) (modeKet M (2 + m)) (modeKet M (2 + j.1))
        _ (modeKet_ne M (2 + j.1) 1 (by omega) (by omega) (by omega))
        (modeKet_ne M (2 + j.1) (2 + m) (by omega) (by omega) hne_nat) hadamard
    have hR01_fix : ∀ j ∈ Finset.univ.erase mFin, act R01 (ket (modeKet M (2 + j.1))) = ket (modeKet M (2 + j.1)) := by
      intro j _
      exact act_twoLevelMat_ket_other (modeKet M 0) (modeKet M 1) (modeKet M (2 + j.1))
        _ (modeKet_ne M (2 + j.1) 0 (by omega) (by omega) (by omega))
        (modeKet_ne M (2 + j.1) 1 (by omega) (by omega) (by omega)) (R2J m)
    rw [hsplit_after, hR, act_mul, act_mul, act_add, hH1, hfix_other H12 hH12_fix,
      act_add, hR01_act, hfix_other R01 hR01_fix, act_add, hH2, hfix_other H12 hH12_fix]
    have hsplit_b : vecW M (bVec M m t) =
        ((bVec M m t 0 : ℂ) • ket (modeKet M 1) + (bVec M m t mFin.succ : ℂ) • ket (modeKet M (2 + m))) +
        ∑ j ∈ Finset.univ.erase mFin, (bVec M m t j.succ : ℂ) • ket (modeKet M (2 + j.1)) := by
      unfold vecW
      rw [Fin.sum_univ_succ, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ mFin)]
      simp only [Fin.val_zero, zero_add]
      have hidx : mFin.succ.1 + 1 = 2 + m := by simp only [Fin.val_succ, mFin]; omega
      rw [hidx]
      have hsum_idx : ∑ j ∈ Finset.univ.erase mFin, (bVec M m t j.succ : ℂ) • ket (modeKet M (j.succ.1 + 1)) =
          ∑ j ∈ Finset.univ.erase mFin, (bVec M m t j.succ : ℂ) • ket (modeKet M (2 + j.1)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hid : j.succ.1 + 1 = 2 + j.1 := by simp only [Fin.val_succ]; omega
        rw [hid]
      rw [hsum_idx]; abel
    rw [hsplit_b]; abel
  · have hm_eq : m = M := by omega
    subst hm_eq
    have hnot_lt : ¬ (t.1 / 2 < m) := by dsimp [t]; omega
    let R01 := twoLevelMat (modeKet m 0) (modeKet m 1)
      (modeKet_ne m 0 1 (by omega) (by omega) (by omega)) (R2Top m)
    have hR : R_mat410 m t.1 = R01 := by
      unfold R_mat410
      rw [if_neg ht0, dif_neg (fun h => hnot_lt h.2), if_pos ⟨hM, rfl⟩]
    have ha_alpha : (-1 : ℝ) ^ m * aVec m m t 0 = alphaM m := by
      simp [aVec, alphaM, pVecPoly, qVecPoly, hpow_t, t]
      rw [pow_succ']
      ring
    have hb_beta : bVec m m t 0 = betaM m := by
      simp [bVec, betaM, pVecPoly, qVecPoly, hpow_t, t]; ring
    have ha_alphaC : (-1 : ℂ) ^ (t.1 / 2) * (aVec m m t 0 : ℂ) = (alphaM m : ℂ) := by
      rw [hhalf]; exact_mod_cast ha_alpha
    have hb_betaC : (bVec m m t 0 : ℂ) = (betaM m : ℂ) := by exact_mod_cast hb_beta
    have hR_star : act R01 ((alphaM m : ℂ) • ket (modeKet m 1)) =
        ket (modeKet m 0) + (betaM m : ℂ) • ket (modeKet m 1) := by
      rw [act_smul, act_twoLevelMat_ket_right, smul_add, smul_smul, smul_smul]
      have hc1 : (alphaM m : ℂ) * R2Top m false true = 1 := by
        simp only [R2Top, Matrix.of_apply]
        norm_cast
        exact mul_div_cancel₀ _ (alphaM_ne_zero m)
      have hc2 : (alphaM m : ℂ) * R2Top m true true = (betaM m : ℂ) := by
        simp only [R2Top, Matrix.of_apply]
        norm_cast
        exact mul_div_cancel₀ _ (alphaM_ne_zero m)
      rw [hc1, hc2, one_smul]
    have hR_rest : act R01 (∑ j : Fin m, ((-1 : ℂ) ^ min j.1 (t.1 / 2) * (aVec m m t j.succ : ℂ)) •
          ket (modeKet m (2 + j.1))) =
        ∑ j : Fin m, (bVec m m t j.succ : ℂ) • ket (modeKet m (2 + j.1)) := by
      rw [act_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hjne : j.1 ≠ m := Nat.ne_of_lt j.isLt
      rw [hj_eq j hjne, act_smul]
      congr 1
      exact act_twoLevelMat_ket_other (modeKet m 0) (modeKet m 1) (modeKet m (2 + j.1))
        _ (modeKet_ne m (2 + j.1) 0 (by omega) (by omega) (by omega))
        (modeKet_ne m (2 + j.1) 1 (by omega) (by omega) (by omega)) (R2Top m)
    rw [hR, ha_alphaC, act_add, hR_star, hR_rest]
    unfold vecW
    rw [Fin.sum_univ_succ, hb_betaC]
    simp only [Fin.val_zero, zero_add]
    have hsum_idx : ∑ j : Fin m, (bVec m m t j.succ : ℂ) • ket (modeKet m (j.succ.1 + 1)) =
        ∑ j : Fin m, (bVec m m t j.succ : ℂ) • ket (modeKet m (2 + j.1)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hid : j.succ.1 + 1 = 2 + j.1 := by simp only [Fin.val_succ]; omega
      rw [hid]
    rw [hsum_idx]; abel

/-! ### Section 4: Two-register `H_hat410`, `U_tilde410`, catalyst energy, and ideal walk step -/

lemma tensorVec_add_left {α β : Type*} (u₁ u₂ : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    tensorVec (u₁ + u₂) v = tensorVec u₁ v + tensorVec u₂ v := by
  ext p; simp [tensorVec, add_mul]

lemma tensorVec_add_right {α β : Type*} (u : EuclideanSpace ℂ α) (v₁ v₂ : EuclideanSpace ℂ β) :
    tensorVec u (v₁ + v₂) = tensorVec u v₁ + tensorVec u v₂ := by
  ext p; simp [tensorVec, mul_add]

lemma tensorVec_smul_left {α β : Type*} (c : ℂ) (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    tensorVec (c • u) v = c • tensorVec u v := by
  ext p; simp [tensorVec, mul_assoc]

lemma tensorVec_smul_right {α β : Type*} (c : ℂ) (u : EuclideanSpace ℂ α) (v : EuclideanSpace ℂ β) :
    tensorVec u (c • v) = c • tensorVec u v := by
  ext p; simp [tensorVec]; ring

lemma tensorVec_sum_left {α β κ : Type*} (s : Finset κ) (u : κ → EuclideanSpace ℂ α)
    (v : EuclideanSpace ℂ β) :
    tensorVec (∑ x ∈ s, u x) v = ∑ x ∈ s, tensorVec (u x) v := by
  classical
  induction s using Finset.induction_on with
  | empty => ext p; simp [tensorVec]
  | insert a s ha ih => rw [Finset.sum_insert ha, tensorVec_add_left, ih, Finset.sum_insert ha]

lemma tensorVec_sum_right {α β κ : Type*} (s : Finset κ) (u : EuclideanSpace ℂ α)
    (v : κ → EuclideanSpace ℂ β) :
    tensorVec u (∑ x ∈ s, v x) = ∑ x ∈ s, tensorVec u (v x) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext p; simp [tensorVec]
  | insert a s ha ih => rw [Finset.sum_insert ha, tensorVec_add_right, ih, Finset.sum_insert ha]

lemma tensorVec_ket_ket {α β : Type*} [DecidableEq α] [DecidableEq β] (a : α) (b : β) :
    tensorVec (ket a) (ket b) = ket (a, b) := by
  ext ⟨a', b'⟩
  by_cases ha : a' = a <;> by_cases hb : b' = b <;>
    simp [tensorVec, ket, PiLp.single_apply, ha, hb]

lemma norm_sq_sum_tensorVec_ket {α β κ : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (s : Finset κ) (idx : κ → α) (hinj : Set.InjOn idx (s : Set κ))
    (ψ : κ → EuclideanSpace ℂ β) :
    ‖∑ c ∈ s, tensorVec (ket (idx c)) (ψ c)‖ ^ 2 = ∑ c ∈ s, ‖ψ c‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hterm : ∀ (a : α) (b : β),
      ‖(∑ c ∈ s, tensorVec (ket (idx c)) (ψ c)) (a, b)‖ ^ 2 =
        ∑ c ∈ s, if a = idx c then ‖ψ c b‖ ^ 2 else 0 := by
    intro a b
    have hval : (∑ c ∈ s, tensorVec (ket (idx c)) (ψ c)) (a, b) =
        ∑ c ∈ s, if a = idx c then ψ c b else 0 := by
      simp only [WithLp.ofLp_sum, Finset.sum_apply, tensorVec, ket, PiLp.single_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h : a = idx c <;> simp [h]
    rw [hval]
    by_cases hex : ∃ c ∈ s, a = idx c
    · rcases hex with ⟨c₀, hc₀, rfl⟩
      rw [Finset.sum_eq_single c₀]
      · rw [Finset.sum_eq_single c₀]
        · simp
        · intro c hc hne; have hne' : idx c₀ ≠ idx c := fun h => hne (hinj hc hc₀ h.symm); simp [hne']
        · intro hnot; exact absurd hc₀ hnot
      · intro c hc hne; have hne' : idx c₀ ≠ idx c := fun h => hne (hinj hc hc₀ h.symm); simp [hne']
      · intro hnot; exact absurd hc₀ hnot
    · have h0 : ∀ c ∈ s, a ≠ idx c := fun c hc h => hex ⟨c, hc, h⟩
      have h1 : (∑ c ∈ s, if a = idx c then ψ c b else 0) = 0 :=
        Finset.sum_eq_zero fun c hc => by simp [h0 c hc]
      have h2 : (∑ c ∈ s, if a = idx c then ‖ψ c b‖ ^ 2 else 0) = 0 :=
        Finset.sum_eq_zero fun c hc => by simp [h0 c hc]
      rw [h1, h2, norm_zero, sq, mul_zero]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext b
    rw [Finset.sum_comm]
  calc ∑ b : β, ∑ c ∈ s, ∑ a : α, (if a = idx c then ‖ψ c b‖ ^ 2 else 0)
      = ∑ b : β, ∑ c ∈ s, ‖ψ c b‖ ^ 2 := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_eq_single (idx c)] <;> simp (config := { contextual := true }) [eq_comm]
    _ = ∑ c ∈ s, ∑ b : β, ‖ψ c b‖ ^ 2 := Finset.sum_comm

lemma H_hat410_mul_self (M n' : ℕ) : H_hat410 M n' * H_hat410 M n' = 1 := by
  ext ⟨m₁, q₁⟩ ⟨m₂, q₂⟩
  simp only [H_hat410, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type]
  by_cases hm : m₁ = m₂
  · subst hm
    rw [Finset.sum_eq_single m₁]
    · simp only [↓reduceIte, Prod.mk.injEq, true_and]
      by_cases hz : m₁ = modeKet M 0
      · simp only [hz, ↓reduceIte]
        rw [Finset.sum_eq_single q₁]
        · simp
        · intro x _ hx; simp [hx.symm]
        · simp
      · simpa only [hz, ↓reduceIte, ← Matrix.mul_apply, Matrix.one_apply] using
          congrFun (congrFun (hadamardN_mul_self n') q₁) q₂
    · intro m' _ hm'; simp [hm'.symm]
    · simp
  · simp only [Prod.mk.injEq, hm, false_and, ↓reduceIte]
    refine Finset.sum_eq_zero fun m' _ => Finset.sum_eq_zero fun q' _ => ?_
    by_cases h1 : m₁ = m'
    · subst h1; simp [hm]
    · simp [h1]

lemma H_hat410_mem_unitaryGroup (M n' : ℕ) :
    H_hat410 M n' ∈ Matrix.unitaryGroup (Qubits (qW M) × Qubits n') ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hstar : star (H_hat410 M n') = H_hat410 M n' := by
    ext ⟨m₁, q₁⟩ ⟨m₂, q₂⟩
    simp only [Matrix.star_apply, H_hat410, Matrix.of_apply]
    by_cases hm : m₁ = m₂
    · subst hm
      by_cases hz : m₁ = modeKet M 0
      · simp [hz, Matrix.one_apply, eq_comm]
      · have hs := congrFun (congrFun (hadamardN_star n') q₁) q₂
        simp only [Matrix.star_apply] at hs
        simpa [hz] using hs
    · simp [hm, ne_comm.mp hm]
  rw [hstar, H_hat410_mul_self]

lemma act_H_hat410_zero (M n' : ℕ) (ψ : EuclideanSpace ℂ (Qubits n')) :
    act (H_hat410 M n') (tensorVec (ket (modeKet M 0)) ψ) = tensorVec (ket (modeKet M 0)) ψ := by
  ext ⟨m', q'⟩
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, H_hat410, Matrix.of_apply,
    tensorVec, ket, PiLp.single_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (modeKet M 0)]
  · by_cases hm : m' = modeKet M 0
    · subst hm
      simp only [↓reduceIte, one_mul, Matrix.one_apply]
      rw [Finset.sum_eq_single q'] <;> simp (config := { contextual := true }) [eq_comm]
    · simp [hm]
  · intro u _ hu; refine Finset.sum_eq_zero fun q _ => ?_; simp [hu]
  · simp

lemma act_H_hat410_ne {M n' : ℕ} {u : Qubits (qW M)} (hu : u ≠ modeKet M 0)
    (ψ : EuclideanSpace ℂ (Qubits n')) :
    act (H_hat410 M n') (tensorVec (ket u) ψ) = tensorVec (ket u) (act (hadamardN n') ψ) := by
  ext ⟨m', q'⟩
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, H_hat410, Matrix.of_apply,
    tensorVec, ket, PiLp.single_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single u]
  · by_cases hm : m' = u
    · subst hm
      simp [hu]
    · simp [hm]
  · intro m₀ _ hm₀; refine Finset.sum_eq_zero fun q _ => ?_; simp [hm₀]
  · simp

lemma U_tilde410_mem_unitaryGroup (M n' : ℕ) :
    U_tilde410 M n' ∈ Matrix.unitaryGroup (Qubits (qW M) × Qubits n') ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨m₁, q₁⟩ ⟨m₂, q₂⟩
  simp only [U_tilde410, Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
    Fintype.sum_prod_type]
  by_cases hq : q₁ = q₂
  · subst hq
    have hU := Matrix.mem_unitaryGroup_iff.mp (U_op410_mem_unitaryGroup M (hammingWeight q₁))
    have hent := congrFun (congrFun hU m₁) m₂
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at hent
    rw [Finset.sum_comm, Finset.sum_eq_single q₁]
    · simpa [Prod.mk.injEq] using hent
    · intro q' _ hqq; refine Finset.sum_eq_zero fun m' _ => ?_; simp [hqq.symm]
    · simp
  · simp only [Prod.mk.injEq, hq, and_false, ↓reduceIte]
    refine Finset.sum_eq_zero fun m' _ => Finset.sum_eq_zero fun q' _ => ?_
    by_cases h1 : q₁ = q'
    · subst h1; simp [Ne.symm hq]
    · simp [h1]

lemma act_U_tilde410_tensorVec_ket (M n' : ℕ) (w : EuclideanSpace ℂ (Qubits (qW M))) (q : Qubits n') :
    act (U_tilde410 M n') (tensorVec w (ket q)) =
      tensorVec (act (U_op410 M (hammingWeight q)) w) (ket q) := by
  ext ⟨m', q'⟩
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, U_tilde410, Matrix.of_apply,
    tensorVec, ket, PiLp.single_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_eq_single q]
  · by_cases hqq : q' = q
    · subst hqq
      simp only [↓reduceIte, mul_one]
    · simp [hqq]
  · intro q₀ _ hq₀; refine Finset.sum_eq_zero fun m₀ _ => ?_; simp [hq₀]
  · simp

lemma wCatVec410_mode_zero_eq_zero {n' M m : ℕ} (B : Finset (Fin n')) (hB : B.card = 2 * m + 1)
    (S : Qubits n') :
    wCatVec410 n' M m B hB (modeKet M 0, S) = 0 := by
  unfold wCatVec410
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hne : modeKet M 0 ≠ modeKet M (c.1 + 1) :=
    modeKet_ne M 0 (c.1 + 1) (by omega) (by omega) (by omega)
  simp [tensorVec, ket, PiLp.single_apply, hne]

lemma wCatVec410_energy_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k n : ℕ), 2 ≤ k → k ≤ n →
      ∀ (A : BoundedSupports n k),
        ‖wCatVec410 (n + 1) (k / 2) (layerOf A) (liftOdd A) (liftOdd_card_eq A).1‖ ^ 2 ≤ C₀ * Real.log k := by
  obtain ⟨C_core, hC_pos, hC_bound⟩ := WVec_energy_bound
  refine ⟨C_core, hC_pos, ?_⟩
  intro k n hk2 hkn A
  let M := k / 2
  let m := layerOf A
  let B := liftOdd A
  have hB : B.card = 2 * m + 1 := (liftOdd_card_eq A).1
  have hmM : m ≤ M := (liftOdd_card_eq A).2
  have hM1 : 1 ≤ M := by dsimp [M]; omega
  have hlen : 2 * m + 1 ≤ n + 1 := by omega
  have hnorm_vec : ‖wCatVec410 (n + 1) M m B hB‖ ^ 2 =
      ∑ c : Fin (M + 1), ‖wCatCoord410 (n + 1) M m B hB c‖ ^ 2 := by
    unfold wCatVec410
    exact norm_sq_sum_tensorVec_ket Finset.univ (fun c : Fin (M + 1) => modeKet M (c.1 + 1))
      (fun c₁ _ c₂ _ h => modeKet_injOn M h) _
  have hnorm_c : ∀ c : Fin (M + 1),
      ‖wCatCoord410 (n + 1) M m B hB c‖ ^ 2 =
        (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
          ∑ S : Qubits (n + 1), (WVec M m (intersectionIndex ⟨B, hB⟩ S) c) ^ 2 := by
    intro c
    rw [EuclideanSpace.norm_sq_eq]
    have hcoeff : ∀ S : Qubits (n + 1),
        ‖wCatCoord410 (n + 1) M m B hB c S‖ ^ 2 =
          (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
            (WVec M m (intersectionIndex ⟨B, hB⟩ S) c) ^ 2 := by
      intro S
      let Aex : ExactSupports (n + 1) (2 * m + 1) := ⟨B, hB⟩
      have hreal_sum : (∑ t : Fin (2 * m + 2),
            (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℝ) * bVec M m t c) =
          WVec M m (intersectionIndex Aex S) c / Real.sqrt 2 := by
        simp only [WVec, LVec, UVec, bVec]
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring
      have hsum_cast : (∑ t : Fin (2 * m + 2),
            (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bVec M m t c : ℂ)) =
          ((WVec M m (intersectionIndex Aex S) c / Real.sqrt 2 : ℝ) : ℂ) := by
        rw [← hreal_sum]; push_cast; rfl
      have hscale : (((Real.sqrt 2)⁻¹ ^ (n + 1) : ℝ) : ℂ) *
            ((WVec M m (intersectionIndex Aex S) c / Real.sqrt 2 : ℝ) : ℂ) =
          ((((Real.sqrt 2)⁻¹ ^ (n + 1) : ℝ) *
            (WVec M m (intersectionIndex Aex S) c / Real.sqrt 2) : ℝ) : ℂ) := by
        push_cast; rfl
      simp only [wCatCoord410]
      change ‖(((Real.sqrt 2)⁻¹ ^ (n + 1) : ℝ) : ℂ) *
          ∑ t : Fin (2 * m + 2),
            (krawtchouk (2 * m + 1) t (intersectionIndex Aex S) : ℂ) * (bVec M m t c : ℂ)‖ ^ 2 = _
      rw [hsum_cast, hscale, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, div_pow]
      have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h2 : ((Real.sqrt 2)⁻¹ ^ (n + 1)) ^ 2 = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
        rw [← pow_mul, mul_comm (n + 1) 2, pow_mul, inv_pow, hs, zpow_neg, zpow_natCast, inv_pow]
      rw [h2, hs]
      ring
    simp_rw [hcoeff, ← Finset.mul_sum]
  rw [hnorm_vec]
  simp_rw [hnorm_c, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hcore := hC_bound (n + 1) M m hM1 hmM hlen ⟨B, hB⟩
  have hlog_le : Real.log (2 * (M : ℝ) + 1) ≤ 2 * Real.log (k : ℝ) := by
    have h2M : 2 * M ≤ k := by dsimp [M]; omega
    have hk_sq : 2 * M + 1 ≤ k ^ 2 := by nlinarith
    have h1 : (2 * (M : ℝ) + 1) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hk_sq
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    simpa using h2
  calc (1 / 2 : ℝ) * (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
        ∑ S : Qubits (n + 1), ∑ c : Fin (M + 1), (WVec M m (intersectionIndex ⟨B, hB⟩ S) c) ^ 2
      = (1 / 2 : ℝ) * ((2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) *
          ∑ S : Qubits (n + 1), ∑ c : Fin (M + 1), (WVec M m (intersectionIndex ⟨B, hB⟩ S) c) ^ 2) := by ring
    _ ≤ (1 / 2 : ℝ) * (C_core * Real.log (2 * M + 1)) := by
        exact mul_le_mul_of_nonneg_left hcore (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (C_core * (2 * Real.log k)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog_le hC_pos.le) (by norm_num)
    _ = C_core * Real.log k := by ring

lemma phaseCtrl410_mul_zero_ket (M n' : ℕ) (B : Finset (Fin n')) (ψ : EuclideanSpace ℂ (Qubits n')) :
    act (phaseCtrl410 M n' B) (tensorVec (ket (modeKet M 0)) ψ) = tensorVec (ket (modeKet M 0)) ψ := by
  ext ⟨m', q'⟩
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, phaseCtrl410, Matrix.of_apply,
    tensorVec, ket, PiLp.single_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (modeKet M 0)]
  · rw [Finset.sum_eq_single q']
    · by_cases hm : m' = modeKet M 0 <;> simp [hm]
    · intro q₀ _ hq₀; simp [hq₀.symm]
    · simp
  · intro m₀ _ hm₀; refine Finset.sum_eq_zero fun q _ => ?_; simp [hm₀]
  · simp

lemma act_phaseCtrl410_wCatVec410 {n' M m : ℕ} (B : Finset (Fin n')) (hB : B.card = 2 * m + 1) :
    act (phaseCtrl410 M n' B) (wCatVec410 n' M m B hB) = wCatAfter410 n' M m B hB := by
  let Aex : ExactSupports n' (2 * m + 1) := ⟨B, hB⟩
  unfold wCatVec410 wCatAfter410
  rw [act_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hne : modeKet M (c.1 + 1) ≠ modeKet M 0 :=
    modeKet_ne M (c.1 + 1) 0 (by omega) (by omega) (by omega)
  ext ⟨m', q'⟩
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, phaseCtrl410, Matrix.of_apply,
    tensorVec, ket, PiLp.single_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (modeKet M (c.1 + 1))]
  · rw [Finset.sum_eq_single q']
    · by_cases hm' : m' = modeKet M (c.1 + 1)
      · subst hm'
        simp only [↓reduceIte, one_mul, ne_eq, hne, not_false_eq_true, true_and]
        have hb_eq : (∑ t : Fin (2 * m + 2),
              (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℝ) * bVec M m t c) =
            (LVec M m (intersectionIndex Aex q') c + UVec M m (intersectionIndex Aex q') c) / Real.sqrt 2 := by
          simp only [LVec, UVec, bVec, ← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun t _ => ?_; ring
        have ha_eq : (∑ t : Fin (2 * m + 2),
              (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℝ) * aVec M m t c) =
            (UVec M m (intersectionIndex Aex q') c - LVec M m (intersectionIndex Aex q') c) / Real.sqrt 2 := by
          simp only [LVec, UVec, aVec, ← Finset.sum_sub_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun t _ => ?_; ring
        have hmaj : majorityBit B q' = true ↔ (intersectionIndex Aex q' : ℕ) ≤ m := by
          simp only [majorityBit, intersectionIndex, Aex, hB, decide_eq_true_eq]
          omega
        have hsign_real : (if majorityBit B q' then (-1 : ℝ) else 1) *
              ((LVec M m (intersectionIndex Aex q') c + UVec M m (intersectionIndex Aex q') c) / Real.sqrt 2) =
            (UVec M m (intersectionIndex Aex q') c - LVec M m (intersectionIndex Aex q') c) / Real.sqrt 2 := by
          by_cases hle : (intersectionIndex Aex q' : ℕ) ≤ m
          · have hm : majorityBit B q' = true := hmaj.mpr hle
            rw [if_pos hm, UVec_eq_zero_of_le hle]; ring
          · have hgt : m < (intersectionIndex Aex q' : ℕ) := Nat.lt_of_not_ge hle
            have hm : majorityBit B q' = false := Bool.eq_false_iff.mpr fun h => hle (hmaj.mp h)
            rw [if_neg (by simp [hm]), LVec_eq_zero_of_gt hgt]; ring
        have hsignC : (if majorityBit B q' then (-1 : ℂ) else 1) *
              ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℂ) * (bVec M m t c : ℂ) =
            ∑ t : Fin (2 * m + 2), (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℂ) * (aVec M m t c : ℂ) := by
          have hc1 : (∑ t : Fin (2 * m + 2),
                (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℂ) * (bVec M m t c : ℂ)) =
              (((LVec M m (intersectionIndex Aex q') c + UVec M m (intersectionIndex Aex q') c) / Real.sqrt 2 : ℝ) : ℂ) := by
            rw [← hb_eq]; push_cast; rfl
          have hc2 : (∑ t : Fin (2 * m + 2),
                (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℂ) * (aVec M m t c : ℂ)) =
              (((UVec M m (intersectionIndex Aex q') c - LVec M m (intersectionIndex Aex q') c) / Real.sqrt 2 : ℝ) : ℂ) := by
            rw [← ha_eq]; push_cast; rfl
          rw [hc1, hc2]
          by_cases hm : majorityBit B q' = true
          · simp only [hm, ↓reduceIte] at hsign_real ⊢; exact_mod_cast hsign_real
          · have hmf : majorityBit B q' = false := Bool.eq_false_iff.mpr hm
            simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hsign_real ⊢; exact_mod_cast hsign_real
        simp only [wCatCoord410, wCatAfterCoord410]
        change (if majorityBit B q' then (-1 : ℂ) else 1) *
            ((((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
              ∑ t : Fin (2 * m + 2),
                (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℂ) * (bVec M m t c : ℂ)) =
          (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
            ∑ t : Fin (2 * m + 2),
              (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℂ) * (aVec M m t c : ℂ)
        calc (if majorityBit B q' then (-1 : ℂ) else 1) *
              ((((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
                ∑ t : Fin (2 * m + 2),
                  (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℂ) * (bVec M m t c : ℂ))
            = (((Real.sqrt 2)⁻¹ ^ n' : ℝ) : ℂ) *
                ((if majorityBit B q' then (-1 : ℂ) else 1) *
                  ∑ t : Fin (2 * m + 2),
                    (krawtchouk (2 * m + 1) t (intersectionIndex Aex q') : ℂ) * (bVec M m t c : ℂ)) := by ring
          _ = _ := by rw [hsignC]
      · simp [hm']
    · intro q₀ _ hq₀; simp [hq₀.symm]
    · simp
  · intro m₀ _ hm₀; refine Finset.sum_eq_zero fun q _ => ?_; simp [hm₀]
  · simp

lemma U_ideal410_transduces {n' M m : ℕ} (hM : 1 ≤ M) (hmM : m ≤ M) (hle : 2 * m + 1 ≤ n')
    (B : Finset (Fin n')) (hB : B.card = 2 * m + 1) :
    act (U_ideal410 M n')
        (tensorVec (ket (modeKet M 0)) (zeroKet n') + wCatAfter410 n' M m B hB) =
      tensorVec (ket (modeKet M 0)) (ket (fun i : Fin n' => decide (i ∈ B))) + wCatVec410 n' M m B hB := by
  have _ := hle
  let indB : Qubits n' := fun i => decide (i ∈ B)
  have h1 : act (H_hat410 M n')
        (tensorVec (ket (modeKet M 0)) (zeroKet n') + wCatAfter410 n' M m B hB) =
      tensorVec (ket (modeKet M 0)) (zeroKet n') +
        ∑ t : Fin (2 * m + 2), tensorVec (vecW M (aVec M m t)) (uniformSubsetKet n' B t.1) := by
    rw [act_add, act_H_hat410_zero]
    unfold wCatAfter410
    rw [act_sum]
    have hterm : ∀ c : Fin (M + 1),
        act (H_hat410 M n') (tensorVec (ket (modeKet M (c.1 + 1))) (wCatAfterCoord410 n' M m B hB c)) =
          ∑ t : Fin (2 * m + 2),
            tensorVec ((aVec M m t c : ℂ) • ket (modeKet M (c.1 + 1))) (uniformSubsetKet n' B t.1) := by
      intro c
      have hne : modeKet M (c.1 + 1) ≠ modeKet M 0 :=
        modeKet_ne M (c.1 + 1) 0 (by omega) (by omega) (by omega)
      rw [act_H_hat410_ne hne]
      unfold wCatAfterCoord410
      rw [act_hadamardN_krawtchouk_combo B hB (fun t => aVec M m t c), tensorVec_sum_right]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [tensorVec_smul_right, ← tensorVec_smul_left]
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← tensorVec_sum_left]
    rfl
  have hU_0 : act (U_tilde410 M n')
        (tensorVec (ket (modeKet M 0)) (zeroKet n') +
          tensorVec (vecW M (aVec M m 0)) (uniformSubsetKet n' B 0)) =
      tensorVec (vecW M (bVec M m 0)) (uniformSubsetKet n' B 0) := by
    rw [uniformSubsetKet_zero, ← tensorVec_add_left, zeroKet, act_U_tilde410_tensorVec_ket,
      show hammingWeight (fun _ : Fin n' => false) = 0 from by simp [hammingWeight],
      act_U_op410_zero hmM]
  have hU_int : ∀ t : Fin (2 * m + 2), 1 ≤ t.1 → t.1 ≤ 2 * m →
      act (U_tilde410 M n') (tensorVec (vecW M (aVec M m t)) (uniformSubsetKet n' B t.1)) =
        tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1) := by
    intro t ht1 ht2
    unfold uniformSubsetKet
    rw [tensorVec_sum_right, act_sum, tensorVec_sum_right]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTcard : T.card = t.1 := (Finset.mem_powersetCard.mp hT).2
    rw [act_U_tilde410_tensorVec_ket, hammingWeight_indicator, hTcard,
      act_U_op410_interior hmM t ht1 ht2]
  have hU_top : act (U_tilde410 M n')
        (tensorVec (vecW M (aVec M m ⟨2 * m + 1, by omega⟩)) (uniformSubsetKet n' B (2 * m + 1))) =
      tensorVec (ket (modeKet M 0)) (ket indB) +
        tensorVec (vecW M (bVec M m ⟨2 * m + 1, by omega⟩)) (uniformSubsetKet n' B (2 * m + 1)) := by
    have hself : uniformSubsetKet n' B (2 * m + 1) = ket indB := by
      rw [← hB]; exact uniformSubsetKet_self B
    rw [hself, act_U_tilde410_tensorVec_ket, hammingWeight_indicator, hB,
      act_U_op410_top hM hmM, tensorVec_add_left]
  let topIdx : Fin (2 * m + 2) := ⟨2 * m + 1, by omega⟩
  have hmem_top : topIdx ∈ Finset.univ.erase (0 : Fin (2 * m + 2)) := by
    rw [Finset.mem_erase]
    exact ⟨by intro h; have := congrArg Fin.val h; simp [topIdx] at this, Finset.mem_univ _⟩
  have hsplit_a :
      (∑ t : Fin (2 * m + 2), tensorVec (vecW M (aVec M m t)) (uniformSubsetKet n' B t.1)) =
      tensorVec (vecW M (aVec M m 0)) (uniformSubsetKet n' B 0) +
      tensorVec (vecW M (aVec M m topIdx)) (uniformSubsetKet n' B (2 * m + 1)) +
        ∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
          tensorVec (vecW M (aVec M m t)) (uniformSubsetKet n' B t.1) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin (2 * m + 2))),
      ← Finset.add_sum_erase (Finset.univ.erase (0 : Fin (2 * m + 2))) _ hmem_top]
    simp only [Fin.val_zero, topIdx]
    abel
  have hsplit_b :
      (∑ t : Fin (2 * m + 2), tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1)) =
      tensorVec (vecW M (bVec M m 0)) (uniformSubsetKet n' B 0) +
      tensorVec (vecW M (bVec M m topIdx)) (uniformSubsetKet n' B (2 * m + 1)) +
        ∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
          tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin (2 * m + 2))),
      ← Finset.add_sum_erase (Finset.univ.erase (0 : Fin (2 * m + 2))) _ hmem_top]
    simp only [Fin.val_zero, topIdx]
    abel
  have hU_mid :
      act (U_tilde410 M n')
        (∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
          tensorVec (vecW M (aVec M m t)) (uniformSubsetKet n' B t.1)) =
      ∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
        tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1) := by
    rw [act_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_erase, Finset.mem_erase] at ht
    have ht0 : t.1 ≠ 0 := fun h => ht.2.1 (Fin.ext h)
    have htk : t.1 ≠ 2 * m + 1 := fun h => ht.1 (Fin.ext h)
    exact hU_int t (Nat.pos_of_ne_zero ht0) (by have := t.isLt; omega)
  have h2 : act (U_tilde410 M n')
        (act (H_hat410 M n') (tensorVec (ket (modeKet M 0)) (zeroKet n') + wCatAfter410 n' M m B hB)) =
      tensorVec (ket (modeKet M 0)) (ket indB) +
        ∑ t : Fin (2 * m + 2), tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1) := by
    rw [h1, hsplit_a]
    have hassoc : tensorVec (ket (modeKet M 0)) (zeroKet n') +
          (tensorVec (vecW M (aVec M m 0)) (uniformSubsetKet n' B 0) +
            tensorVec (vecW M (aVec M m topIdx)) (uniformSubsetKet n' B (2 * m + 1)) +
            ∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
              tensorVec (vecW M (aVec M m t)) (uniformSubsetKet n' B t.1)) =
        (tensorVec (ket (modeKet M 0)) (zeroKet n') +
          tensorVec (vecW M (aVec M m 0)) (uniformSubsetKet n' B 0)) +
          tensorVec (vecW M (aVec M m topIdx)) (uniformSubsetKet n' B (2 * m + 1)) +
          ∑ t ∈ (Finset.univ.erase (0 : Fin (2 * m + 2))).erase topIdx,
            tensorVec (vecW M (aVec M m t)) (uniformSubsetKet n' B t.1) := by abel
    rw [hassoc, act_add, act_add, hU_0, hU_top, hU_mid, hsplit_b]
    abel
  have h3 : act (H_hat410 M n') (tensorVec (ket (modeKet M 0)) (ket indB) +
        ∑ t : Fin (2 * m + 2), tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1)) =
      tensorVec (ket (modeKet M 0)) (ket indB) + wCatVec410 n' M m B hB := by
    have hsum_eq : (∑ t : Fin (2 * m + 2), tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1)) =
        ∑ c : Fin (M + 1), tensorVec (ket (modeKet M (c.1 + 1))) (act (hadamardN n') (wCatCoord410 n' M m B hB c)) := by
      have hcomm : (∑ t : Fin (2 * m + 2), tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1)) =
          ∑ c : Fin (M + 1), ∑ t : Fin (2 * m + 2),
            tensorVec (ket (modeKet M (c.1 + 1))) ((bVec M m t c : ℂ) • uniformSubsetKet n' B t.1) := by
        unfold vecW
        simp_rw [tensorVec_sum_left, tensorVec_smul_left, ← tensorVec_smul_right]
        exact Finset.sum_comm
      rw [hcomm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← tensorVec_sum_right]
      unfold wCatCoord410
      rw [act_hadamardN_krawtchouk_combo B hB (fun t => bVec M m t c)]
    rw [hsum_eq, act_add, act_H_hat410_zero, act_sum]
    congr 1
    unfold wCatVec410
    refine Finset.sum_congr rfl fun c _ => ?_
    have hne : modeKet M (c.1 + 1) ≠ modeKet M 0 :=
      modeKet_ne M (c.1 + 1) 0 (by omega) (by omega) (by omega)
    rw [act_H_hat410_ne hne, ← act_mul, hadamardN_mul_self, act_one_vec]
  calc act (U_ideal410 M n') (tensorVec (ket (modeKet M 0)) (zeroKet n') + wCatAfter410 n' M m B hB)
      = act (H_hat410 M n') (act (U_tilde410 M n') (act (H_hat410 M n')
          (tensorVec (ket (modeKet M 0)) (zeroKet n') + wCatAfter410 n' M m B hB))) := by
        simp [U_ideal410, act_mul]
    _ = act (H_hat410 M n') (tensorVec (ket (modeKet M 0)) (ket indB) +
          ∑ t : Fin (2 * m + 2), tensorVec (vecW M (bVec M m t)) (uniformSubsetKet n' B t.1)) := by
        rw [h2]
    _ = tensorVec (ket (modeKet M 0)) (ket indB) + wCatVec410 n' M m B hB := h3

end TransducerAlgebra410

end Thm410Algebra

section MainTheorem410Coupled

open QAlgorithms QuantumLTF.Majority QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.CoupledOp410

theorem solution :
    (∀ M t, U_op410 M t ∈ Matrix.unitaryGroup (Qubits (qW M)) ℂ) ∧
    (∀ j, R2J j ∈ Matrix.unitaryGroup Bool ℂ) ∧
    (∀ M, R2Top M ∈ Matrix.unitaryGroup Bool ℂ) ∧
    (∀ {n k : ℕ} (A : BoundedSupports n k),
      (∀ i : Fin n, i.castSucc ∈ liftOdd A ↔ i ∈ A.1) ∧
      ((liftOdd A).card = 2 * layerOf A + 1 ∧ layerOf A ≤ k / 2) ∧
      (∀ x : Qubits n, majorityBit (liftOdd A) (Fin.snoc (α := fun _ => Bool) x true) = majorityBit A.1 x) ∧
      (∀ x : Qubits n, majorityBit (liftOdd A) (Fin.snoc (α := fun _ => Bool) (fun i => !(x i)) false) = !(majorityBit A.1 x))) ∧
    (∀ {n' M m : ℕ} (B : Finset (Fin n')) (hB : B.card = 2 * m + 1) (S : Qubits n'),
      wCatVec410 n' M m B hB (modeKet M 0, S) = 0) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k n : ℕ), 2 ≤ k → k ≤ n →
      ∀ (A : BoundedSupports n k) (hB : (liftOdd A).card = 2 * layerOf A + 1),
        ‖wCatVec410 (n + 1) (k / 2) (layerOf A) (liftOdd A) hB‖ ^ 2 ≤ C₀ * Real.log k) ∧
    (∀ {n' M m : ℕ} (B : Finset (Fin n')) (hB : B.card = 2 * m + 1),
      act (phaseCtrl410 M n' B) (wCatVec410 n' M m B hB) = wCatAfter410 n' M m B hB) ∧
    (∀ {n' M m : ℕ} (_hM : 1 ≤ M) (_hmM : m ≤ M) (_hle : 2 * m + 1 ≤ n')
      (B : Finset (Fin n')) (hB : B.card = 2 * m + 1),
      act (U_ideal410 M n') (tensorVec (ket (modeKet M 0)) (zeroKet n') + wCatAfter410 n' M m B hB) =
        tensorVec (ket (modeKet M 0)) (ket (fun i : Fin n' => decide (i ∈ B))) + wCatVec410 n' M m B hB) := by
  refine ⟨Thm410Algebra.U_op410_mem_unitaryGroup,
    Thm410Algebra.R2J_mem_unitaryGroup,
    Thm410Algebra.R2Top_mem_unitaryGroup,
    fun A => ⟨Thm410Algebra.liftOdd_mem_castSucc A, Thm410Algebra.liftOdd_card_eq A,
      Thm410Algebra.liftOdd_majorityBit_snoc_true A, Thm410Algebra.liftOdd_majorityBit_snoc_false A⟩,
    fun B hB S => Thm410Algebra.wCatVec410_mode_zero_eq_zero B hB S,
    ?_,
    fun B hB => Thm410Algebra.act_phaseCtrl410_wCatVec410 B hB,
    fun hM hmM hle B hB => Thm410Algebra.U_ideal410_transduces hM hmM hle B hB⟩
  obtain ⟨C₀, hC₀, hBnd⟩ := Thm410Algebra.wCatVec410_energy_bound
  exact ⟨C₀, hC₀, fun k n hk2 hkn A _hB => hBnd k n hk2 hkn A⟩

end MainTheorem410Coupled
