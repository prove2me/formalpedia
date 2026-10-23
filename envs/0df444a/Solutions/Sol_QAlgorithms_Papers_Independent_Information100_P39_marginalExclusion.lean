-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P39.marginalExclusion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:24:54.737985+00:00
-- url     : https://prove2.me/submissions/78321387-657a-4972-a2cb-e198b2dff32c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

namespace X6P39M

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P39

local notation "ω" => SparsePauliNoise.symplecticPairing

theorem sgn_add (x y : ZMod 2) :
    (-1 : ℝ) ^ (x + y).val = (-1 : ℝ) ^ x.val * (-1 : ℝ) ^ y.val := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

theorem sgn_sum {ι : Type*} (s : Finset ι) (c : ι → ZMod 2) :
    (-1 : ℝ) ^ (∑ a ∈ s, c a).val = ∏ a ∈ s, (-1 : ℝ) ^ (c a).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sgn_add, ih]

theorem omega_add_right {N : ℕ} (u a b : PauliLabel N) : ω u (a + b) = ω u a + ω u b := by
  simp only [SparsePauliNoise.symplecticPairing, Prod.fst_add, Prod.snd_add, dotProduct_add]
  ring

theorem omega_add_left {N : ℕ} (u a b : PauliLabel N) : ω (a + b) u = ω a u + ω b u := by
  simp only [SparsePauliNoise.symplecticPairing, Prod.fst_add, Prod.snd_add, add_dotProduct]
  ring

theorem omega_sum_right {N m : ℕ} (u : PauliLabel N) (b : Fin m → ZMod 2) (e : Fin m → PauliLabel N) :
    ω u (∑ a, b a • e a) = ∑ a, b a * ω u (e a) := by
  simp only [SparsePauliNoise.symplecticPairing, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
    Prod.smul_snd, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.sum_add_distrib, mul_add]

theorem wht_event {N m : ℕ} (e : Fin m → PauliLabel N) (p : Fin m → ℝ) (u : PauliLabel N) :
    SparsePauliNoise.eigenvalueWHT (eventLaw e p) u =
      ∏ a, ((1 - p a) + p a * (-1 : ℝ) ^ (ω u (e a)).val) := by
  unfold SparsePauliNoise.eigenvalueWHT eventLaw pushLaw
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr (g := fun b : Bits m => (-1 : ℝ) ^ (ω u (∑ a, b a • e a)).val *
    binaryLaw p b) rfl fun b _ => ?_).trans ?_
  · simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]; simp
  simp_rw [omega_sum_right, sgn_sum, binaryLaw, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a (x : ZMod 2) =>
    (-1 : ℝ) ^ (x * ω u (e a)).val * (if x = 1 then p a else 1 - p a))]
  refine Finset.prod_congr rfl fun a _ => ?_
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} :=
    (Finset.eq_univ_of_card _ (by rw [Finset.card_pair zero_ne_one, ZMod.card])).symm
  rw [huniv, Finset.sum_pair zero_ne_one]
  simp
  ring

theorem triple (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s1 s2 s3 : ℝ)
    (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1) (h3 : s3 = 1 ∨ s3 = -1)
    (h : s1 * s2 * s3 = 1) :
    0 ≤ ((1 - p) + p * s1) * ((1 - p) + p * s2) * ((1 - p) + p * s3) := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    (try norm_num at h) <;> nlinarith [sq_nonneg (1 - 2 * p)]

theorem labels_sum : labelX + labelY + labelZ = (0 : PauliLabel 1) := by
  ext i <;> fin_cases i <;> simp [labelX, labelY, labelZ] <;> decide

theorem indep_nonneg (nu : PauliLabel 1 → ℝ) (h : HasIndependentEvents nu) :
    0 ≤ SparsePauliNoise.eigenvalueWHT nu labelX *
      SparsePauliNoise.eigenvalueWHT nu labelY *
      SparsePauliNoise.eigenvalueWHT nu labelZ := by
  obtain ⟨m, e, p, hp, rfl⟩ := h
  rw [wht_event, wht_event, wht_event, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_nonneg fun a _ => ?_
  have hsum : ω labelX (e a) + ω labelY (e a) + ω labelZ (e a) = 0 := by
    rw [← omega_add_left, ← omega_add_left, labels_sum]
    simp [SparsePauliNoise.symplecticPairing]
  have hprod : (-1 : ℝ) ^ (ω labelX (e a)).val * (-1 : ℝ) ^ (ω labelY (e a)).val *
      (-1 : ℝ) ^ (ω labelZ (e a)).val = 1 := by
    rw [← sgn_add, ← sgn_add, hsum]; simp
  exact triple (p a) (hp a).1 (hp a).2 _ _ _ (neg_one_pow_eq_or ℝ _) (neg_one_pow_eq_or ℝ _)
    (neg_one_pow_eq_or ℝ _) hprod

def proj {N : ℕ} (j : Fin N) (x : PauliLabel N) : PauliLabel 1 :=
  ((fun _ => x.1 j), (fun _ => x.2 j))

theorem push_push {A B C : Type*} [Fintype A] [Fintype B] (q : A → ℝ) (f : A → B) (g : B → C) :
    pushLaw (pushLaw q f) g = pushLaw q (g ∘ f) := by
  funext z
  simp only [pushLaw]
  have : ∀ y, (if g y = z then ∑ b, (if f b = y then q b else 0) else 0) =
      ∑ b, (if f b = y then (if g y = z then q b else 0) else 0) := by
    intro y
    split_ifs with h <;> simp [h]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem marginal_event {N m : ℕ} (e : Fin m → PauliLabel N) (p : Fin m → ℝ) (j : Fin N) :
    pauliMarginal (eventLaw e p) j = eventLaw (fun a => proj j (e a)) p := by
  unfold pauliMarginal eventLaw
  rw [push_push]
  congr 1
  funext b
  ext i <;> simp [proj, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

end X6P39M

open X6P39M QAlgorithms QAlgorithms.Papers.Independent.Information100.P39 in
theorem solution {N : ℕ} (nu : PauliLabel N → ℝ)
    (hnu : Learning.IsDistribution nu) (j : Fin N) :
    (HasIndependentEvents nu → HasIndependentEvents (pauliMarginal nu j)) ∧
    (SparsePauliNoise.eigenvalueWHT (pauliMarginal nu j) labelX *
      SparsePauliNoise.eigenvalueWHT (pauliMarginal nu j) labelY *
      SparsePauliNoise.eigenvalueWHT (pauliMarginal nu j) labelZ < 0 →
      ¬ HasIndependentEvents nu) := by
  have h1 : HasIndependentEvents nu → HasIndependentEvents (pauliMarginal nu j) := by
    rintro ⟨m, e, p, hp, rfl⟩
    exact ⟨m, fun a => proj j (e a), p, hp, marginal_event e p j⟩
  refine ⟨h1, fun hneg hind => ?_⟩
  have := indep_nonneg _ (h1 hind)
  linarith
