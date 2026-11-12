-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P89.naive_heralding_success
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:23:57.968927+00:00
-- url     : https://prove2.me/submissions/68606a0b-9142-463e-a11f-29e32dada170

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

open scoped BigOperators ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)

open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

namespace Aux_naive_heralding

open QAlgorithms.Papers.Independent.Intakenext100.P89

theorem herald_add {A : Type*} [Fintype A] (w : A → ℝ) (E : A → Prop) :
    heraldLaw w E true + heraldLaw w E false = ∑ a, w a := by
  simp only [heraldLaw]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : E a <;> simp [h]

theorem total (w : Bool → ℝ) (n : ℕ) :
    ∑ x : Fin n → Bool, copiesWeight w n x = (w true + w false) ^ n := by
  rw [← Fintype.sum_bool, Fintype.sum_pow]
  rfl

theorem any_norm (n : ℕ) (w : Bool → ℝ) :
    anyLaw n w true + anyLaw n w false = (w true + w false) ^ n := by
  rw [anyLaw, herald_add, total]

theorem any_false (n : ℕ) (w : Bool → ℝ) : anyLaw n w false = (w false) ^ n := by
  simp only [anyLaw, heraldLaw, copiesWeight]
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp
  · intro x _ hx
    have hex : ∃ i, x i = true := by
      by_contra hne
      push_neg at hne
      apply hx
      funext i
      simpa using hne i
    simp [hex]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem any_true (n : ℕ) (w : Bool → ℝ) :
    anyLaw n w true = (w true + w false) ^ n - (w false) ^ n := by
  have h1 := any_norm n w
  have h2 := any_false n w
  linarith

theorem all_true (n : ℕ) (w : Bool → ℝ) : allLaw n w true = (w true) ^ n := by
  simp only [allLaw, heraldLaw, copiesWeight]
  rw [Finset.sum_eq_single (fun _ => true)]
  · simp
  · intro x _ hx
    have hex : ¬ ∀ i, x i = true := by
      intro hall
      apply hx
      funext i
      exact hall i
    simp [hex]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem and_true' (w v : Bool → ℝ) : andLaw w v true = w true * v true := by
  simp only [andLaw, heraldLaw]
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_bool]

theorem and_norm (w v : Bool → ℝ) :
    andLaw w v true + andLaw w v false = (w true + w false) * (v true + v false) := by
  rw [andLaw, herald_add, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  ring

theorem bern_true (p : ℝ) : QAlgorithms.Papers.Independent.Information100.P56.bernoulli p true = p := rfl

theorem bern_false (p : ℝ) : QAlgorithms.Papers.Independent.Information100.P56.bernoulli p false = 1 - p := rfl

theorem bern_norm (p : ℝ) : QAlgorithms.Papers.Independent.Information100.P56.bernoulli p true + QAlgorithms.Papers.Independent.Information100.P56.bernoulli p false = 1 := by
  rw [bern_true, bern_false]; ring

theorem any_of_norm (n : ℕ) (w : Bool → ℝ) (hw : w true + w false = 1) :
    anyLaw n w true = 1 - (1 - w true) ^ n := by
  rw [any_true, hw, one_pow, show w false = 1 - w true by linarith]

theorem any_norm1 (n : ℕ) (w : Bool → ℝ) (hw : w true + w false = 1) :
    anyLaw n w true + anyLaw n w false = 1 := by
  rw [any_norm, hw, one_pow]

theorem and_norm1 (w v : Bool → ℝ) (hw : w true + w false = 1) (hv : v true + v false = 1) :
    andLaw w v true + andLaw w v false = 1 := by
  rw [and_norm, hw, hv, one_mul]

theorem cluster_norm (d : Devices) (nGHZ nB : ℕ) (l : ℕ) :
    naiveClusterLaw d nGHZ nB l true + naiveClusterLaw d nGHZ nB l false = 1 := by
  induction l with
  | zero =>
    simp only [naiveClusterLaw]
    exact any_norm1 _ _ (bern_norm _)
  | succ l ih =>
    simp only [naiveClusterLaw]
    exact any_norm1 _ _ (and_norm1 _ _ (and_norm1 _ _ ih ih) (bern_norm _))

end Aux_naive_heralding

open QAlgorithms.Papers.Independent.Intakenext100.P89 Aux_naive_heralding in
theorem solution (d : Devices) (k m n nGHZ nB nMeas : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hGHZ : 0 < nGHZ) (hB : 0 < nB)
    (hMeas : 0 < nMeas) :
    naiveClusterLaw d nGHZ nB 0 true = 1 - (1 - ghzSuccess d) ^ nGHZ ∧
    (∀ l : ℕ, naiveClusterLaw d nGHZ nB (l + 1) true =
      1 - (1 - (naiveClusterLaw d nGHZ nB l true) ^ 2 *
        naiveFusionSuccess d (l + 1)) ^ nB) ∧
    naiveFinalLaw d k m nGHZ nB nMeas true =
      1 - (1 - naiveClusterLaw d nGHZ nB k true *
        finalMeasurementSuccess d k m) ^ nMeas ∧
    allLaw n (naiveFinalLaw d k m nGHZ nB nMeas) true =
      (naiveFinalLaw d k m nGHZ nB nMeas true) ^ n := by
  refine ⟨?_, ?_, ?_, all_true _ _⟩
  · simp only [naiveClusterLaw]
    rw [any_of_norm _ _ (bern_norm _), bern_true]
  · intro l
    have hc := cluster_norm d nGHZ nB l
    simp only [naiveClusterLaw]
    rw [any_of_norm _ _ (and_norm1 _ _ (and_norm1 _ _ hc hc) (bern_norm _)),
      and_true', and_true', bern_true]
    ring
  · have hc := cluster_norm d nGHZ nB k
    simp only [naiveFinalLaw]
    rw [any_of_norm _ _ (and_norm1 _ _ hc (bern_norm _)), and_true', bern_true]

end
