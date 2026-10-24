-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P38.contractiveOperator_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:15:32.876832+00:00
-- url     : https://prove2.me/submissions/2008a403-ec1a-46a3-a021-f92b3781cd35

import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P38_jensenOperator_equivalences

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
namespace QAlgorithms.Papers.Independent.Renew46.P38.ContractiveProof
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma zero_inInterval (I : Set ℝ) (hzero : 0 ∈ I) :
    InInterval I (0 : Operators H) := by
  refine ⟨IsSelfAdjoint.zero _, ?_⟩
  rcases subsingleton_or_nontrivial (Operators H) with h | h
  · let := h
    simp [spectrum.of_subsingleton]
  · let := h
    simpa only [spectrum.zero_eq, Set.singleton_subset_iff] using hzero

lemma zero_cfc_nonpos (f : ℝ → ℝ) (hf : f 0 ≤ 0) :
    cfc f (0 : Operators H) ≤ 0 := by
  rcases subsingleton_or_nontrivial (Operators H) with h | h
  · let := h
    exact le_of_eq (Subsingleton.elim _ _)
  · let := h
    apply cfc_nonpos
    simpa only [spectrum.zero_eq, Set.mem_singleton_iff, forall_eq] using hf

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
lemma contractive_of_unital (I : Set ℝ) (f : ℝ → ℝ) (hzero : 0 ∈ I)
    (hfzero : f 0 ≤ 0) (n : ℕ)
    (hJ : UnitalJensenOn H I f (n + 1)) : ContractiveJensenOn H I f n := by
  intro x a hx ha
  let b := CFC.sqrt (1 - columnSquares a)
  have hb : star b * b = 1 - columnSquares a := by
    rw [(CFC.sqrt_nonneg (1 - columnSquares a)).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr ha)
  have hunital : columnSquares (Fin.cons b a) = 1 := by
    simp only [columnSquares, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change star b * b + columnSquares a = 1
    rw [hb, sub_add_cancel]
  have h := hJ (Fin.cons 0 x) (Fin.cons b a)
    (fun i => Fin.cases (zero_inInterval I hzero) hx i) hunital
  have hneg : star b * cfc f (0 : Operators H) * b ≤ 0 := by
    simpa using star_left_conjugate_le_conjugate (zero_cfc_nonpos f hfzero) b
  simp only [combination, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    mul_zero, zero_mul, zero_add] at h
  exact h.trans (add_le_of_nonpos_left hneg)

lemma isometry_of_contractive (I : Set ℝ) (f : ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hJ : AllContractiveJensen.{u} I f n) : IsometryJensen.{u} I f := by
  intro H _ _ _ _ v x hv hx
  classical
  let i₀ : Fin n := ⟨0, by omega⟩
  let a : Fin n → Operators H := fun i => if i = i₀ then v else 0
  have ha : columnSquares a = 1 := by
    simpa [columnSquares, a] using hv
  have h := hJ H (fun _ => x) a (fun _ => hx) ha.le
  simpa [combination, a] using h

lemma nonpos_of_contractive (I : Set ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f I)
    (hzero : 0 ∈ I) (n : ℕ) (hJ : AllContractiveJensen.{u} I f n) : f 0 ≤ 0 := by
  let H := EuclideanSpace ℂ (ULift.{u} Unit)
  have hz := zero_inInterval (H := H) I hzero
  have h := hJ H (fun _ => 0) (fun _ => 0) (fun _ => hz)
    (by simp [columnSquares])
  have hc : cfc f (0 : Operators H) ≤ 0 := by simpa [combination] using h
  exact (cfc_nonpos_iff f (0 : Operators H) (hf.mono hz.2)).mp hc 0
    (by simp)

end QAlgorithms.Papers.Independent.Renew46.P38.ContractiveProof

open QAlgorithms.Papers.Independent.Renew46.P38
universe u

theorem solution (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I) (hzero : 0 ∈ I) :
    ((IntervalOperatorConvex.{u} I f ∧ f 0 ≤ 0) ↔
      ∃ n : ℕ, 1 ≤ n ∧ AllContractiveJensen.{u} I f n) ∧
    ((IntervalOperatorConvex.{u} I f ∧ f 0 ≤ 0) ↔
      ∀ n : ℕ, 1 ≤ n → AllContractiveJensen.{u} I f n) := by
  have hforward : (IntervalOperatorConvex.{u} I f ∧ f 0 ≤ 0) →
      ∀ n : ℕ, 1 ≤ n → AllContractiveJensen.{u} I f n := by
    intro h n _ H _ _ _
    exact ContractiveProof.contractive_of_unital I f hzero h.2 n
      ((jensenOperator_equivalences I f hI hf).1.mp h.1 (n + 1) (by omega) H)
  have hback : (∃ n : ℕ, 1 ≤ n ∧ AllContractiveJensen.{u} I f n) →
      IntervalOperatorConvex.{u} I f ∧ f 0 ≤ 0 := by
    rintro ⟨n, hn, hJ⟩
    exact ⟨(jensenOperator_equivalences I f hI hf).2.1.mpr
      (ContractiveProof.isometry_of_contractive I f n hn hJ),
      ContractiveProof.nonpos_of_contractive I f hf hzero n hJ⟩
  exact ⟨⟨fun h => ⟨1, le_rfl, hforward h 1 le_rfl⟩, hback⟩,
    ⟨hforward, fun h => hback ⟨1, le_rfl, h 1 le_rfl⟩⟩⟩
