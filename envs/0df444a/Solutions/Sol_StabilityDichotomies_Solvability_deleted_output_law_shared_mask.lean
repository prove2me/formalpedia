-- Prove2me | solution 1 for StabilityDichotomies.Solvability.deleted_output_law_shared_mask
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:26:48.501987+00:00
-- url     : https://prove2.me/submissions/6b223293-f061-4ade-9b63-8272055d9dee

import Theorems.Thm_StabilityDichotomies_Solvability_delete_occurrence_equivalence
import Theorems.Thm_StabilityDichotomies_Solvability_delete_thinned_mask_alignment
import Theorems.Thm_StabilityDichotomies_Approximability_bernoulli_mask_restriction
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Approximability

theorem solution (Γ : Language) (b : Bool) (ε : ℝ)
    (A : Solver Γ) (hLaw : ThinningOutputLaw Γ b ε A)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (c : Constraint Γ V) (hc : c ∈ I.constraints) :
    ∃ i : Fin I.constraints.card, ∀ x : V → Bool,
      (A V (I.delete c) x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
        ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
          (if extremalSolution (thinnedInstance I (Function.update mask i false)) b = x then 1 else 0) := by
  obtain ⟨e,he⟩ := delete_occurrence_equivalence I c hc
  refine ⟨e.symm none, ?_⟩
  intro x
  have hDel : Satisfiable (I.delete c) := by
    obtain ⟨a,ha⟩ := hSat
    refine ⟨a,?_⟩
    intro d hd
    apply ha d
    exact Multiset.mem_of_mem_erase hd
  rw [hLaw V (I.delete c) hDel x]
  congr 1
  apply intervalIntegral.integral_congr
  intro p hp
  have h := bernoulli_mask_restriction e p (fun mask : Fin (I.delete c).constraints.card → Bool =>
    if extremalSolution (thinnedInstance (I.delete c) mask) b = x then (1 : ℝ) else 0)
  have hAlign (mask : Fin I.constraints.card → Bool) :
      extremalSolution (thinnedInstance I (Function.update mask (e.symm none) false)) b =
      extremalSolution (thinnedInstance (I.delete c) (fun k => mask (e.symm (some k)))) b := by
    rw [delete_thinned_mask_alignment I c hc e he mask]
  simp only [retentionWeight]
  simp_rw [hAlign]
  convert h.symm using 1
  · apply Finset.sum_congr
    · ext z; simp
    · intro z hz
      congr 1
  · apply Finset.sum_congr
    · ext z; simp
    · intro z hz
      congr 1
