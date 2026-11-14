-- Prove2me | solution 1 for StabilityDichotomies.Solvability.deleted_output_law_at_original_index
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:31:34.160013+00:00
-- url     : https://prove2.me/submissions/806b61d3-71ee-432b-8a1b-0b35dda44e98

import Theorems.Thm_StabilityDichotomies_Solvability_delete_equivalence_at_original_index
import Theorems.Thm_StabilityDichotomies_Solvability_delete_thinned_mask_alignment
import Theorems.Thm_StabilityDichotomies_Approximability_bernoulli_mask_restriction
noncomputable section
open scoped Classical BigOperators Interval
open MeasureTheory StabilityDichotomies.Solvability StabilityDichotomies.Approximability

theorem solution (Γ : Language) (b : Bool) (ε : ℝ)
    (A : Solver Γ) (hLaw : ThinningOutputLaw Γ b ε A)
    (V : Type) [Fintype V] (I : Instance Γ V) (hSat : Satisfiable I)
    (i : Fin I.constraints.card) (x : V → Bool) :
      (A V (I.delete (occurrenceAt I i)) x).toReal = ε⁻¹ * ∫ p in (1-ε)..1,
        ∑ mask : Fin I.constraints.card → Bool, retentionWeight p mask *
          (if extremalSolution (thinnedInstance I (Function.update mask i false)) b = x then 1 else 0) := by
  let c := occurrenceAt I i
  have hc : c ∈ I.constraints := by
    unfold c occurrenceAt
    exact Multiset.mem_toList.mp (List.get_mem _ _)
  obtain ⟨e, he0, he⟩ := delete_equivalence_at_original_index I i
  have hei : e.symm none = i := by
    apply e.injective
    simpa using he0.symm
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
  rw [← hei]
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
