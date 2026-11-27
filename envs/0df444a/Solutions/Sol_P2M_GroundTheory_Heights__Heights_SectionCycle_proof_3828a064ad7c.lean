-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionCycle_proof_3828a064ad7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:48.060895+00:00
-- url     : https://prove2.me/submissions/4793bc69-a2c0-42c0-af57-9bb9f0eb6b35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LiftOldChartMonomialMemPrimeCompl
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_zero_84a12a66bfd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_divCycle_eq_of_cross_e8d8a257b3c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_mem_8765b3f76011
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_cross_mem_b4bbd6c8875a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_swap_mem_d8794d20a831
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_liftOld_chartMonomial_mem_primeCompl_232337c8b957
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionCycle_exists_form_not_mem_587f4c48195d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionCycle
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SectionCycle
theorem _root_.solution : SectionCycle.Statement := by
  intro ι _ _ n P D d g hg c j hgc W
  unfold NumbersDVR.ratDiv
  rw [sub_eq_zero]
  have hc : P.IsLive c := by
    by_contra hc
    exact hgc (by rw [hg.dead c hc j, map_zero]; exact Submodule.zero_mem _)
  by_cases hW : W.IsPrime ∧ NumbersDVR.IsRelevant W ∧ D.extIdeal ≤ W
  swap
  · rw [divCycle_eq_zero _ hW, divCycle_eq_zero _ hW]
  obtain ⟨hWp, hrel, hPW⟩ := hW
  have := hWp
  choose c' hc'W using fun k : ι ↦ hrel (some k)
  obtain ⟨j', hj'W⟩ := hrel none
  let c'' : (k : ι) → Fin (n k + 1) := c'
  have hWc : ∀ k, (X (D.oldCoord ⟨k, c'' k⟩) : MvPolynomial _ ℤ) ∉ W := hc'W
  have hlive : P.IsLive c'' := fun k hk ↦ by
    have h := hPW (liftOld_mem D hk)
    rw [AddBlockData.liftOld, rename_X] at h
    exact hWc k h
  obtain ⟨i, hi⟩ := exists_form_not_mem D hg hlive hPW hWc
  have hj'' : (X (D.newCoord j') : MvPolynomial (Coord D.extSizes) ℤ) ∉ W := hj'W
  have hg' : D.liftOld (g c'' j') ∉ W := by
    intro hmem
    have hs := hPW (swap_mem D hg hlive i j')
    have : D.liftOld (g c'' i) * X (D.newCoord j') ∈ W := by
      have := W.add_mem hs (W.mul_mem_right (X (D.newCoord i)) hmem)
      rwa [sub_add_cancel] at this
    rcases Ideal.IsPrime.mem_or_mem hWp this with h | h
    · exact hi h
    · exact hj'' h
  have hf' : X (D.newCoord j') * D.liftOld (chartMonomial c'' d) ∉ W := by
    intro hmem
    rcases Ideal.IsPrime.mem_or_mem hWp hmem with h | h
    · exact hj'' h
    · exact Ideal.mem_primeCompl_iff.mp (liftOld_chartMonomial_mem_primeCompl D hWc d) h
  exact divCycle_eq_of_cross _ hf' hg' (cross_mem D hg hc hlive j j')
end GroundTheory.Heights₂.Heights.SectionCycle
