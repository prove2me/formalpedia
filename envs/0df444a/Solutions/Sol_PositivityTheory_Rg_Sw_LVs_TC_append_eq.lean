-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.append_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:20:41.480943+00:00
-- url     : https://prove2.me/submissions/b55d36d4-44a3-4a33-94bc-b92ded040c27

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCHeights
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlockC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_epsE_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_epsE_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (j : ℕ) (σA : Equiv.Perm (blkA (n := n) j)) (τ : Equiv.Perm (blkB (n := n) j)) :
    Fin.append (fun i => embL (blkA (n := n) j) (single ((Fintype.equivFin (blkA (n := n) j)).symm i)
        (σA ((Fintype.equivFin (blkA (n := n) j)).symm i)) (1 : ℂ)))
      (fun i => embL (blkB (n := n) j) (single ((Fintype.equivFin (blkB (n := n) j)).symm i)
        (τ ((Fintype.equivFin (blkB (n := n) j)).symm i)) (1 : ℂ))) = vv (piP j σA τ) ∘ epsE j := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left, Function.comp_apply, epsE_left]
    generalize (Fintype.equivFin (blkA (n := n) j)).symm i = a
    have hp : piP j σA τ a = σA a := by
      simp [piP, Equiv.Perm.subtypeCongr.left_apply _ _ a.2]
    ext p q
    simp only [vv, hp, embL]
    simp only [embOn, Matrix.single_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hpq : (a : Fin n) = p ∧ (σA a : Fin n) = q
    · obtain ⟨rfl, rfl⟩ := hpq
      simp
    · rw [if_neg hpq]
      split_ifs with h1 h2
      · exact absurd ⟨by rw [h2.1], by rw [h2.2]⟩ hpq
      · rfl
      · rfl
  · simp only [Fin.append_right, Function.comp_apply, epsE_right]
    generalize (Fintype.equivFin (blkB (n := n) j)).symm i = b
    have hp : piP j σA τ b = τ b := by
      have hb : (b : Fin n) ∉ blkA (n := n) j := by
        have := b.2; simpa [blkB] using this
      simp [piP, Equiv.Perm.subtypeCongr.right_apply _ _ hb, eBq]
      exact Subtype.ext rfl
    ext p q
    simp only [vv, hp, embL]
    simp only [embOn, Matrix.single_apply, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hpq : (b : Fin n) = p ∧ (τ b : Fin n) = q
    · obtain ⟨rfl, rfl⟩ := hpq
      simp
    · rw [if_neg hpq]
      split_ifs with h1 h2
      · exact absurd ⟨by rw [h2.1], by rw [h2.2]⟩ hpq
      · rfl
      · rfl
end PositivityTheory.Rg.Sw.LVs.TC
