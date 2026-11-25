-- Prove2me | solution 1 for PI.WGL.Adj.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:08.027132+00:00
-- url     : https://prove2.me/submissions/d544de93-bd03-45f3-9f72-1d7f0cbb642f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitPowerNormScale_NormUnitsZpowSq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_AdjBase
import Theorems.Thm_PI_WHw_bC_fd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.Adj
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL.Adj
theorem _root_.solution (n : ℕ) (sg : DomWeight n) :
    ∃ (d : ℕ) (b : Fin d → MvPolynomial (Fin n × Fin n) ℂ), (∀ k, b k ∈ nablaSq ℂ n sg) ∧
      ∀ s ∈ nablaSq ℂ n sg, s = ∑ k, normFock sg s (b k) • b k := by
  letI : NormedAddCommGroup (nablaSq ℂ n sg) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (frameCore n sg)
  letI : InnerProductSpace ℂ (nablaSq ℂ n sg) := InnerProductSpace.ofCore (frameCore n sg).toCore
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  let b := stdOrthonormalBasis ℂ (nablaSq ℂ n sg)
  refine ⟨Module.finrank ℂ (nablaSq ℂ n sg), fun k => (b k : MvPolynomial (Fin n × Fin n) ℂ),
    fun k => (b k).2, fun s hs => ?_⟩
  have h1 := congrArg Subtype.val (b.sum_repr' ⟨s, hs⟩)
  rw [Submodule.coe_sum] at h1
  exact h1.symm
end PI.WGL.Adj
