-- Prove2me | solution 1 for PositivityTheory.ThKR.Join.poly_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:39.87369+00:00
-- url     : https://prove2.me/submissions/19dbcd54-24ba-4e9e-872c-9da7a81b8ede

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalPoly
import Theorems.Thm_PositivityTheory_ThKR_Join_aeval_inter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.KReal PositivityTheory.ThKF.Unit
namespace PositivityTheory.ThKR.Join
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (C : Module.End ℂ M) (U : Submodule ℂ M) [FiniteDimensional ℂ U]
    (hU : ∀ y ∈ U, C y ∈ U) (hi : Function.Injective (C.restrict hU)) {x : M} (hx : x ∈ U) :
    ∃ g : Polynomial ℂ, g.eval 0 = 1 ∧ Polynomial.aeval C g x = 0 := by
  have h0 : (C.restrict hU).charpoly.eval 0 ≠ 0 := fun e => by
    obtain ⟨m, h1, h2⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff (C.restrict hU)).1
      (by rw [Polynomial.constantCoeff_apply, Polynomial.coeff_zero_eq_eval_zero, e])
    exact h1 (hi (h2.trans (map_zero _).symm))
  refine ⟨Polynomial.C ((C.restrict hU).charpoly.eval 0)⁻¹ * (C.restrict hU).charpoly, ?_, ?_⟩
  · rw [Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ h0]
  · have := aeval_inter U.subtype (C.restrict hU) C (fun _ => rfl) (C.restrict hU).charpoly ⟨x, hx⟩
    rw [LinearMap.aeval_self_charpoly] at this
    rw [map_mul, Module.End.mul_apply, show Polynomial.aeval C (C.restrict hU).charpoly x = 0 from this.symm, map_zero]
end PositivityTheory.ThKR.Join
