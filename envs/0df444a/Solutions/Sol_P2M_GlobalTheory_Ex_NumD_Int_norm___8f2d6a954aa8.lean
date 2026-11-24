-- Prove2me | solution 1 for P2M_GlobalTheory_Ex_NumD_Int_norm___8f2d6a954aa8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:45:16.099934+00:00
-- url     : https://prove2.me/submissions/b2a31074-df3d-4eae-9b2c-0e051897aaac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
namespace GlobalTheory.Ex.NumD.Int
theorem _root_.solution (h : N.Int q) (a b : N.X) : ‖(N.τ a b : C)‖ = Real.exp (-QuadraticMap.polar q a b) := by
  rw [NumD.τ, Units.val_div_eq_div_val, Units.val_div_eq_div_val, norm_div, norm_div, h.ψ, h.ψ, h.ψ,
    ← Real.exp_sub, ← Real.exp_sub, QuadraticMap.polar]
  congr 1
  ring
end GlobalTheory.Ex.NumD.Int
