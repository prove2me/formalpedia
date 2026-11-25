-- Prove2me | solution 1 for P2M_GlobalTheory_Ex_NumB___mul_symm_9d7986a68c1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:45:58.239888+00:00
-- url     : https://prove2.me/submissions/18bb1eac-2a5c-4614-b17c-5a245ac6dd0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_P2M_GlobalTheory_Ex_NumB___mul_inv_inv_8a7e67fece5a

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
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumB
variable {O : Type} [CommRing O] (B : NumB O)
namespace GlobalTheory.Ex.NumB
theorem _root_.solution (x y : B.A) : B.σ (x * y) * B.θ (x * y) x⁻¹ y⁻¹ = B.σ x * B.σ y := by
  have a := B.θ_mul_inv_inv y x
  have b := B.σ_mul x y
  rw [mul_comm y x, B.cub.s12] at a
  rw [← a, ← mul_assoc] at b
  exact mul_right_cancel b
end GlobalTheory.Ex.NumB
