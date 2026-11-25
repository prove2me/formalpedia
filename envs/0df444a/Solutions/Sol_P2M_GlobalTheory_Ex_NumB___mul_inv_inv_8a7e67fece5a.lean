-- Prove2me | solution 1 for P2M_GlobalTheory_Ex_NumB___mul_inv_inv_8a7e67fece5a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:44.778776+00:00
-- url     : https://prove2.me/submissions/a41d4ed6-6acb-4a93-ba29-778a48148848

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339


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
theorem _root_.solution (x y : B.A) : B.θ (x * y) x⁻¹ y⁻¹ * B.θ x x⁻¹ y = B.θ y y⁻¹ x⁻¹ := by
  have a := B.cub.coc x y y⁻¹ x⁻¹
  rwa [mul_inv_cancel, B.cub.face₂, one_mul, B.cub.s12, B.cub.s12 x y] at a
end GlobalTheory.Ex.NumB
