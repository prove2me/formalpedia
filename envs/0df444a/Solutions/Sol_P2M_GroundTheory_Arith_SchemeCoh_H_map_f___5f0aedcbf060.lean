-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_H_map_f___5f0aedcbf060
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:41.459368+00:00
-- url     : https://prove2.me/submissions/d1d32a6b-e382-433b-a6a6-071fde7fd379

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H___apply_db07d4b535cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GroundTheory.Arith.SchemeCoh
namespace H
theorem _root_.solution {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    Sheaf.H.map S.f n₁ (H.δ hS n₀ n₁ h x) = 0 := by
  rw [H.δ_apply, Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp,
    Ext.comp_zero]
end H
end GroundTheory.Arith.SchemeCoh
