-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_H___apply_db07d4b535cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:28.513138+00:00
-- url     : https://prove2.me/submissions/b7ddf659-736d-4536-bb92-de14853cb10f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH

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
theorem _root_.solution (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : Sheaf.H S.X₃ n₀) :
    H.δ hS n₀ n₁ h x = x.comp hS.extClass h := rfl
end H
end GroundTheory.Arith.SchemeCoh
