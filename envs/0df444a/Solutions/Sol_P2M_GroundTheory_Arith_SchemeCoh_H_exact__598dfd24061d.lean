-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_H_exact__598dfd24061d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:29.127944+00:00
-- url     : https://prove2.me/submissions/96750fb8-a4b2-4607-80b6-fe7f8f0d4910

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
theorem _root_.solution {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (y : Sheaf.H S.X₃ n₀)
    (hy : H.δ hS n₀ n₁ h y = 0) : ∃ x : Sheaf.H S.X₂ n₀, Sheaf.H.map S.g n₀ x = y :=
  Ext.covariant_sequence_exact₃ _ hS y h hy
end H
end GroundTheory.Arith.SchemeCoh
