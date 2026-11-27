-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_H_exact__8bc15c0024ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:53:34.99328+00:00
-- url     : https://prove2.me/submissions/aa7db0f5-1417-43dc-8930-f6c7a11cdf35

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
include hS
namespace GroundTheory.Arith.SchemeCoh
namespace H
theorem _root_.solution {n : ℕ} (y : Sheaf.H S.X₂ n) (hy : Sheaf.H.map S.g n y = 0) :
    ∃ x : Sheaf.H S.X₁ n, Sheaf.H.map S.f n x = y :=
  Ext.covariant_sequence_exact₂ _ hS y hy
end H
end GroundTheory.Arith.SchemeCoh
