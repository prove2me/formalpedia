-- Prove2me | solution 1 for ReciprocityTheory.PGsh.wedge_ne_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:06.413942+00:00
-- url     : https://prove2.me/submissions/77516724-8475-4fa9-bf33-2e15962815f8

import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open ReciprocityTheory ReciprocityTheory.PGsh
attribute [local instance] extModR
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {k : ℕ} {b : Fin k → V} (hb : LinearIndependent K b) :
    ExteriorAlgebra.ιMulti K k b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := k) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin k)).toOrderEmbedding)
  intro h0; apply h
  apply Subtype.ext
  simpa [exteriorPower.ιMulti_family] using h0
end ReciprocityTheory.PGsh
