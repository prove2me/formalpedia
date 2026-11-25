-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.mem_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:04:03.279295+00:00
-- url     : https://prove2.me/submissions/5e533815-429b-45fe-bce7-de27e788c20b

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) (f : X → C) :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  simp [augIdeal, Submodule.mem_inf, LinearMap.mem_ker]
end ReciprocityTheory.PGsh.Up
