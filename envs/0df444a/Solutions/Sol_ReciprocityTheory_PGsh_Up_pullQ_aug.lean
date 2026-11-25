-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.pullQ_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:11:17.634027+00:00
-- url     : https://prove2.me/submissions/0d257985-ceff-4e14-9c05-ec1dbd4fbbe0

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_aug
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1


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
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable (K : AddSubgroup N) [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (AA : HopfOrder (C := C) R N) (AQ : HopfOrder (C := C) R (N ⧸ K))
    (hAQ : AQ.carrier = AA.carrier.comap (pullQ K)) {b : N ⧸ K → C}
    (hb : b ∈ augIdeal AQ.carrier) : pullQ (R := R) K b ∈ augIdeal AA.carrier := by
  rw [mem_aug] at hb ⊢
  refine ⟨?_, ?_⟩
  · have h1 : b ∈ AA.carrier.comap (pullQ (R := R) K) := hAQ ▸ hb.1
    exact h1
  · simpa [pullQ, LinearMap.funLeft_apply] using hb.2
end ReciprocityTheory.PGsh.Up
