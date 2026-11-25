-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.pullQ_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:07.627197+00:00
-- url     : https://prove2.me/submissions/bfd9f084-367d-4714-b6e6-261a0cb46389

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Theorems.Thm_ReciprocityTheory_PGsh_Up_pullQ_aug

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
    (hAQ : AQ.carrier = AA.carrier.comap (pullQ K)) {z : N ⧸ K → C}
    (hz : z ∈ sqIdeal (augIdeal AQ.carrier)) :
    pullQ (R := R) K z ∈ sqIdeal (augIdeal AA.carrier) := by
  have key : sqIdeal (augIdeal AQ.carrier) ≤
      (sqIdeal (augIdeal AA.carrier)).comap (pullQ (R := R) K) := by
    rw [sqIdeal, Submodule.span_le]
    rintro h ⟨f, hf, f', hf', rfl⟩
    apply Submodule.subset_span
    exact ⟨_, pullQ_aug K AA AQ hAQ hf, _, pullQ_aug K AA AQ hAQ hf', rfl⟩
  exact key hz
end ReciprocityTheory.PGsh.Up
