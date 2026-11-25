-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.pow_mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:01:20.275533+00:00
-- url     : https://prove2.me/submissions/ed41f614-62ef-4a66-a5e2-0420684d5935

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
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (AA : HopfOrder (C := C) R N) {f : N → C} (hf : f ∈ AA.carrier) :
    ∀ k : ℕ, f ^ k ∈ AA.carrier := by
  intro k
  induction k with
  | zero => simpa using AA.one_mem
  | succ k ih => rw [pow_succ]; exact AA.mul_mem _ _ ih hf
end ReciprocityTheory.PGsh.Up
