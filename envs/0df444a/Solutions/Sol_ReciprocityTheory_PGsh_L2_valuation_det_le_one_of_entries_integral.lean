-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.valuation_det_le_one_of_entries_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:40:07.162227+00:00
-- url     : https://prove2.me/submissions/b7c629a3-08d2-4628-a796-e3b4229275de

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Matrix X X C) (hM : ∀ i j, ∃ r : R, algebraMap R C r = M i j) : v M.det ≤ 1 := by
  choose Mr hMr using hM
  have e : M = (algebraMap R C).mapMatrix (Matrix.of Mr) := by
    ext i j; simp [hMr]
  rw [e, ← RingHom.map_det]
  exact hv.map_le_one _
end ReciprocityTheory.PGsh.L2
