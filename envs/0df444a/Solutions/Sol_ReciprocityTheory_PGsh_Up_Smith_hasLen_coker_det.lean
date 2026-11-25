-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.Smith.hasLen_coker_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:30:13.648156+00:00
-- url     : https://prove2.me/submissions/6a1b46e0-9cbd-4f16-bda2-813d8a2c14ea

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_smith_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.Smith
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.Smith
theorem _root_.solution (hv : v.Integers R) {n : ℕ} (X : Matrix (Fin n) (Fin n) R) :
    HasLen v R ((Fin n → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)) := by
  obtain ⟨c, e, h⟩ := smith_sq hv n X
  exact ⟨n, c, e, h.symm⟩
end ReciprocityTheory.PGsh.Up.Smith
