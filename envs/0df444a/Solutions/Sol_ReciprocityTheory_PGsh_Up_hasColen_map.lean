-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.hasColen_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:42:06.743678+00:00
-- url     : https://prove2.me/submissions/a289d98c-89fb-412e-b92a-32ded7e3241f

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv

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
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (v : Valuation C NNReal) (e : X ≃+ Y) (M : Submodule R (Y → C)) (c : NNReal)
    (h : HasColen R v M c) : HasColen R v (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) c := by
  obtain ⟨B, hM, hc⟩ := h
  exact ⟨B.submatrix e e, by rw [hM, map_cols], by rw [det_sub, hc]⟩
end ReciprocityTheory.PGsh.Up
