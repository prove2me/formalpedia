-- Prove2me | solution 1 for PI.IsoFunVW.det_submatrix_noninj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:46:50.789195+00:00
-- url     : https://prove2.me/submissions/81a824b1-6dee-412c-8e39-cfcebc7a6204

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Equiv
open PI PI.IsoFunVW
namespace PI.IsoFunVW
theorem _root_.solution {R : Type*} [CommRing R] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) R) (f : Fin m → Fin n) (hf : ¬ Function.Injective f) :
    (B.submatrix f id).det = 0 := by
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  exact det_zero_of_row_eq hne (by ext k; simp [hij])
end PI.IsoFunVW
