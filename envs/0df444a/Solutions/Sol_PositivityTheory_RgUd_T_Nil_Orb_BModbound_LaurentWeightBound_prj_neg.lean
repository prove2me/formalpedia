-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.prj_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:51.140066+00:00
-- url     : https://prove2.me/submissions/783bd06c-1df9-4a41-8da8-3f39b7a931de

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
open PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
variable {k : Type} [Field k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
theorem _root_.solution (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (hm : m < 0) (y : Fin n → k)
    (hy : ∃ u : Fin n → k, y = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) : prj P w m y = 0 := by
  obtain ⟨u, rfl, hu⟩ := hy
  rw [prj, mulVec_mulVec]
  simp only [Units.inv_mul, one_mulVec]
  have hc : cut w m u = 0 := by
    ext i
    simp only [cut, Pi.zero_apply]
    split_ifs with h
    · exact hu i (h ▸ hm)
    · rfl
  rw [hc, mulVec_zero]
end PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
