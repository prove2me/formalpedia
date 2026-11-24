-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.gt_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:51.313695+00:00
-- url     : https://prove2.me/submissions/dfd2b05c-f354-4b7d-b2a0-b4ae56f25fbc

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
theorem _root_.solution (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) (y : Fin n → k) :
    gt P w t *ᵥ y = ∑ m ∈ Finset.univ.image w, ((t ^ m : kˣ) : k) • prj P w m y := by
  classical
  simp only [prj, ← mulVec_smul, ← mulVec_sum]
  rw [gt, ← mulVec_mulVec, ← mulVec_mulVec]
  congr 1
  ext i
  simp only [mulVec_diagonal, Finset.sum_apply, Pi.smul_apply, cut, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp
end PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
