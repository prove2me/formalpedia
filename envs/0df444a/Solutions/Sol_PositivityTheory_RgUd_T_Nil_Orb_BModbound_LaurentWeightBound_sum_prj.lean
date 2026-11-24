-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.sum_prj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:51.370085+00:00
-- url     : https://prove2.me/submissions/39ec058f-33a9-4fef-90b1-3ef84dc52f84

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_LaurentWeightBound_gt_mulVec

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
theorem _root_.solution (P : GL (Fin n) k) (w : Fin n → ℤ) (y : Fin n → k) :
    ∑ m ∈ Finset.univ.image w, prj P w m y = y := by
  have h := gt_mulVec P w 1 y
  have hg : gt P w 1 = 1 := by
    simp only [gt, _root_.one_zpow, Units.val_one]
    rw [diagonal_one, mul_one, Units.mul_inv]
  rw [hg, one_mulVec] at h
  simpa using h.symm
end PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
