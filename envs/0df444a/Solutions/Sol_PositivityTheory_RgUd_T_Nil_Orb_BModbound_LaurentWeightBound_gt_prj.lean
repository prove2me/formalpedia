-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.gt_prj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:51.126703+00:00
-- url     : https://prove2.me/submissions/403f4026-1215-4942-80a6-c1d48c07108e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BModbound_LaurentWeightBound_inv_mulVec_prj

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
theorem _root_.solution (P : GL (Fin n) k) (w : Fin n → ℤ) (t : kˣ) (m : ℤ) (y : Fin n → k) :
    gt P w t *ᵥ prj P w m y = ((t ^ m : kˣ) : k) • prj P w m y := by
  rw [gt, ← mulVec_mulVec, ← mulVec_mulVec, inv_mulVec_prj, prj, ← mulVec_smul]
  congr 1
  ext i
  simp only [mulVec_diagonal, cut, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [h]
  · simp
end PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
