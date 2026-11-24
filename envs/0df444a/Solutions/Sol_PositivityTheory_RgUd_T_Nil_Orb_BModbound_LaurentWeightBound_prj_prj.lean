-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.prj_prj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:51.149276+00:00
-- url     : https://prove2.me/submissions/eee7f8d9-c5ea-42e1-bce6-e68b17cfecad

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
theorem _root_.solution (P : GL (Fin n) k) (w : Fin n → ℤ) (m : ℤ) (y : Fin n → k) :
    prj P w m (prj P w m y) = prj P w m y := by
  rw [prj, inv_mulVec_prj]
  congr 1
  ext i
  simp only [cut]
  split_ifs <;> rfl
end PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
