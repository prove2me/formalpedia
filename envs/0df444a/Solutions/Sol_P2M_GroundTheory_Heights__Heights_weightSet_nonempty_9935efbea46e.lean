-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_weightSet_nonempty_9935efbea46e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:51.882795+00:00
-- url     : https://prove2.me/submissions/2c898a6a-8e69-4bd8-a30c-514b4f52a068

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {p : MvPolynomial σ R} (hp : p ≠ 0) : (weightSet w p).Nonempty := by
  classical
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hp)
  exact ⟨_, mem_weightSet.mpr ⟨d, hd, rfl⟩⟩
end GroundTheory.Heights₂.Heights
