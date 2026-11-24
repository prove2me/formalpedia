-- Prove2me | solution 1 for P2M_PI_MirrorSection__ut_inv_c3f594f8935a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:12.531139+00:00
-- url     : https://prove2.me/submissions/3dc6db36-801b-488f-833b-30826238a82a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Theorems.Thm_P2M_PI_MirrorSection__det_ut_7f3e5f0304a5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) :
    u * u⁻¹ = 1 ∧ u⁻¹ * u = 1 ∧ u⁻¹ ∈ UTset m := by
  have hd : IsUnit u.det := by rw [det_ut hu]; exact isUnit_one
  have h1 : u * u⁻¹ = 1 := mul_nonsing_inv u hd
  have h2 : u⁻¹ * u = 1 := nonsing_inv_mul u hd
  have hbt : BlockTriangular u id := fun i j h => hu.1 i j h
  haveI := u.invertibleOfIsUnitDet hd
  have hbti : BlockTriangular u⁻¹ id := blockTriangular_inv_of_blockTriangular hbt
  refine ⟨h1, h2, fun i j hji => hbti hji, fun i => ?_⟩
  have e := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hu.2, one_mul, Matrix.one_apply_eq] at e
  · exact e
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hu.1 i l h, zero_mul]
    · rw [hbti h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.MirrorSection₂
