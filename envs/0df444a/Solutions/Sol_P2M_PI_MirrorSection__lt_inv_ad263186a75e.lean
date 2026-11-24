-- Prove2me | solution 1 for P2M_PI_MirrorSection__lt_inv_ad263186a75e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:49:43.471543+00:00
-- url     : https://prove2.me/submissions/3247c79d-cf52-4a7f-aa8a-d14890227369

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Theorems.Thm_P2M_PI_MirrorSection__det_ut_7f3e5f0304a5
import Theorems.Thm_P2M_PI_MirrorSection__ut_conjTranspose_65da1bf78ca4
import Theorems.Thm_P2M_PI_MirrorSection__lt_conjTranspose_880787298ed1
import Theorems.Thm_P2M_PI_MirrorSection__ut_inv_c3f594f8935a

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
theorem _root_.solution {l : Matrix (Fin m) (Fin m) ℂ} (hl : l ∈ LTset m) :
    l * l⁻¹ = 1 ∧ l⁻¹ * l = 1 ∧ l⁻¹ ∈ LTset m := by
  have hu := ut_inv (lt_conjTranspose hl)
  have hd : IsUnit l.det := by
    have := det_ut (lt_conjTranspose hl)
    rw [det_conjTranspose] at this
    have h2 : l.det = 1 := by simpa using congrArg star this
    rw [h2]; exact isUnit_one
  refine ⟨mul_nonsing_inv l hd, nonsing_inv_mul l hd, ?_⟩
  have := ut_conjTranspose hu.2.2
  rwa [conjTranspose_nonsing_inv, conjTranspose_conjTranspose] at this
end PI.MirrorSection₂
