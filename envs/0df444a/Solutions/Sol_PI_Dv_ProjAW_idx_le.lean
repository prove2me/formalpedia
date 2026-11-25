-- Prove2me | solution 1 for PI.Dv.ProjAW.idx_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:53:56.680807+00:00
-- url     : https://prove2.me/submissions/028b6764-6d46-433d-9d17-7ba3df9b51b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_IdxEqLen
import Theorems.Thm_PI_Dv_ProjAW_fg_cut
import Theorems.Thm_PI_Dv_ProjAW_fg_img
import Theorems.Thm_PI_Dv_ProjAW_part1
import Theorems.Thm_PI_Dv_ProjAW_part2
import Theorems.Thm_PI_Dv_ProjAW_rk_img
import Theorems.Thm_PI_Dv_ProjAW_span_cut_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution (hI : IdxCalc) (hG : A.Good) {f : Module.End K A.V} (hf : f * f = f) {n : ℕ}
    (hn0 : 0 < n) (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) (w : HeightOneSpectrum (𝓞 K)) :
    idxAt w (imgE A f A.L) (cutE A f A.L) ≤ (dimE A f : ℤ) * vAdd w ((n : ℕ) : K) := by
  have h := (hI K A.V w (imgE A f A.L) (cutE A f A.L) (fg_img A hG f) (fg_cut A hG f)
    (span_cut_eq A hf hn0 hn)).2.2.2.2.2 n hn0 (part2 A hf) (part1 A hn)
  rwa [rk_img A hG f] at h
end PI.Dv.ProjAW
