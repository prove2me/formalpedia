-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FubiniStudySmooth_contDiffAt_blockNorm_76253190e502
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:18.383889+00:00
-- url     : https://prove2.me/submissions/c8d09558-2f4d-4a5a-9525-5483e9f9218c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsLineSmooth

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
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.FubiniStudySmooth
namespace GroundTheory.Heights₂.Heights.FubiniStudySmooth
theorem _root_.solution {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k : K)
    (z : (Σ k, ι k) → ℂ) (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => ‖WithLp.toLp 2 (fun i => w ⟨k, i⟩)‖) z := by
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => WithLp.toLp 2 (fun i => w ⟨k, i⟩)) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))
  have hne : WithLp.toLp 2 (fun i => z ⟨k, i⟩) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    intro h0
    exact hi (by simpa using congrArg (fun v : WithLp 2 (ι k → ℂ) => v.ofLp i) h0)
  exact (contDiffAt_norm ℂ hne).comp z hL.contDiffAt
end GroundTheory.Heights₂.Heights.FubiniStudySmooth
