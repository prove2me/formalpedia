-- Prove2me | solution 1 for ZetaZeros.D.EllReg.localSobolev_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:09:59.895605+00:00
-- url     : https://prove2.me/submissions/39744815-37cb-4c3d-86d6-1c0e7d3734ef

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllReg
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {d : ℕ}
namespace ZetaZeros.D.EllReg
theorem _root_.solution (hB : BaseLevel) (hC : CutCont) (hS : Step) : LocalSobolev := by
  intro d ι _ P U u hH x0 hx0
  obtain ⟨r, hr, hrU, hstep⟩ := hS d ι P U u hH x0 hx0
  refine ⟨r, hr, hrU, ?_⟩
  have key : ∀ n : ℕ, ∀ χ : E d → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ ball x0 r →
      Hs ((-(d : ℝ) - 1) + n) (cut χ u) := by
    intro n
    induction n with
    | zero =>
      intro χ hχ hχc hχs
      have h := (hC d U u χ hH.1 hH.2.2.2.1 hχ hχc (hχs.trans hrU))
      simpa using hB d (cut χ u) h.1 h.2
    | succ n ih =>
      intro χ hχ hχc hχs
      have := hstep ((-(d : ℝ) - 1) + n) ih χ hχ hχc hχs
      simpa [Nat.cast_succ, add_assoc] using this
  intro χ hχ hχc hχs s
  have h := key (s + d + 1) χ hχ hχc hχs
  have e : (-(d : ℝ) - 1) + ((s + d + 1 : ℕ) : ℝ) = (s : ℝ) := by push_cast; ring
  rw [e] at h
  exact h
end ZetaZeros.D.EllReg
