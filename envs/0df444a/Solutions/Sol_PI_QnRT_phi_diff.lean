-- Prove2me | solution 1 for PI.QnRT.phi_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:47.515215+00:00
-- url     : https://prove2.me/submissions/d71c7bcb-124a-4f15-866c-5cd849fbcde5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_WColOther
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusConjugationRule_SecondHermitianPartDiagonal
import Theorems.Thm_PI_QnRT_w_diff
import Theorems.Thm_PI_QnRT_w_mul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.QnRT
variable {k r : ℕ}
namespace PI.QnRT
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) :
    DifferentiableAt ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf _ ⟨w_mul_mem l (c l) hc g₁ hg₁, hD⟩
  have hγ := w_diff l g₁ c hc
  have hFd : DifferentiableAt ℝ F (w1 k r l (c l) * g₁) :=
    (hF.differentiableOn (by first | simp | exact le_top | norm_num)).differentiableAt
      (hU.mem_nhds hgU)
  have hev1 : ∀ᶠ c' in 𝓝 c, w1 k r l (c' l) * g₁ ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  have hev2 : ∀ᶠ c' in 𝓝 c, c' l ≠ 0 := (continuous_apply l).continuousAt.eventually_ne hc
  have hev := hev1.and hev2
  refine (hFd.comp c hγ).congr_of_eventuallyEq ?_
  filter_upwards [hev] with c' hc'
  exact hfF _ hc'.1 (w_mul_mem l (c' l) hc'.2 g₁ hg₁)
end PI.QnRT
