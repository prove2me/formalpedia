-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.key2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:08:39.320799+00:00
-- url     : https://prove2.me/submissions/11f96307-eae6-4c5a-a866-2759a944d766

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_DetMEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (q : ℕ) (γ x : EuclideanSpace ℂ ι) :
    cexp (q * Real.pi * Hf x γ + q * Real.pi * Hf γ γ / 2) * ((paW q (x + γ) : ℝ) : ℂ) =
      ((paW q x : ℝ) : ℂ) * (starRingEnd ℂ) (cexp (q * Real.pi * Hf x (-γ) - q * Real.pi * Hf (-γ) (-γ) / 2)) := by
  have hH : ∀ v w : EuclideanSpace ℂ ι, Hf v w = inner ℂ w v := fun v w => by
    rw [Hf, PiLp.inner_apply]
    try rfl
  have hn : ∀ v : EuclideanSpace ℂ ι, ((‖v‖ ^ 2 : ℝ) : ℂ) = inner ℂ v v := fun v => by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    first
    | rfl
    | simp
    | norm_cast
  have hexp : ∀ r : ℝ, ((Real.exp r : ℝ) : ℂ) = cexp (r : ℂ) := fun r => Complex.ofReal_exp r
  simp only [paW, hH, hexp]
  rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h1 : ((-(↑q * Real.pi) * ‖x + γ‖ ^ 2 : ℝ) : ℂ) =
      -((q : ℂ) * Real.pi) * inner ℂ (x + γ) (x + γ) := by
    rw [← hn]
    push_cast
    ring
  have h2 : ((-(↑q * Real.pi) * ‖x‖ ^ 2 : ℝ) : ℂ) = -((q : ℂ) * Real.pi) * inner ℂ x x := by
    rw [← hn]
    push_cast
    ring
  rw [h1, h2]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, map_sub, map_mul,
    map_div₀, map_neg, Complex.conj_ofReal, map_natCast, map_ofNat, inner_conj_symm, neg_neg]
  ring
end ReciprocityTheory.ChartRestriction.G.I2.FPw
