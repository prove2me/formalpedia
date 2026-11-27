-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:49.738198+00:00
-- url     : https://prove2.me/submissions/7f11d681-6839-4b98-a777-e49949d1f385

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Bump_zero
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Dat_pow
import Theorems.Thm_PositivityTheory_ThKEnd_Two_kill_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]
namespace PositivityTheory.ThKEnd.Two
theorem _root_.solution (hC : Cusp Γ n a) (hn : Continuous n) (hl : ‖l‖ < 1) {m : ℕ} (h : Dat Γ n a lam l φ c) (hm : Gr a m φ) (g : G) :
    c (a * g) = c g := by
  refine kill_ind (Measure.haar) hC hn hl (fun _ c => ∀ g, c (a * g) = c g) (fun φ c h ⟨M, hM⟩ g => ?_) (fun φ c h h1 g => ?_) m φ c h hm g
  · have hc : ∀ g, ‖c g‖ ≤ M := fun g => by
      rw [h.av]
      simpa using norm_integral_le_of_norm_le_const (μ := lam) (.of_forall fun x => hM (n x * g))
    have t : Tendsto (fun k : ℕ => ‖l‖ ^ k * (M + M)) atTop (𝓝 (0 * (M + M))) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg l) hl).mul_const _
    rw [zero_mul] at t
    refine sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' t fun k => ?_))
    have := h.pow k ((a ^ k)⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    rw [this, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hc _) (hc _))) (by positivity)
  · have := h.contc
    refine sub_eq_zero.1 (Bump.zero Measure.haar (fun g => c (a * g) - c g) (by fun_prop) g fun V hV => ?_)
    obtain ⟨η, a1, a2⟩ := h1 V hV
    refine ⟨η, a1, ?_⟩
    rw [← sub_eq_zero.2 (a2 g), conv, conv, conv, ← integral_sub (a1.int _ h.contc _) (a1.int _ h.contc _)]
    simp only [sub_mul, mul_assoc]
end PositivityTheory.ThKEnd.Two
