-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatChartChangeVar_ratPosDens_split_c1d7b98829fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:59.435101+00:00
-- url     : https://prove2.me/submissions/2d4797a8-2252-4a70-ac4b-0269adb41611

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatChartChangeVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSheetNoRatNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatChartChangeVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
open GroundTheory.Heights₂.Heights.RatChartChangeVar
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.RatChartChangeVar
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (E : ℕ → Set (Fin n → ℂ)) (y : Fin d → ℂ) (hfin : (RatChart.ratFibre J p q y).Finite)
    (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ x ∈ RatChart.ratFibre J p q y, (∃ s, RatChart.IsRatSheetAt J p q x s) → ∃ k, x ∈ E k) :
    ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∑' k, ENNReal.ofReal (RatChart.ratPosDens J p q ((E k).indicator f) φ y) := by
  classical
  unfold RatChart.ratPosDens RatChart.ratSheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x =>
    if h : ∃ s, RatChart.IsRatSheetAt J p q x s then
      max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT
  have hT0 : ∀ g x, 0 ≤ T g x := fun g x => by
    simp only [hT]; split_ifs <;> simp
  have hpt : ∀ x ∈ hfin.toFinset,
      ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x) := by
    intro x hx
    have hx' : x ∈ RatChart.ratFibre J p q y := hfin.mem_toFinset.mp hx
    by_cases hs : ∃ s, RatChart.IsRatSheetAt J p q x s
    · obtain ⟨k₀, hk₀⟩ := hcov x hx' hs
      rw [tsum_eq_single k₀]
      · simp only [hT, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : x ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [hT, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [hT, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm
end GroundTheory.Heights₂.Heights.RatChartChangeVar
