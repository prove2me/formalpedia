-- Prove2me | solution 1 for P2M_Formalism_CountingSumsFrames_segment_top_room__9bcf6696b84d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:45.074841+00:00
-- url     : https://prove2.me/submissions/a7770057-c97e-4520-80e4-d3f73e609089

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Theorems.Thm_Formalism_CountingSumsFrames_window_parameter_bounds
import Theorems.Thm_Formalism_CountingSumsFrames_derived_parameter_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : SegmentTopRoom := by
  intro p N N₁ r Y a b' Q La P A c o h hP hA0 hA hc ho
  obtain ⟨hY, hp, h2, hN, hN1, hlog, hLa0, hLa, h4, hba, h6, hK, hN', hN1', hQ, hb0⟩ := window_parameter_bounds h
  obtain ⟨hp9, hb27, hpb, h243, hpa, hKQ, hKa, hKQY, hK2QY⟩ := derived_parameter_bounds hY hp h4 hba h6 hK hQ hb0
  generalize (r : ℝ) + 1 = K at *
  generalize (p : ℝ) = pp at *
  have hK0 : 0 < K := by linarith
  have ha0 : 0 < a := by linarith
  have haP : 0 < a / P := by positivity
  have hb9 : b' ≤ a / 9 := by
    have : 9 * b' ≤ pp * b' := by gcongr
    linarith
  have hbP : b' / P ≤ a / P / 9 := by
    calc b' / P ≤ a / 9 / P := by gcongr
      _ = a / P / 9 := by ring
  have hp2 : (81 : ℝ) ≤ pp ^ 2 := by
    calc (81 : ℝ) = 9 ^ 2 := by norm_num
      _ ≤ pp ^ 2 := by gcongr
  have h4p : 4 / pp ^ 2 ≤ 4 / 81 := by gcongr
  have c1 : A * (1 + 4 / pp ^ 2) ≤ 0.25 * (a / P) := by
    calc A * (1 + 4 / pp ^ 2) ≤ (3 * b' / (2 * P)) * (1 + 4 / 81) := by gcongr
      _ = 85 / 54 * (b' / P) := by field_simp; ring
      _ ≤ 85 / 54 * (a / P / 9) := by gcongr
      _ ≤ 0.25 * (a / P) := by norm_num; linarith
  have c2 : a / (pp * P) + (3 * b' / 2) / ((pp ^ 2 - 1) * P) ≤ 0.12 * (a / P) := by
    have d1 : a / (pp * P) ≤ a / (9 * P) := by gcongr
    have d2 : (3 * b' / 2) / ((pp ^ 2 - 1) * P) ≤ (3 * b' / 2) / (80 * P) := by
      gcongr; linarith
    have d3 : a / (9 * P) = a / P / 9 := by field_simp
    have d4 : (3 * b' / 2) / (80 * P) = 3 / 160 * (b' / P) := by field_simp; ring
    have d5 : 3 / 160 * (b' / P) ≤ 3 / 160 * (a / P / 9) := by gcongr
    norm_num
    linarith
  refine ⟨c1, c2, ?_⟩
  have c3 : La * c / K ≤ 0.12 * (a / P) := by
    rw [div_le_iff₀ hK0]
    calc La * c ≤ La * (0.12 * (a / P)) := by gcongr; linarith
      _ ≤ K * (0.12 * (a / P)) := by gcongr
      _ = 0.12 * (a / P) * K := by ring
  norm_num at c1 c3 ⊢
  linarith
end Formalism.CountingSumsFrames
