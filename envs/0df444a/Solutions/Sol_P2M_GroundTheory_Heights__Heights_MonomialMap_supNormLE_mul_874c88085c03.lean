-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_mul_874c88085c03
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:37.330388+00:00
-- url     : https://prove2.me/submissions/6e106062-d5c9-47b8-bc44-bc82e533dd99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_mul_b675f81d17d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_evalCone_chartMonomial_ne_zero_f3bbdf95a0d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_live_of_point_dc057d7f8053
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_chart_value_eq_f30369e8f416
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_ratio_norm_eq_693ade00c38c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_mul_5bfd3b05f445


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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n}
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution (A B : HermLine n) (s : IntegralSection P A.deg) (t : IntegralSection P B.deg)
    {C C' : ℝ} (hs : s.SupNormLE A C) (ht : t.SupNormLE B C') :
    IntegralSection.SupNormLE (A.mul B) (s.mul t) (C + C') := by
  intro z hz c d e he hc
  have live := live_of_point hz hc
  obtain ⟨d₁, e₁, he₁⟩ := s.regular c live
  obtain ⟨d₂, e₂, he₂⟩ := t.regular c live
  have hmem : s.den * t.den * (e₁ * e₂) - s.num * t.num * chartMonomial c (d₁ + d₂) ∈ P.ideal := by
    rw [chartMonomial_add]
    have hid : s.den * t.den * (e₁ * e₂) - s.num * t.num * (chartMonomial c d₁ * chartMonomial c d₂) =
        (s.den * e₁ - s.num * chartMonomial c d₁) * (t.den * e₂) +
          (s.num * chartMonomial c d₁) * (t.den * e₂ - t.num * chartMonomial c d₂) := by ring
    rw [hid]
    exact P.ideal.add_mem (P.ideal.mul_mem_right _ he₁.2) (P.ideal.mul_mem_left _ he₂.2)
  have hv := chart_value_eq (s.mul t).den_not_mem he.2 hmem hz
  have hA := hs z hz c d₁ e₁ he₁ hc
  have hB := ht z hz c d₂ e₂ he₂ hc
  change ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * (A.metric z * B.metric z)) ≤ _
  rw [ratio_norm_eq (evalCone_chartMonomial_ne_zero z c d hc)
    (evalCone_chartMonomial_ne_zero z c _ hc) hv, evalCone_mul, chartMonomial_add, evalCone_mul,
    norm_mul, norm_mul, Real.exp_add]
  have hid : ‖evalCone z e₁‖ * ‖evalCone z e₂‖ /
      (‖evalCone z (chartMonomial c d₁)‖ * ‖evalCone z (chartMonomial c d₂)‖ * (A.metric z * B.metric z)) =
      (‖evalCone z e₁‖ / (‖evalCone z (chartMonomial c d₁)‖ * A.metric z)) *
        (‖evalCone z e₂‖ / (‖evalCone z (chartMonomial c d₂)‖ * B.metric z)) := by
    rw [div_mul_div_comm]; ring_nf
  rw [hid]
  exact mul_le_mul hA hB
    (div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (B.metric_pos z hz.1).le))
    (Real.exp_pos _).le
end GroundTheory.Heights₂.Heights.MonomialMap
