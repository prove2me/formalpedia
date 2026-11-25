-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartChange_ae_split_edbb5f1af625
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:07:32.58279+00:00
-- url     : https://prove2.me/submissions/5233015a-8cbd-483b-9684-c2f196f161ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralIndep_proof_4b5bf5e5d261
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PosPartSplit_proof_e6248afef178
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1


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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChange
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartChange
theorem _root_.solution {K : Ideal (MvPolynomial (Fin n) ℂ)} {B : Matrix (Fin d) (Fin n) ℂ}
    (w : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) (F : ℕ → Set (Fin n → ℂ))
    (P : (Fin n → ℂ) → Prop) (hB : IsFiniteProjection K B) (hF : Pairwise (Function.onFun Disjoint F))
    (h0 : volume ((fun x => B *ᵥ x) '' {x | x ∈ zeroSet K ∧ (∃ s, IsSheetAt K B x s) ∧ ¬ P x}) = 0)
    (hc : ∀ x ∈ zeroSet K, (∃ s, IsSheetAt K B x s) → P x → ∃ k, x ∈ F k) :
    ∀ᵐ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy
  refine PosPartSplit.proof n d K B w ψ F y hB hF fun x hx hs => hc x hx.1 hs ?_
  by_contra hn
  exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
end GroundTheory.Heights₂.Heights.ChartChange
