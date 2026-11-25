-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integrable_chartDens_b4865e99a51f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:51.284144+00:00
-- url     : https://prove2.me/submissions/48d5fa16-f35a-432d-86ec-78481ad99311

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_chartDens_le_fe914f30ce28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionCluster_proof_477bb4961448
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelProper_proof_63b250feae60
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.RegLelongAnnulus
variable {n m : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin m) (Fin n) ℂ}
variable (hCM : ChartMassCompact.Statement) (hJ : J.IsPrime)
  (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (m : ℕ)) (hA : IsFiniteProjection J A)
include hCM hJ hdim hA
namespace GroundTheory.Heights₂.Heights.RegLelongAnnulus
theorem _root_.solution {φ : Fin m → (Fin n → ℂ) → ℝ} (hφ : ∀ k, SmoothNear (zeroSet J) (φ k))
    {f : (Fin n → ℂ) → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {C : ℝ} (hC : 0 ≤ C)
    {w : (Fin n → ℂ) → ℝ} (hwm : Measurable w) (hb : ∀ z, |w z| ≤ C * f z) :
    Integrable (chartDens J A w φ) :=
  ((hCM n m J A f φ hJ hdim hA hf.continuousOn hφ (Or.inl hfc)).const_mul C).mono'
    (SheetSumMeasurable.proof n m J A w φ hJ hdim hA hwm hφ).1.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_chartDens_le hA hC hb φ y)
end GroundTheory.Heights₂.Heights.RegLelongAnnulus
