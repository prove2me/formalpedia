-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeJacMeasurable_proof_d10b79c0fe5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:24.959843+00:00
-- url     : https://prove2.me/submissions/e93a3bf3-1855-4626-be1a-73cd8bf26790

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_coneJacMat_b0929fe06168
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneTangent_eq_ker_28afad4fe744
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneTangent_eq_bot_6b94c19276ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_starProjection_congr_5afb96649393
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_compressDet_649ceb054437
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneJac_eq_compressDet_7f1389046cce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isClosed_coneSet_ab7a54df5c4b


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
open MvPolynomial MeasureTheory Module
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ConeJacMeasurable
theorem _root_.solution (hComp : TangentJacCompress.Statement)
    (hKer : KernelProjMeasurable.Statement) : ConeJacMeasurable.Statement := by
  classical
  intro n m h J _ _ _ _
  refine Measurable.aemeasurable ?_
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian J)
  let P : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    (coneSet h J).piecewise
      (fun y => (LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y))).starProjection) 0
  have hP : Measurable P :=
    Measurable.piecewise (isClosed_coneSet h J).measurableSet
      (hKer (EuclideanSpace ℂ (Fin n)) n k _ (continuous_coneJacMat h g)) measurable_const
  have hTP : ∀ y, (coneTangent h J y).starProjection = P y := by
    intro y
    by_cases hy : y ∈ coneSet h J
    · simp only [P, Set.piecewise_eq_of_mem _ _ _ hy]
      exact starProjection_congr (coneTangent_eq_ker h g hg hy)
    · simp only [P, Set.piecewise_eq_of_notMem _ _ _ hy]
      rw [starProjection_congr (coneTangent_eq_bot h hy), Submodule.starProjection_bot]
      rfl
  have hJac : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => coneJac h J p.1 p.2) =
      fun p => compressDet p.1 (P p.2) := by
    funext p
    rw [coneJac_eq_compressDet hComp, hTP]
  have hM : Measurable fun q : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet q.1 q.2 :=
    (continuous_compressDet m).measurable
  have hM2 : Measurable fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => (p.1, P p.2) :=
    measurable_fst.prodMk (hP.comp measurable_snd)
  have hM3 := hM.comp hM2
  rw [hJac]
  exact hM3
end ConeJacMeasurable
end GroundTheory.Heights₂.Heights
