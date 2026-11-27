-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalCurveRegularPoint_proof_bb10d4225231
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:05:31.037321+00:00
-- url     : https://prove2.me/submissions/0296510f-1a7b-4c9e-b471-8df016869e1b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveRegularPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveJacobian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCurveRegularPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalCurveRegularPoint_fderiv_eval_single_e2e36c26b6f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsExists_proof_791d6fddc3f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsFinite_proof_1e0c84911ab6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsOpen_proof_265a021d820f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_DiscriminantCover_proof_5ee235c71037
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjHomInjective_proof_a56a3c2f38d9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FiniteProjectionsContainOpen_proof_15145ee0a27d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_GenericProjectionFinite_proof_8dc043b44cde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_HomogDimZeroPow_proof_57ceec37771d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_LeadIdealDim_proof_02c6e2a8e310
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_LinearFormCut_proof_0748af3de968
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveElementFibres_proof_bedd125def68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_SimpleRootBranch_proof_ccd25a0d5bfd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_proof_ee9a0946a210
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticImplicitChart_proof_243fc403b1d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelOpenMapping_proof_6e043588db91


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
namespace GroundTheory.Heights₂.Heights
namespace NormalCurveRegularPoint
theorem _root_.solution (hJ : NormalCurveJacobian.Statement) : NormalCurveRegularPoint.Statement := by
  classical
  intro σ _ I w hI hnorm hdim hw
  obtain ⟨k, f, D, hk, hfI, hlin, hD, hgen⟩ := hJ σ I w hI hnorm hdim hw
  set W : Set (σ → ℂ) := {z | eval z D ≠ 0}
  have hWo : IsOpen W := isOpen_ne_fun (continuous_eval D) continuous_const
  have hder : ∀ j, (fun i : σ => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w (Pi.single i 1)) =
      fun i => eval w (pderiv i (f j)) := fun j => funext fun i =>
    NormalCurveRegularPoint.fderiv_eval_single (f j) w i
  let Φ : ((σ → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (σ → ℂ) :=
    { toFun := fun L i => L (Pi.single i 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hlin' : LinearIndependent ℂ (fun j => fderiv ℂ (fun z : σ → ℂ => eval z (f j)) w) := by
    refine LinearIndependent.of_comp Φ ?_
    convert hlin using 1
    funext j
    exact hder j
  obtain ⟨d, A, O, V, g, hd, hO, hV, hwV, hVW, hg, hAg, hset⟩ :=
    IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.proof σ (Fin k) (fun j z => eval z (f j)) w W
      (fun j => AnalyticOnNhd.eval_mvPolynomial (f j) w trivial) (fun j => hw _ (hfI j)) hlin'
      (hWo.mem_nhds hD)
  simp only [Fintype.card_fin] at hd
  obtain rfl : d = 1 := by omega
  refine ⟨A, O, V, g, hO, hV, hwV, hg, hAg, ?_⟩
  rw [← hset]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hzV⟩
    exact ⟨hzV, fun j => hz _ (hfI j)⟩
  · rintro ⟨hzV, hzf⟩
    refine ⟨fun q hq => ?_, hzV⟩
    have hspan : Ideal.span (Set.range f) ≤ RingHom.ker (eval z) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hzf j
    have h0 : eval z (D * q) = 0 := hspan (hgen q hq)
    rw [eval_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hVW hzV)
end NormalCurveRegularPoint
end GroundTheory.Heights₂.Heights
