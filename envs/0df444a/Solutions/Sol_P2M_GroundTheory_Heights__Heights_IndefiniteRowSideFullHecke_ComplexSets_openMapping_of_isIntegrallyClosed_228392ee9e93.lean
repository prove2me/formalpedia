-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_openMapping_of_isIntegrallyClosed_228392ee9e93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:54:37.333115+00:00
-- url     : https://prove2.me/submissions/ccefa3f3-08db-4b35-a25d-179810a37625

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericProjectionFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDiscriminantCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelOpenMapping
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isFiniteProjection_d36cfd18aee8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_open_image_off_discriminant_0e35fea895a1
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mono
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsExists_proof_791d6fddc3f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsFinite_proof_1e0c84911ab6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_ConeAvoidsOpen_proof_265a021d820f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_DiscriminantCover_proof_5ee235c71037
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_eval_pullback_d784c0eada3b
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


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (hirr : NormalLocallyIrreducible.Statement)
    (hoff : BranchOffHypersurface.Statement) (hinj : InjectiveHolomorphicOpen.Statement) {N k : ℕ}
    (I : Ideal (MvPolynomial (Fin N) ℂ)) (hI : I.IsPrime) (hic : IsIntegrallyClosed (MvPolynomial (Fin N) ℂ ⧸ I))
    (hdim : ringKrullDim (MvPolynomial (Fin N) ℂ ⧸ I) = (k : ℕ)) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin N → ℂ) (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hφi : Set.InjOn φ U)
    (hφZ : Set.MapsTo φ U (zeroSetIn I)) :
    ∃ O : Set (Fin N → ℂ), IsOpen O ∧ φ '' U = zeroSetIn I ∩ O := by
  obtain ⟨A, hA⟩ := exists_isFiniteProjection I hI hdim
  obtain ⟨P, hP0, hP⟩ := GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof
    GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof N k I A hI hdim hA
  set h := GroundTheory.Heights₂.Heights.ComplexSets.pullback A P with hh
  have hhe : ∀ z, eval z h = eval (A *ᵥ z) P := fun z =>
    GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.eval_pullback A z P
  have hhI : h ∉ I := by
    intro hmem
    apply hP0
    apply hA.injective
    rw [map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
  have hP' := fun y hy => (hP y hy).2.2
  have hloc : ∀ τ ∈ U, ∃ B : Set (Fin N → ℂ), IsOpen B ∧ φ τ ∈ B ∧ zeroSetIn I ∩ B ⊆ φ '' U := by
    intro τ hτ
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU τ hτ
    have hr0 : 0 < ε / 2 := by positivity
    have hKU : Metric.closedBall τ (ε / 2) ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεU
    have hVU : Metric.ball τ (ε / 2) ⊆ U := Metric.ball_subset_closedBall.trans hKU
    have hKc : IsCompact (φ '' Metric.closedBall τ (ε / 2)) :=
      (isCompact_closedBall τ (ε / 2)).image_of_continuousOn (hφ.continuousOn.mono hKU)
    have hSc : IsCompact (φ '' Metric.sphere τ (ε / 2)) :=
      (isCompact_sphere τ (ε / 2)).image_of_continuousOn
        (hφ.continuousOn.mono (Metric.sphere_subset_closedBall.trans hKU))
    have hwS : φ τ ∉ φ '' Metric.sphere τ (ε / 2) := by
      rintro ⟨s, hs, hsτ⟩
      have hst := hφi (Metric.sphere_subset_closedBall.trans hKU hs) hτ hsτ
      rw [hst, Metric.mem_sphere, dist_self] at hs
      exact hr0.ne hs
    obtain ⟨B, hBo, hwB, hBS, hpre, hdense⟩ := hirr (Fin N) I h (φ τ) hI hic hhI (hφZ hτ)
      (φ '' Metric.sphere τ (ε / 2))ᶜ (hSc.isClosed.isOpen_compl.mem_nhds hwS)
    set G := ⋃₀ {O : Set (Fin N → ℂ) | IsOpen O ∧ zeroSetIn I ∩ O ⊆ φ '' Metric.ball τ (ε / 2)} with hG
    have hGo : IsOpen G := isOpen_sUnion fun O hO => hO.1
    have hGZ : zeroSetIn I ∩ G ⊆ φ '' Metric.ball τ (ε / 2) := by
      rintro z ⟨hzZ, O, hO, hzO⟩
      exact hO.2 ⟨hzZ, hzO⟩
    have hVK : φ '' Metric.ball τ (ε / 2) ⊆ φ '' Metric.closedBall τ (ε / 2) :=
      Set.image_mono Metric.ball_subset_closedBall
    obtain ⟨t0, ⟨ht0V, ht0B⟩, ht0h⟩ := hoff N k I h (Metric.ball τ (ε / 2) ∩ φ ⁻¹' B) φ hI hdim hhI
      ((hφ.continuousOn.mono hVU).isOpen_inter_preimage Metric.isOpen_ball hBo)
      ⟨τ, Metric.mem_ball_self hr0, hwB⟩ (hφ.mono (Set.inter_subset_left.trans hVU))
      (hφi.mono (Set.inter_subset_left.trans hVU)) (fun s hs => hφZ (hVU hs.1))
    have hcover : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ G ∪ (φ '' Metric.closedBall τ (ε / 2))ᶜ := by
      rintro z ⟨⟨hzZ, hzB⟩, hzh⟩
      by_cases hzK : z ∈ φ '' Metric.closedBall τ (ε / 2)
      · left
        obtain ⟨s, hsK, rfl⟩ := hzK
        have hsV : s ∈ Metric.ball τ (ε / 2) := by
          rcases (Metric.mem_closedBall.1 hsK).lt_or_eq with hlt | heq
          · exact hlt
          · exact absurd ⟨s, heq, rfl⟩ (hBS hzB)
        obtain ⟨O, hOo, hsO, hOZ⟩ := open_image_off_discriminant hinj hP' Metric.isOpen_ball
          (hφ.mono hVU) (hφi.mono hVU) (fun s hs => hφZ (hVU hs)) hsV (by rw [← hhe]; exact hzh)
        exact ⟨O, ⟨hOo, hOZ⟩, hsO⟩
      · exact Or.inr hzK
    have hdisj : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ∩ (G ∩ (φ '' Metric.closedBall τ (ε / 2))ᶜ) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun z ⟨⟨⟨hzZ, _⟩, _⟩, hzG, hzK⟩ => hzK (hVK (hGZ ⟨hzZ, hzG⟩))
    have hDG : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ G := by
      rcases isPreconnected_iff_subset_of_disjoint.1 hpre _ _ hGo hKc.isClosed.isOpen_compl hcover hdisj
        with h1 | h1
      · exact h1
      · exact absurd (hVK ⟨t0, ht0V, rfl⟩) (h1 ⟨⟨hφZ (hVU ht0V), ht0B⟩, ht0h⟩)
    have hDK : (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.closedBall τ (ε / 2) :=
      fun z hz => hVK (hGZ ⟨hz.1.1, hDG hz⟩)
    exact ⟨B, hBo, hwB, fun z hz =>
      Set.image_mono hKU (closure_minimal hDK hKc.isClosed (hdense hz))⟩
  refine ⟨⋃₀ {O : Set (Fin N → ℂ) | IsOpen O ∧ zeroSetIn I ∩ O ⊆ φ '' U},
    isOpen_sUnion fun O hO => hO.1, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨B, hBo, hτB, hBU⟩ := hloc τ hτ
    exact ⟨hφZ hτ, B, ⟨hBo, hBU⟩, hτB⟩
  · rintro z ⟨hzZ, O, hO, hzO⟩
    exact hO.2 ⟨hzZ, hzO⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
