-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_open_image_off_discriminant_0e35fea895a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:16.133433+00:00
-- url     : https://prove2.me/submissions/d835d53f-1970-48d7-b217-67b0b08f3437

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
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mono


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
theorem _root_.solution (hinj : InjectiveHolomorphicOpen.Statement) {N k : ℕ}
    {I : Ideal (MvPolynomial (Fin N) ℂ)} {A : Matrix (Fin k) (Fin N) ℂ} {P : MvPolynomial (Fin k) ℂ}
    (hP : ∀ y : Fin k → ℂ, eval y P ≠ 0 → ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A y,
      ∃ (U : Set (Fin k → ℂ)) (V : Set (Fin N → ℂ)) (g : (Fin k → ℂ) → (Fin N → ℂ)),
        IsOpen U ∧ y ∈ U ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ g U ∧ g y = x ∧
          (∀ w ∈ U, A.mulVec (g w) = w) ∧ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V = g '' U)
    {V : Set (Fin k → ℂ)} {φ : (Fin k → ℂ) → Fin N → ℂ} (hV : IsOpen V) (hφ : DifferentiableOn ℂ φ V)
    (hφi : Set.InjOn φ V) (hφZ : Set.MapsTo φ V (zeroSetIn I)) {t : Fin k → ℂ} (ht : t ∈ V)
    (hPt : eval (A *ᵥ φ t) P ≠ 0) :
    ∃ O : Set (Fin N → ℂ), IsOpen O ∧ φ t ∈ O ∧ zeroSetIn I ∩ O ⊆ φ '' V := by
  obtain ⟨U0, V0, g, -, -, hV0, hzV0, -, -, hAg, hZV0⟩ := hP _ hPt (φ t) ⟨hφZ ht, rfl⟩
  have hAd : Differentiable ℂ (fun v : Fin N → ℂ => A *ᵥ v) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
  have hWo : IsOpen (V ∩ φ ⁻¹' V0) := hφ.continuousOn.isOpen_inter_preimage hV hV0
  have hkey : ∀ s ∈ V ∩ φ ⁻¹' V0, φ s = g (A *ᵥ φ s) := by
    intro s hs
    have hmem : φ s ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V0 := ⟨hφZ hs.1, hs.2⟩
    rw [hZV0] at hmem
    obtain ⟨u, hu, hgu⟩ := hmem
    rw [← hgu, hAg u hu]
  have hFd : DifferentiableOn ℂ (fun s => A *ᵥ φ s) (V ∩ φ ⁻¹' V0) :=
    hAd.comp_differentiableOn (hφ.mono Set.inter_subset_left)
  have hFi : Set.InjOn (fun s => A *ᵥ φ s) (V ∩ φ ⁻¹' V0) := fun s hs s' hs' hss' =>
    hφi hs.1 hs'.1 (by rw [hkey s hs, hkey s' hs']; exact congrArg g hss')
  have hΩ := hinj k _ _ hWo hFd hFi
  refine ⟨V0 ∩ (fun v => A *ᵥ v) ⁻¹' ((fun s => A *ᵥ φ s) '' (V ∩ φ ⁻¹' V0)),
    hV0.inter (hAd.continuous.isOpen_preimage _ hΩ), ⟨hzV0, t, ⟨ht, hzV0⟩, rfl⟩, ?_⟩
  rintro z ⟨hzZ, hzV0', s, hsW, hsz⟩
  have hmem : z ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ V0 := ⟨hzZ, hzV0'⟩
  rw [hZV0] at hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  refine ⟨s, hsW.1, ?_⟩
  rw [hkey s hsW]
  simp only at hsz
  rw [hsz, hAg u hu]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
