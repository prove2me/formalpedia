-- Prove2me | solution 1 for P2M_GlobalTheory_ProjSpace_chart__baseChange_4f839b0b071b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:07.722796+00:00
-- url     : https://prove2.me/submissions/1e115c90-ace6-4b0e-aa66-f5decfd9a719

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Theorems.Thm_GlobalTheory_ProjSpace_gradedMap_apply
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply


attribute [local simp] GlobalTheory.ProjSpace.gradedMap_apply

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable (R : Type) [CommRing R] (N : ℕ)
variable {R N}
variable (R N)
variable {R N}
variable (R N)
variable {R} {R' : Type} [CommRing R'] (φ : R →+* R')
namespace GlobalTheory.ProjSpace
theorem _root_.solution (i : Fin (N + 1)) :
    chartι R' N i ≫ baseChange N φ =
      spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _) ≫ chartι R N i := by
  have key : ∀ (s : MvPolynomial (Fin (N + 1)) R') (hs : s = X i) (hd : s ∈ grading R' N 1),
      ∃ ψ : HomogeneousLocalization.Away (grading R' N) s →+* MvPolynomial {j // j ≠ i} R',
        chartι R' N i = spMap ψ ≫ Proj.awayι (grading R' N) s hd one_pos ∧
        ∀ n f hf, ψ (HomogeneousLocalization.Away.mk (grading R' N) hd n f hf) = dehom R' N i f := by
    rintro _ rfl hd
    exact ⟨awayToPoly R' N i, rfl, awayToPoly_mk R' N i⟩
  obtain ⟨ψ, h1, h2⟩ := key (gradedMap N φ (X i)) (map_X φ i) ((gradedMap N φ).2 (X_mem R N i))
  rw [h1, Category.assoc, baseChange, Proj.awayι_comp_map _ _ one_pos _ (X_mem R N i), chartι,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext1
  refine RingHom.ext fun x => ?_
  obtain ⟨n, f, hf, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (X_mem R N i) x
  change ψ (HomogeneousLocalization.Away.map (gradedMap N φ) (X i) _) =
    MvPolynomial.map φ (awayToPoly R N i _)
  rw [HomogeneousLocalization.Away.map_mk, h2, awayToPoly_mk]
  have : (RingHomClass.toRingHom (dehom R' N i)).comp (MvPolynomial.map φ) =
      (MvPolynomial.map φ).comp (RingHomClass.toRingHom (dehom R N i)) := by
    refine ringHom_ext (fun r => by simp) (fun j => ?_)
    by_cases h : j = i <;> simp [dehom, h]
  exact congrArg (fun φ => φ f) this
end GlobalTheory.ProjSpace
