-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sum_eq_of_transversal_49c02c2d25ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:18.756067+00:00
-- url     : https://prove2.me/submissions/1148b07a-d3e7-4b9d-8ac5-6859b6df58ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveDegreeVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveDegreeVert
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sameOrbit_refl_a2f42243f46b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sameOrbit_symm_6e2327b721fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveDegreeVert_sameOrbit_trans_b1bff1cd0f76

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
theorem _root_.solution {P : Ideal (MRing ι)} {R R' : Finset ((Σ k, ι k) → ℂ)}
    (hRP : ∀ t ∈ R, t ∈ mcPts P) (hRu : ∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t)
    (hR'P : ∀ t ∈ R', t ∈ mcPts P) (hR'u : ∀ z ∈ mcPts P, ∃! t, t ∈ R' ∧ SameOrbit z t)
    (h : ((Σ k, ι k) → ℂ) → ℝ) (hh : ∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') :
    ∑ t ∈ R, h t = ∑ t ∈ R', h t := by
  refine Finset.sum_bij (fun t ht => (hR'u t (hRP t ht)).exists.choose)
    (fun t ht => (hR'u t (hRP t ht)).exists.choose_spec.1) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ he
    have e1 := (hR'u t₁ (hRP t₁ h₁)).exists.choose_spec.2
    have e2 := (hR'u t₂ (hRP t₂ h₂)).exists.choose_spec.2
    rw [he] at e1
    exact (hRu t₂ (hRP t₂ h₂)).unique ⟨h₁, sameOrbit_trans e2 (sameOrbit_symm e1)⟩ ⟨h₂, sameOrbit_refl t₂⟩
  · intro t' ht'
    obtain ⟨t, ⟨htR, hto⟩, -⟩ := hRu t' (hR'P t' ht')
    exact ⟨t, htR, (hR'u t (hRP t htR)).unique (hR'u t (hRP t htR)).exists.choose_spec
      ⟨ht', sameOrbit_symm hto⟩⟩
  · intro t ht
    exact hh _ _ (hRP t ht) (hR'u t (hRP t ht)).exists.choose_spec.2
end GroundTheory.Heights₂.Heights.Targets.CurveDegreeVert
