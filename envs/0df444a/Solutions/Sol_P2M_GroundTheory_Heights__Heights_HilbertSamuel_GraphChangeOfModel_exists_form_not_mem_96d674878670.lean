-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GraphChangeOfModel_exists_form_not_mem_96d674878670
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:37.680855+00:00
-- url     : https://prove2.me/submissions/4625fd20-c064-46e0-8fb5-7c25bd685a19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} {ι₂ : K₂ → Type}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel
theorem _root_.solution {P : Ideal (MRing ι)} {d : ℕ} {g : (Σ k, ι₂ k) → MRing ι} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P g) : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => g ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk
end GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel
