-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ChangeOfModel_exists_linForm_not_mem_f14275273c1a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:16.609117+00:00
-- url     : https://prove2.me/submissions/5e6d931a-71f5-4680-b2ee-c8c5642bb233

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel

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
open GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfModel
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
omit [∀ k, Fintype (ι₂ k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfModel
theorem _root_.solution {P : Ideal (MRing ι)} {d : ℕ} {A : ∀ k, ι₂ k → ι k → ℤ} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P (linForm A)) : ∀ k₂, ∃ j, linForm A ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => linForm A ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  have := hprime
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk
end GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfModel
