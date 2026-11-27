-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomogIdeal_coordIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:36.255278+00:00
-- url     : https://prove2.me/submissions/4af2d5fd-4339-4e0a-bc39-162bb8a4e6d0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_coordIdeal_isHomogIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {κ : Type} [Fintype κ] (v : Ix κ → Ω) :
    IsMultiHomogIdeal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  refine ⟨{f | f ∈ coordIdeal ℤ v ∧ ∃ n, f.IsHomogeneous n}, ?_, ?_⟩
  · rintro f ⟨_, n, hn⟩
    refine ⟨fun _ => n, fun m hm k => ?_⟩
    have h1 : Finsupp.degree m = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hn (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma] at h1
    cases k
    simpa using h1
  · apply le_antisymm
    · intro f hf
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => Ideal.subset_span
        ⟨coordIdeal_isHomogIdeal ℤ v f hf d, d, homogeneousComponent_isHomogeneous d f⟩
    · exact Ideal.span_le.mpr fun f hf => hf.1
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
