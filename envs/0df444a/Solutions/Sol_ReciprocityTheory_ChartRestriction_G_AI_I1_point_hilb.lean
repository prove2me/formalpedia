-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.point_hilb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:34:35.02479+00:00
-- url     : https://prove2.me/submissions/61f63b93-727e-4081-b5bd-352e9f345593

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsMonomialNotMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_exists_homog_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_of_mem_chartIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_chart_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]
variable {W : Ideal (MRingOver F ι)}
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution [DecidableEq K] (hW : IsProjVarF W 0) {j : ∀ k, ι k} (hj : IsChart W j) :
    ∃ e₀ : K → ℕ, ∀ e, e₀ ≤ e →
      Module.finrank F ↥(weightedHomogeneousSubmodule F (mw (ι := ι)) e ⊓ W.restrictScalars F) +
        ptDeg W j = Module.finrank F ↥(weightedHomogeneousSubmodule F (mw (ι := ι)) e) := by
  haveI := chart_finite hW hj
  haveI := hW.1.1
  let bs := Module.finBasis F (MRingOver F ι ⧸ chartIdeal W j)
  choose lift hlift using fun i => Ideal.Quotient.mk_surjective (bs i)
  choose e0 he0 using fun i => exists_homog_chart W j (lift i)
  refine ⟨Finset.univ.sup e0, fun e he => ?_⟩
  let π : weightedHomogeneousSubmodule F (mw (ι := ι)) e →ₗ[F] MRingOver F ι ⧸ chartIdeal W j :=
    (Ideal.Quotient.mkₐ F (chartIdeal W j)).toLinearMap ∘ₗ Submodule.subtype _
  have hsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← bs.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨b', hb', eb⟩ := he0 i e ((Finset.le_sup (Finset.mem_univ i)).trans he)
    exact ⟨⟨b', hb'⟩, by simp [π, eb, hlift]⟩
  have hker : LinearMap.ker π = (W.restrictScalars F).comap (Submodule.subtype _) := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.restrictScalars_mem,
      Submodule.coe_subtype]
    constructor
    · intro h
      exact mem_of_mem_chartIdeal hW.1.2.1 hj x.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
    · intro h
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left h)
  have h1 := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype] at h1
  rw [ptDeg]
  omega
end ReciprocityTheory.ChartRestriction.G.AI.I1
