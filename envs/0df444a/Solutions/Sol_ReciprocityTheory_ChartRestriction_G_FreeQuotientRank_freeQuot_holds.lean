-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.freeQuot_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:28:20.647236+00:00
-- url     : https://prove2.me/submissions/a6b9768b-4f1f-45b7-8dac-c07124fa4698

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Lemmata_MiscLemmasJ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_freeQuot_exists_smul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_freeQuot_rank_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Module
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution : FreeQuotStatement := by
  intro R F X _ _ _ _ _ _ _ _ _ _ M₁ hM₁ N
  have : Module.Finite R M₁ := Module.Finite.iff_fg.mpr hM₁
  have ne : ∀ r : R, r ≠ 0 → algebraMap R F r ≠ 0 := fun r hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  have htf : Module.IsTorsionFree R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r q hq
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    have hq' : algebraMap R F r • (m : X) ∈ N := by
      rw [algebraMap_smul]
      simpa using hq
    show (m : X) ∈ N
    have h2 := N.smul_mem (algebraMap R F r)⁻¹ hq'
    rwa [smul_smul, inv_mul_cancel₀ (ne r hr), one_smul] at h2
  refine ⟨inferInstance, ?_⟩
  have hspan : Submodule.span F ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) =
      Submodule.span F (M₁ : Set X) ⊓ N := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr ⟨Submodule.subset_span hx1, hx2⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem M₁ hx1
      have hN : d • x ∈ N := by
        rw [← algebraMap_smul F d x]
        exact N.smul_mem _ hx2
      have hmem : d • x ∈ Submodule.span F
          ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) :=
        Submodule.subset_span (Submodule.mem_inf.mpr ⟨hd', hN⟩)
      rw [← algebraMap_smul F d x] at hmem
      have h2 := Submodule.smul_mem _ (algebraMap R F d)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (ne d hd), one_smul] at h2
  have hrn := Submodule.finrank_quotient_add_finrank ((N.restrictScalars R).comap M₁.subtype)
  have hM : finrank R M₁ = finrank F (Submodule.span F (M₁ : Set X)) :=
    congrArg Cardinal.toNat (freeQuot_rank_span M₁)
  have hP : finrank R ((N.restrictScalars R).comap M₁.subtype) =
      finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) := by
    rw [(Submodule.equivMapOfInjective M₁.subtype M₁.injective_subtype
      ((N.restrictScalars R).comap M₁.subtype)).finrank_eq, Submodule.map_comap_subtype, ← hspan]
    exact congrArg Cardinal.toNat (freeQuot_rank_span _)
  rw [← hP, ← hM]
  exact hrn
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
