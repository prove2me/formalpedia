-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.traceDual_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:45.94685+00:00
-- url     : https://prove2.me/submissions/6ab76c5c-6a4e-4f36-81b9-d95af99972d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_algebraMap_smul_oe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution (τ : E ≃ₐ[ℚ] E) {y : E} (hy : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E)) :
    τ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_traceDual] at hy ⊢
  intro a ha
  obtain ⟨o, rfl⟩ := Submodule.mem_one.mp ha
  have hb : τ.symm (algebraMap (𝓞 E) E o) ∈ (1 : Submodule (𝓞 E) E) :=
    Submodule.mem_one.mpr ⟨τ.symm • o, algebraMap_smul_oe τ.symm o⟩
  have key := hy _ hb
  rw [Algebra.traceForm_apply] at key ⊢
  rw [← Algebra.trace_eq_of_algEquiv τ, map_mul, AlgEquiv.apply_symm_apply] at key
  exact key
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
