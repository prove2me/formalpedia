-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:38.623009+00:00
-- url     : https://prove2.me/submissions/b8f1c834-5ff2-4d41-91cc-dc6056ed3589

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero

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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
theorem _root_.solution (E : Type) [Field E] [NumberField E] (ℓ : ℕ) (hℓ : ℓ.Prime) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (hl : (ℓ : 𝓞 E) ∈ P) : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
  have hne : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hpr : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hne).mpr (Nat.prime_iff_prime_int.mp hℓ)
  have hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    hpr.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hne)
  haveI := hP
  refine ⟨hmax.eq_of_le ?_ ?_⟩
  · exact (inferInstance : (P.under ℤ).IsPrime).ne_top
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
    simpa using hl
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
