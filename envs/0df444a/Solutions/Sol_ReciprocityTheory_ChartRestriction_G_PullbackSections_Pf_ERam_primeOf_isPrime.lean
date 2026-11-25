-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.primeOf_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:21.125864+00:00
-- url     : https://prove2.me/submissions/023ff7c3-492b-4757-9690-900da1208ea8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_mem_primeOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_psi_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution (ψ : E →+* k) (hψ : Function.Injective ψ) : (primeOf (V := V) ψ hψ).IsPrime := by
  have hmul : ∀ a b : k, a ≠ 0 → b ≠ 0 → vV V (a * b) = vV V a + vV V b := by
    intro a b ha hb
    unfold vV
    rw [map_mul, WithZero.log_mul ((valV V (K' := k)).ne_zero_iff.mpr ha)
      ((valV V (K' := k)).ne_zero_iff.mpr hb)]
    ring
  have hv1 : vV V (1 : k) = 0 := by
    unfold vV; rw [map_one, WithZero.log_one]; simp
  refine Ideal.isPrime_iff.2 ⟨(Ideal.ne_top_iff_one _).2 ?_, ?_⟩
  · rw [mem_primeOf]
    push_neg
    refine ⟨?_, one_ne_zero⟩
    simp [hv1]
  · intro x y hxy
    rw [mem_primeOf] at hxy ⊢
    rw [mem_primeOf]
    by_cases hx0 : x = 0
    · exact Or.inl (Or.inr hx0)
    by_cases hy0 : y = 0
    · exact Or.inr (Or.inr hy0)
    have hxy' := hxy.resolve_right (mul_ne_zero hx0 hy0)
    have hc : ((x * y : 𝓞 E) : E) = (x : E) * (y : E) := by simp
    rw [hc, map_mul, hmul _ _ (psi_ne_zero ψ hψ hx0) (psi_ne_zero ψ hψ hy0)] at hxy'
    by_contra hno
    push_neg at hno
    have := hno.1.1
    have := hno.2.1
    linarith
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
