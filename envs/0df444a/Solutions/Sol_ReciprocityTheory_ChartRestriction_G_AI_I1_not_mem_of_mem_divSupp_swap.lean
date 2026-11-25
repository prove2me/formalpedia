-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.not_mem_of_mem_divSupp_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:54.157104+00:00
-- url     : https://prove2.me/submissions/6c736735-999d-46e0-9c5c-5a8607ecdab8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_not_lt_lt_of_mem_minimalPrimes

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
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution {V W : Ideal (MRingOver F ι)} {n : ℕ} {f t : MRingOver F ι}
    {α β : K → ℕ} (hV : IsProjVarF V (n + 1)) (hf : IsMultiHomog f α) (ht : IsMultiHomog t β)
    (hfV : f ∉ V) (htV : t ∉ V) (hft : ∀ W ∈ divSupp V f, t ∉ W) (hW : W ∈ divSupp V t) :
    f ∉ W := by
  intro hfW
  haveI hVp : V.IsPrime := hV.1.1
  have hWp : W.IsPrime := hW.1.isPrime
  have hle : V ⊔ Ideal.span {f} ≤ W :=
    sup_le (le_sup_left.trans hW.1.1.2) (Ideal.span_le.mpr (by simpa using hfW))
  obtain ⟨W', hW', hW'W⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : W'.IsPrime := hW'.isPrime
  have hVW' : V < W' := lt_of_le_of_ne (le_sup_left.trans hW'.1.2) fun he =>
    hfV (he ▸ hW'.1.2 (le_sup_right (a := V) (Ideal.subset_span rfl)))
  rcases hW'W.lt_or_eq with hlt | heq
  · exact not_lt_lt_of_mem_minimalPrimes hW.1 hVW' hlt
  · subst heq
    exact hft W' ⟨hW', hW.2⟩ (hW.1.1.2 (le_sup_right (a := V) (Ideal.subset_span rfl)))
end ReciprocityTheory.ChartRestriction.G.AI.I1
