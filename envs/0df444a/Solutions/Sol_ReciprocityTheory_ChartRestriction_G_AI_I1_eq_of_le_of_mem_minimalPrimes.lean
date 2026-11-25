-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_le_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:22.974169+00:00
-- url     : https://prove2.me/submissions/05f341b1-4d0f-4246-b514-2b50643093dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_map_mk_mem_minimalPrimes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_comap_map_mk_of_le

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
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution [IsNoetherianRing R] {V W Q : Ideal R} (hV : V.IsPrime) {f g : R}
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hQ : Q.IsPrime) (hVQ : V ≤ Q) (hgQ : g ∈ Q)
    (hgV : g ∉ V) (hQW : Q ≤ W) : Q = W := by
  by_contra hne
  let π := Ideal.Quotient.mk V
  have hW' := map_mk_mem_minimalPrimes hW
  have : (W.map π).IsPrime := hW'.1.1
  have : (Ideal.span {π f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hW'
  have : (Q.map π).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hVQ)
  have hVW : V ≤ W := le_sup_left.trans hW.1.2
  have hlt : Q.map π < W.map π := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun e => hne ?_
    rw [← comap_map_mk_of_le hVQ, e, comap_map_mk_of_le hVW]
  have hbot : (⊥ : Ideal (R ⧸ V)) < Q.map π := by
    refine bot_lt_iff_ne_bot.mpr fun e => hgV ?_
    have : π g ∈ Q.map π := Ideal.mem_map_of_mem _ hgQ
    rw [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h4 : (2 : ℕ∞) ≤ (W.map π).height := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal (R ⧸ V)).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Q.map π).height + 1 := by gcongr
      _ ≤ _ := h2
  have := h4.trans h1
  norm_num at this
end ReciprocityTheory.ChartRestriction.G.AI.I1
