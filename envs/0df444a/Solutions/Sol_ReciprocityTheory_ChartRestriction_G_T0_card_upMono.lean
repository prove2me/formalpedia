-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.card_upMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:39.899339+00:00
-- url     : https://prove2.me/submissions/1b77c52d-a2b5-4c4d-8f85-a329f52cdf3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UpMkApplyInl
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (D N n n' : ℕ) : (upMono D N n n').card = cardUX D N n n' := by
  classical
  unfold upMono cardUX
  rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
    Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · congr 1
    · rw [show D + 2 + n - 1 = n + (D + 1) by omega, Nat.choose_symm_add, Nat.add_assoc]
    · rw [show (D + 2) * (N + 1) + 1 + n' - 1 = n' + (D + 2) * (N + 1) by omega, Nat.choose_symm_add]
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_finsuppAntidiag] at hab hab'
    have h1 : ∀ i, a i = a' i := fun i => by
      have := congrArg (fun s => s (Sum.inr i)) h
      simpa [upMk] using this
    have h2 : ∀ p, b (some p) = b' (some p) := fun p => by
      have := congrArg (fun s => s (Sum.inl p)) h
      simpa [upMk] using this
    have hb := hab.2.1
    have hb' := hab'.2.1
    rw [Fintype.sum_option] at hb hb'
    have hs : ∑ p, b (some p) = ∑ p, b' (some p) := Finset.sum_congr rfl fun p _ => h2 p
    have h3 : b none = b' none := by omega
    refine Prod.ext (Finsupp.ext h1) (Finsupp.ext fun o => ?_)
    cases o
    · exact h3
    · exact h2 _
end ReciprocityTheory.ChartRestriction.G.T0
