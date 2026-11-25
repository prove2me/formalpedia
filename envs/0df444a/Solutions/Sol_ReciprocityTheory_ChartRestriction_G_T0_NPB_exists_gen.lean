-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPB.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:04.694799+00:00
-- url     : https://prove2.me/submissions/87f59531-7f2f-4653-94e6-de86df7ab72d

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_countable_mvPoly
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_eval_psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_psi_injective
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_eval_ne_zero_of_ne_zero_fin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.NPB
open MvPolynomial MeasureTheory ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.NPB
theorem _root_.solution (sg : K →+* ℂ) [Countable K] (tt : Fin D × Fin (N + 1) → ℂ)
    (hG : ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → eval₂ sg tt p ≠ 0)
    (Q : MvPolynomial (Fin (N + 1 + D)) ℂ) (hQ : Q ≠ 0) :
    ∃ y : Fin (N + 1 + D) → ℂ, eval y Q ≠ 0 ∧
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval₂ sg (gpt tt y) q ≠ 0 := by
  have := countable_mvPoly (σ := Fin (D + 1) × Fin (N + 1)) (R := K)
  have h1 := ae_eval_ne_zero_of_ne_zero_fin _ Q hQ
  have h2 : ∀ᵐ y ∂(volume : Measure (Fin (N + 1 + D) → ℂ)),
      ∀ q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K, q ≠ 0 → eval y (psi sg tt q) ≠ 0 := by
    rw [ae_all_iff]; intro q
    by_cases hq : q = 0
    · exact Filter.Eventually.of_forall fun y h => absurd hq h
    · have hq' : psi sg tt q ≠ 0 := fun h0 => hq (psi_injective sg tt hG (by rw [h0, map_zero]))
      filter_upwards [ae_eval_ne_zero_of_ne_zero_fin _ _ hq'] with y hy _ using hy
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  exact ⟨y, hy1, fun q hq => by rw [← eval_psi]; exact hy2 q hq⟩
end ReciprocityTheory.ChartRestriction.G.T0.NPB
