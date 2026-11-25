-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.TG_q_long
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:21.330104+00:00
-- url     : https://prove2.me/submissions/9cf7f254-353a-4df3-97fd-cb6889ba73ab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_D_zero

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2 ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
open ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {S : Type} [CommRing S] {ι : Type}
  (D : ι → S → S) (κ : k →+* S)
  (hadd : ∀ l f g, D l (f + g) = D l f + D l g) (hC : ∀ l a, D l (κ a) = 0)
  (hmul : ∀ l f g, D l (f * g) = D l f * g + f * D l g)
variable (e : S →+* k) (c : ι → ι → k) (q : S)
  (hq0 : e q = 0) (hq1 : ∀ l, e (D l q) = 0) (hq2 : ∀ l l', D l (D l' q) = κ (c l l'))
include hadd hC hq2
namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
theorem _root_.solution (w : List ι) (hw : 3 ≤ w.length) : TG D w q = 0 := by
  induction w with
  | nil => simp at hw
  | cons l w ih =>
    show D l (TG D w q) = 0
    rcases Nat.lt_or_ge w.length 3 with h | h
    · have h2 : w.length = 2 := by
        simp only [List.length_cons] at hw
        omega
      obtain ⟨y, z, rfl⟩ := List.length_eq_two.mp h2
      show D l (D y (D z q)) = 0
      rw [hq2, hC]
    · rw [ih h, D_zero D hadd]
end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
