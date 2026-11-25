-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.e_TG_mul_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:49.262639+00:00
-- url     : https://prove2.me/submissions/1c980017-4a9c-4cb8-bde1-65576114994c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_TG_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_e_TG_q

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
variable (he : ∀ a, e (κ a) = a)
include hadd hmul hC hq0 hq1 hq2 he
namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
theorem _root_.solution (w : List ι) (A : S) :
    e (TG D w (A * q)) = ((splits w).map (fun p => e (TG D p.1 A) * ev2 c p.2)).sum := by
  simp only [TG_mul (D := D) (hadd := hadd) (hmul := hmul), map_list_sum, List.map_map,
    Function.comp_def, map_mul, e_TG_q (D := D) (κ := κ) (hadd := hadd) (hC := hC) (e := e) (c := c)
      (q := q) (hq0 := hq0) (hq1 := hq1) (hq2 := hq2) (he := he)]
end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
