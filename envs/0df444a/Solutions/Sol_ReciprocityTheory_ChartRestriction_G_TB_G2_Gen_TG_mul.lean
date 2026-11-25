-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.Gen.TG_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:57.075541+00:00
-- url     : https://prove2.me/submissions/eb634970-e670-405d-965e-51e24f9363ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ETGMulQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_Gen_D_list_sum

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
include hadd hmul
namespace ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
theorem _root_.solution (w : List ι) (A B : S) :
    TG D w (A * B) = ((splits w).map (fun p => TG D p.1 A * TG D p.2 B)).sum := by
  induction w with
  | nil => simp [TG, splits]
  | cons l w ih =>
    have e : ∀ (v : List ι) (X : S), TG D (l :: v) X = D l (TG D v X) := fun _ _ => rfl
    rw [e, ih, D_list_sum D hadd]
    simp only [splits, List.map_append, List.sum_append, List.map_map, Function.comp_def, e, hmul,
      List.sum_map_add]
end ReciprocityTheory.ChartRestriction.G.TB.G2.Gen
