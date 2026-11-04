-- Prove2me | solution 1 for ThreeSum.LightBruteThreeSum.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:28:31.409104+00:00
-- url     : https://prove2.me/submissions/996a2719-17f8-4c2c-b910-e69ca69af157

import Definitions.Def_Submission_ThreeSum_LightOriginalTripleScan
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Definitions.Def_Submission_ThreeSum_LightBruteThreeSum
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_Spec_length_affL
import Theorems.Thm_ThreeSumApsp_Spec_length_subMat
import Definitions.Def_WeightedCache3SUM_Alias_9de9e2ba6f3cf510
import Theorems.Thm_ThreeSum_ColorClassLists_value_fin
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
import Definitions.Def_WeightedCache3SUM_Alias_98152438e5b788f3
import Definitions.Def_WeightedCache3SUM_Alias_5d83a00a3f301eb9
import Definitions.Def_WeightedCache3SUM_Alias_6cd6f72823a59258
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_ec604c008ed4b1df
import Definitions.Def_WeightedCache3SUM_Alias_eb09b223848624eb
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.ColorClassLists.value_fin
attribute [local simp] ThreeSum.LightClassFilter.items_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSumApsp.Spec.length_affL
attribute [local simp] ThreeSumApsp.Spec.length_subMat
set_option autoImplicit false
open ThreeSum ThreeSum.LightBruteThreeSum
open Light ThreeSumApsp.Spec
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBruteThreeSum
theorem _root_.solution {pMain pScan pRow pDivide src n U fr d : ℕ} (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hp : P[pMain]? = some (body pScan)) (hscan : P[pScan]? = some (LightOriginalTripleScan.body pScan pRow))
    (hrow : P[pRow]? = some (LightOriginalTripleRow.body pDivide)) (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (hn : 0 < n) (hsrc : src + n ≤ fr) (H : (need n U).Ok lim fr d) (hread : ∀ i : Fin n, μ (src + i.val) = x i)
    (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [n, U, src, fr] μ (time n)
      (fun r ν => (r = 0 ∨ r = 1) ∧ (r = 1 ↔ Coloring.DistinctZeroSum x) ∧ ν = μ) :=
  by
  have hw := H.word
  have hs := H.space
  have hspace : src + n ≤ lim.space := hsrc.trans (by have := H.cells; simp only [need, add_zero] at this; exact this)
  have hd : d + n ^ 3 + 3 ≤ lim.depth := H.depth
  have hn3 : (n ^ 3 : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by dsimp [need, LightOriginalTripleRow.word]; omega)).trans hw
  have hn2 : n * n ≤ n ^ 3 := by
    have hh := Nat.le_mul_of_pos_right (n * n) hn
    simpa only [pow_succ, pow_zero, one_mul] using hh
  have h2Word : (n : ℤ) * (n : ℤ) ≤ lim.word := (by exact_mod_cast hn2 : (n : ℤ) * (n : ℤ) ≤ (n ^ 3 : ℤ)).trans hn3
  have h3Eq : (n : ℤ) * (n : ℤ) * (n : ℤ) = (n ^ 3 : ℕ) := by push_cast; ring
  apply Meets.of_body hp
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (n ^ 3 : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, h3Eq, LightOriginalTripleScan.time,
            LightOriginalTripleRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [h3Eq, LightOriginalTripleScan.time, LightOriginalTripleRow.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, h3Eq, LightOriginalTripleScan.time,
            LightOriginalTripleRow.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hc :=
    LightOriginalTripleScan.meets (d := d + 1) x μ hscan hrow hdivide hn le_rfl hs hspace H.word (by omega) hread hbound
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    first
    | refine _root_.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightOriginalTripleScan.time,
            LightOriginalTripleRow.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightOriginalTripleScan.time, LightOriginalTripleRow.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightOriginalTripleScan.time,
            LightOriginalTripleRow.time] <;>
          omega)
    on_goal -1 => (rintro r ν ⟨hbool, hcorrect, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  exact ⟨hbool, hcorrect.trans (BruteTripleIndex.hit_complete x hn), hmem⟩
end ThreeSum.LightBruteThreeSum
