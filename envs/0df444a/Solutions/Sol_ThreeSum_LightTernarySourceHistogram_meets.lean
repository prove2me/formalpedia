-- Prove2me | solution 1 for ThreeSum.LightTernarySourceHistogram.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:42:12.071879+00:00
-- url     : https://prove2.me/submissions/1b6adee4-bfe3-4b83-aef7-bbf33a4f7191

import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_scale_meets
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Definitions.Def_WeightedCache3SUM_Alias_a9326e55c9f5f09c
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHistogram
open Light ThreeSum.LightArray ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernarySourceHistogram
theorem _root_.solution
    {pMain pKeys pHist pScale pSearch pFill a bank powers W L pairs count words wordCount keyBase valueBase : ℕ}
    (hmain : P[pMain]? = some (body pKeys pHist pScale))
    (hkeys : P[pKeys]? = some (LightTernarySourceKeys.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hhist : P[pHist]? = some (LightHistogram.histogramBody pFill)) (hfill : P[pFill]? = some fillBody)
    (hscale : P[pScale]? = some scaleBody) (μ : ℕ → ℤ) (codes : ℕ → ℕ) (position key : ℕ → ℕ) (weight : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + bank ≤ keyBase) (hpair : pairs + 2 * count ≤ keyBase)
    (hwords : words + wordCount ≤ keyBase) (hpows : powers + (W + 1) ≤ keyBase)
    (hkeysBefore : keyBase + count ≤ valueBase) (hvalues : valueBase + bank ≤ lim.space)
    (hword : ((bank + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word) (hweight : (weight : ℤ) ≤ lim.word)
    (hweightedCount : (weight : ℤ) * (count : ℤ) ≤ lim.word) (hcodes : ∀ i < bank, μ (a + i) = (codes i : ℤ))
    (hpairRead : ∀ i < count, μ (pairs + 2 * i + 1) = (position i : ℤ))
    (hposition : ∀ i < count, position i < wordCount)
    (hwordRead : ∀ i < count, μ (words + position i) = (codes (key i) : ℤ)) (hkey : ∀ i < count, key i < bank)
    (hcodeBound : ∀ i < bank, codes i < 2 ^ W) (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < bank → codes i < codes k) (hL : L ≤ W) (hn : bank < 2 ^ L)
    (hd : d + L + 2 ≤ lim.depth) :
    Meets lim P pMain d [a, bank, powers, L, pairs, count, words, wordCount, keyBase, valueBase, weight] μ
      (time L count bank)
      (fun _ ν =>
        (∀ r < bank, ν (valueBase + r) = (weight : ℤ) * (LightHistogram.count key r count : ℤ)) ∧
          ∀ x, (x < keyBase ∨ keyBase + count ≤ x) → (x < valueBase ∨ valueBase + bank ≤ x) → ν x = μ x) :=
  by
  have hk :=
    LightTernarySourceKeys.meets (d := d + 1) hkeys hsearch μ codes position key hw ha hpair hwords hpows (by omega)
      hword hcodes hpairRead hposition hwordRead hkey hcodeBound hpowers hsorted hL hn (by omega)
  apply Meets.of_body hmain
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
    first
    | refine _root_.Light.Ends.callToThen (hk _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hk ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernarySourceKeys.time,
            LightHistogram.histogramTime, scaleTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernarySourceKeys.time, LightHistogram.histogramTime, scaleTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernarySourceKeys.time,
            LightHistogram.histogramTime, scaleTime] <;>
          omega)
    on_goal -1 => (rintro res μ₁ ⟨hkeyArray, hkeepKeys⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hh :=
    LightHistogram.histogram_meets (d := d + 1) hhist hfill key hw (by omega) (by omega) hvalues
      (by unfold Apart; omega) hkeyArray hkey
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
    | refine _root_.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernarySourceKeys.time,
            LightHistogram.histogramTime, scaleTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernarySourceKeys.time, LightHistogram.histogramTime, scaleTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernarySourceKeys.time,
            LightHistogram.histogramTime, scaleTime] <;>
          omega)
    on_goal -1 => (rintro res μ₂ ⟨hcounts, hkeepHist⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hcountBound : ∀ j < bank, |μ₂ (valueBase + j)| ≤ count :=
    by
    intro j hj
    rw [hcounts j hj, abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast LightHistogram.count_le key j count
  have hs := scale_meets (d := d + 1) hscale μ₂ weight hw hvalues hcountBound hweight hweightedCount
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
    | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernarySourceKeys.time,
            LightHistogram.histogramTime, scaleTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernarySourceKeys.time, LightHistogram.histogramTime, scaleTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernarySourceKeys.time,
            LightHistogram.histogramTime, scaleTime] <;>
          omega)
    on_goal -1 => (rintro res ν ⟨hweighted, hkeepScale⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_⟩
  · intro r hr
    change ν (valueBase + r) = (weight : ℤ) * (LightHistogram.count key r count : ℤ)
    rw [hweighted r hr, hcounts r hr]
  · intro x hx hy
    exact (hkeepScale x hy).trans ((hkeepHist x hy).trans (hkeepKeys x hx))
end ThreeSum.LightTernarySourceHistogram
