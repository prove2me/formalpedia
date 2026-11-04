-- Prove2me | solution 1 for ThreeSum.LightTernaryGroupedSources.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:50:19.773284+00:00
-- url     : https://prove2.me/submissions/24fc96f8-ac6b-4d2f-9961-c81c3d09cfa6

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSourceKeys
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedSources
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightTernaryGroupedSourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHistogram_scale_meets
import Theorems.Thm_ThreeSum_LightTernarySourceKeys_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_abs_le
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedSources
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryGroupedSources
theorem _root_.solution
    {pMain pKeys pHist pScale pSearch pFill a bank powers W L pairs count words wordCount keyBase valueBase weightBase
      originalCount U groupBase groups : ℕ}
    (hmain : P[pMain]? = some (body pKeys pHist pScale))
    (hkeys : P[pKeys]? = some (LightTernaryGroupedSourceKeys.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hhist : P[pHist]? = some (LightTernaryWeightedHistogram.body pFill)) (hfill : P[pFill]? = some fillBody)
    (hscale : P[pScale]? = some LightTernarySourceHistogram.scaleBody) (μ : ℕ → ℤ) (codes : ℕ → ℕ)
    (dictionaryPosition originalPosition key group : ℕ → ℕ) (weight : ℕ → ℤ) (factor : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + bank ≤ keyBase) (hpair : pairs + 2 * count ≤ keyBase)
    (hwords : words + wordCount ≤ keyBase) (hpows : powers + (W + 1) ≤ keyBase)
    (hweightArray : weightBase + originalCount ≤ keyBase) (hgroupArray : groupBase + wordCount ≤ keyBase)
    (hgroupRead : ∀ i < count, μ (groupBase + dictionaryPosition i) = (group i : ℤ))
    (hgroupLt : ∀ i < count, group i < groups) (hgroupWord : ((groups * bank + 1 : ℕ) : ℤ) ≤ lim.word)
    (hgroupSpace : groups * bank + 1 ≤ lim.space) (hkeysBefore : keyBase + count ≤ valueBase)
    (hvalues : valueBase + groups * bank ≤ lim.space) (hword : ((bank + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hfactor : (factor : ℤ) ≤ lim.word) (hweightedCount : (factor : ℤ) * (count * U : ℕ) ≤ lim.word)
    (hhistWord : ((count + 1 : ℕ) : ℤ) * U ≤ lim.word) (hcodes : ∀ i < bank, μ (a + i) = (codes i : ℤ))
    (hpairRead : ∀ i < count, μ (pairs + 2 * i + 1) = (dictionaryPosition i : ℤ))
    (hdictionaryPosition : ∀ i < count, dictionaryPosition i < wordCount)
    (hwordRead : ∀ i < count, μ (words + dictionaryPosition i) = (codes (key i) : ℤ)) (hkey : ∀ i < count, key i < bank)
    (hcodeBound : ∀ i < bank, codes i < 2 ^ W) (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < bank → codes i < codes k)
    (hposRead : ∀ i < count, μ (pairs + 2 * i) = (originalPosition i : ℤ))
    (hposLt : ∀ i < count, originalPosition i < originalCount)
    (hweightRead : ∀ i < count, μ (weightBase + originalPosition i) = weight i)
    (hweightBound : ∀ i < count, |weight i| ≤ U) (hL : L ≤ W) (hn : bank < 2 ^ L) (hd : d + L + 2 ≤ lim.depth) :
    Meets lim P pMain d
      [a, bank, powers, L, pairs, count, words, wordCount, keyBase, valueBase, weightBase, originalCount, factor,
        groupBase, groups]
      μ (time L count bank groups)
      (fun _ ν =>
        (∀ r < groups * bank,
            ν (valueBase + r) =
              (factor : ℤ) * LightTernaryWeightedHistogram.total (fun i => group i * bank + key i) weight r count) ∧
          ∀ x, (x < keyBase ∨ keyBase + count ≤ x) → (x < valueBase ∨ valueBase + groups * bank ≤ x) → ν x = μ x) :=
  by
  have hk :=
    LightTernaryGroupedSourceKeys.meets (d := d + 1) hkeys hsearch μ codes dictionaryPosition key group hw ha hpair
      hwords hpows hgroupArray hgroupRead hgroupLt hgroupWord hgroupSpace (by omega) hword hcodes hpairRead
      hdictionaryPosition hwordRead hkey hcodeBound hpowers hsorted hL hn (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightTernaryGroupedSourceKeys.time,
            LightTernaryWeightedHistogram.time, LightTernarySourceHistogram.scaleTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightTernaryGroupedSourceKeys.time, LightTernaryWeightedHistogram.time,
              LightTernarySourceHistogram.scaleTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightTernaryGroupedSourceKeys.time,
            LightTernaryWeightedHistogram.time, LightTernarySourceHistogram.scaleTime] <;>
          omega)
    on_goal -1 => (rintro res μ₁ ⟨hkeyArray, hkeepKeys⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hpos : ∀ i < count, μ₁ (pairs + 2 * i) = (originalPosition i : ℤ) :=
    by
    intro i hi
    exact (hkeepKeys _ (Or.inl (by omega))).trans (hposRead i hi)
  have hweights : ∀ i < count, μ₁ (weightBase + originalPosition i) = weight i :=
    by
    intro i hi
    exact (hkeepKeys _ (Or.inl (by have hh := hposLt i hi; omega))).trans (hweightRead i hi)
  have hgroupKey : ∀ i < count, group i * bank + key i < groups * bank :=
    by
    intro i hi
    have hg := hgroupLt i hi
    have hk := hkey i hi
    nlinarith
  have hbg : (bank : ℤ) * (groups : ℤ) = ((groups * bank : ℕ) : ℤ) := by push_cast; ring
  have hh :=
    LightTernaryWeightedHistogram.meets (d := d + 1) hhist hfill μ₁ (fun i => group i * bank + key i) originalPosition
      weight hw (by omega) hkeysBefore (by omega) (by omega) hvalues hkeyArray hpos hweights hgroupKey hposLt
      hweightBound hhistWord
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbg, LightTernaryGroupedSourceKeys.time,
            LightTernaryWeightedHistogram.time, LightTernarySourceHistogram.scaleTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbg, LightTernaryGroupedSourceKeys.time, LightTernaryWeightedHistogram.time,
              LightTernarySourceHistogram.scaleTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbg, LightTernaryGroupedSourceKeys.time,
            LightTernaryWeightedHistogram.time, LightTernarySourceHistogram.scaleTime] <;>
          omega)
    on_goal -1 => (rintro res μ₂ ⟨hcounts, hkeepHist⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hbound : ∀ j < groups * bank, |μ₂ (valueBase + j)| ≤ (count * U : ℕ) :=
    by
    intro j hj
    rw [hcounts j hj]
    simpa only [Nat.cast_mul] using
      LightTernaryWeightedHistogram.total_abs_le (fun i => group i * bank + key i) weight j count U hweightBound
  have hs :=
    LightTernarySourceHistogram.scale_meets (d := d + 1) hscale μ₂ factor hw hvalues hbound hfactor hweightedCount
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbg, LightTernaryGroupedSourceKeys.time,
            LightTernaryWeightedHistogram.time, LightTernarySourceHistogram.scaleTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbg, LightTernaryGroupedSourceKeys.time, LightTernaryWeightedHistogram.time,
              LightTernarySourceHistogram.scaleTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbg, LightTernaryGroupedSourceKeys.time,
            LightTernaryWeightedHistogram.time, LightTernarySourceHistogram.scaleTime] <;>
          omega)
    on_goal -1 => (rintro res ν ⟨hscaled, hkeepScale⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨?_, ?_⟩
  · intro r hr
    change
      ν (valueBase + r) =
        (factor : ℤ) * LightTernaryWeightedHistogram.total (fun i => group i * bank + key i) weight r count
    rw [hscaled r hr, hcounts r hr]
  · intro x hx hy
    exact (hkeepScale x hy).trans ((hkeepHist x hy).trans (hkeepKeys x hx))
end ThreeSum.LightTernaryGroupedSources
