-- Prove2me | solution 1 for ThreeSum.LightSourceRetainedStages.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:56.303617+00:00
-- url     : https://prove2.me/submissions/d31cbbd7-5cfb-4437-9393-1702a591e1d7

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Theorems.Thm_ThreeSum_LightSourceRetainedStages_source_abs_le
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_source_abs_le
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5
import Theorems.Thm_ThreeSum_SourceTableLayout_setAt_card
import Theorems.Thm_ThreeSum_SourceTableLayout_tableAt_of_setAt
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRetainedStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceRetainedStages
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ} {raw flags table base m work L cut maskBase E B : ℕ}
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d + L + 8 ≤ lim.depth) (hm : 0 < m) (hcut : cut ≤ L) (hraw : raw + downsetCap L cut ≤ base)
    (hflags : flags + downsetCap L cut ≤ base) (htable : table + m ≤ base)
    (hdata : base + (L + 1) * downsetCap L cut ≤ maskBase) (hmasks : maskBase + downsetCap L cut ≤ work)
    (hspace : space work L E ≤ lim.space) (hword : (word L m E B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < downsetCap L cut, μ (raw + i) = endpoint (SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < downsetCap L cut, μ (flags + i) = (flag (SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1) (hhistRead : ∀ r < m, μ (table + r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    Meets lim P pMain d [raw, flags, table, base, m, work, L, cut, maskBase, downsetCap L cut] μ (time L cut E)
      (fun _ ν => LightZetaStages.StoredThrough ν base cut (source m endpoint flag hist) L ∧ Kept μ ν base) :=
  by
  have hsGather : work + (Nat.log 2 (E + 1) + 2) ≤ lim.space := (le_max_left _ _).trans hspace
  have hsZeta : work + tableSize L + (L + 1) ≤ lim.space := (le_max_right _ _).trans hspace
  have hwGather : (4 * E + 4 * m + 16 : ℤ) ≤ lim.word :=
    by
    have hh : 4 * E + 4 * m + 16 ≤ word L m E B := by unfold word; omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  have hwB : (B : ℤ) ≤ lim.word := by
    have hh : B ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwZeta : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (L + 1) * 2 ^ (L + 1) ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwValues : ((2 ^ L * B : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ L * B ≤ word L m E B := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hcap : downsetCap L cut ≤ (L + 1) * downsetCap L cut := Nat.le_mul_of_pos_left _ (by omega)
  apply Meets.of_body C.main
  unfold body time
  have hg :=
    LightSourceGather.meets C.gather C.emod (d := d + 1) (μ := μ) (raw := raw) (flags := flags) (table := table) (dst :=
      base) (n := downsetCap L cut) (m := m) (work := work) (U := E) (B := B)
      (fun i => endpoint (SourceTableLayout.setAt L cut i)) (fun i => flag (SourceTableLayout.setAt L cut i)) hist hw
      (by omega) hm hraw hflags htable (by omega) hsGather hwGather hwB hrawRead
      (fun i hi => hrawBound _ (SourceTableLayout.setAt_card hi)) hflagRead
      (fun i hi => hflagBound _ (SourceTableLayout.setAt_card hi)) hhistRead hhistBound
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hg ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceGather.time,
            LightZetaStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceGather.time, LightZetaStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceGather.time,
            LightZetaStages.time] <;> omega)
    on_goal -1 => (rintro r ν₁ ⟨out, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have htableAt : TableAt ν₁ base cut (source m endpoint flag hist) :=
    by
    apply SourceTableLayout.tableAt_of_setAt
    exact out
  have hz :=
    C.zeta.meets (d := d + 1) (μ := ν₁) (L := L) (cut := cut) (base := base) (maskBase := maskBase) (work := work) (U :=
      B) (source m endpoint flag hist) hw hcut hdata hmasks hsZeta hwZeta hwValues htableAt
      (fun S _ => source_abs_le hm endpoint flag hist hhistBound S) (by omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (hz _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hz ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceGather.time,
            LightZetaStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceGather.time, LightZetaStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceGather.time,
            LightZetaStages.time] <;> omega)
    on_goal -1 => (rintro r ν₂ ⟨stored, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨stored, ?_⟩
  intro a ha
  exact (kept₂ a ⟨by omega, Or.inl (by omega)⟩).trans (kept₁ a ⟨by omega, Or.inl ha⟩)
end Procs
end ThreeSum.LightSourceRetainedStages
