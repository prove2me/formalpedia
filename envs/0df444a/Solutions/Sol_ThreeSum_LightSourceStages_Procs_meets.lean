-- Prove2me | solution 1 for ThreeSum.LightSourceStages.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:51.3725+00:00
-- url     : https://prove2.me/submissions/9970bd92-ebc2-4545-b45a-b77c42493ab9

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_SourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_source_abs_le
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
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
open ThreeSum ThreeSum.LightSourceStages
open Light SubsetAddress LightSubsetAddress LightPascal LightZetaCell
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceStages
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain) {μ : ℕ → ℤ}
    {src N raw flags p m hist base codes work L cut maskBase U D E : ℕ} {shift : ℤ} (endpoint : Finset (Fin L) → ℤ)
    (flag : Finset (Fin L) → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + L + 8 ≤ lim.depth) (hp : 0 < p) (hm : 0 < m)
    (hcut : cut ≤ L) (hsrc : src + N ≤ hist) (hraw : raw + downsetCap L cut ≤ hist)
    (hflags : flags + downsetCap L cut ≤ hist) (hhist : hist + m ≤ base)
    (hdata : base + (L + 1) * downsetCap L cut ≤ maskBase) (hmasks : maskBase + downsetCap L cut ≤ codes)
    (hcodes : codes + N ≤ work) (hspace : space work L p U D E ≤ lim.space) (hshift : |shift| ≤ (D : ℤ))
    (hword : (word N L p m U D E : ℤ) ≤ lim.word) (hvalues : ∀ i < N, |μ (src + i)| ≤ (U : ℤ))
    (hrawRead : ∀ i < downsetCap L cut, μ (raw + i) = endpoint (SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < downsetCap L cut, μ (flags + i) = (flag (SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1) :
    Meets lim P pMain d [src, N, raw, flags, p, m, hist, base, codes, work, shift, L, cut, maskBase, downsetCap L cut] μ
      (time N L cut p m U D E)
      (fun _ ν =>
        LightZetaStages.StoredThrough ν base cut (source μ src N p m shift endpoint flag) L ∧
          (∀ r < m,
              ν (hist + r) =
                (LightHistogram.count (fun j => LightSourceResidues.key p m shift (μ (src + j))) r N : ℤ)) ∧
            Kept μ ν hist) :=
  by
  have hsSource : LightSourceBuild.space work p U D E ≤ lim.space := (le_max_left _ _).trans hspace
  have hsZeta : work + tableSize L + (L + 1) ≤ lim.space := (le_max_right _ _).trans hspace
  have hwSource : (LightSourceBuild.word p m U D E : ℤ) ≤ lim.word :=
    by
    have hh : LightSourceBuild.word p m U D E ≤ word N L p m U D E := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwZeta : (((L + 1) * 2 ^ (L + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : (L + 1) * 2 ^ (L + 1) ≤ word N L p m U D E := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwValues : ((2 ^ L * N : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 2 ^ L * N ≤ word N L p m U D E := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hcap : downsetCap L cut ≤ (L + 1) * downsetCap L cut := Nat.le_mul_of_pos_left _ (by omega)
  apply Meets.of_body C.main
  unfold body time
  have hs :=
    C.sourceProcs.meets (d := d + 1) (μ := μ) (src := src) (N := N) (raw := raw) (flags := flags) (n :=
      downsetCap L cut) (p := p) (m := m) (hist := hist) (dst := base) (codes := codes) (work := work) (U := U) (D := D)
      (E := E) (shift := shift) (fun i => endpoint (SourceTableLayout.setAt L cut i))
      (fun i => flag (SourceTableLayout.setAt L cut i)) hw (by omega) hp hm hsrc hraw hflags hhist (by omega) hcodes
      hsSource hshift hwSource hvalues hrawRead (fun i hi => hrawBound _ (SourceTableLayout.setAt_card hi)) hflagRead
      (fun i hi => hflagBound _ (SourceTableLayout.setAt_card hi))
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
    | refine _root_.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceBuild.time,
            LightSourceHistogram.time, LightSourceResidues.time, LightSourceGather.time, LightZetaStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceBuild.time, LightSourceHistogram.time, LightSourceResidues.time, LightSourceGather.time,
              LightZetaStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceBuild.time,
            LightSourceHistogram.time, LightSourceResidues.time, LightSourceGather.time, LightZetaStages.time] <;> omega)
    on_goal -1 => (rintro r ν₁ ⟨out, counts, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have htable : TableAt ν₁ base cut (source μ src N p m shift endpoint flag) :=
    by
    apply SourceTableLayout.tableAt_of_setAt
    exact out
  have hz :=
    C.zeta.meets (d := d + 1) (μ := ν₁) (L := L) (cut := cut) (base := base) (maskBase := maskBase) (work := work) (U :=
      N) (source μ src N p m shift endpoint flag) hw hcut hdata (by omega) hsZeta hwZeta hwValues htable
      (fun S _ => source_abs_le μ src N p m shift endpoint flag S) (by omega)
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceBuild.time,
            LightSourceHistogram.time, LightSourceResidues.time, LightSourceGather.time, LightZetaStages.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceBuild.time, LightSourceHistogram.time, LightSourceResidues.time, LightSourceGather.time,
              LightZetaStages.time] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceBuild.time,
            LightSourceHistogram.time, LightSourceResidues.time, LightSourceGather.time, LightZetaStages.time] <;> omega)
    on_goal -1 => (rintro r ν₂ ⟨stored, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨stored, ?_, ?_⟩
  · intro r hr
    exact (kept₂ _ ⟨by omega, Or.inl (by omega)⟩).trans (counts r hr)
  · intro a ha
    exact (kept₂ a ⟨by omega, Or.inl (by omega)⟩).trans (kept₁ a ha)
end Procs
end ThreeSum.LightSourceStages
