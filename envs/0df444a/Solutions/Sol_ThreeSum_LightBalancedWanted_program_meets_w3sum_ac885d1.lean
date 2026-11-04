-- Prove2me | solution 1 for ThreeSum.LightBalancedWanted.program_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:38:19.602233+00:00
-- url     : https://prove2.me/submissions/5ef824e5-03d6-4a72-9413-50c2f4c74bfb

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Theorems.Thm_Light_Ends_append
import Theorems.Thm_Light_Exec_append
import Theorems.Thm_Light_Meets_append
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSumApsp_AbsLe_append
import Theorems.Thm_ThreeSum_GlobalKeyOffset_selected_lt
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_selected_lt
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_db7e3579c631dfa5
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_724c353a3aa82655
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_7018b9952430b957
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_5471e369d555e9e5
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_ThreeSum_RawAKeyLists_selected_lt
import Theorems.Thm_ThreeSum_ReportingHostRelocation_meets
import Theorems.Thm_ThreeSum_WantedResidueKeys_selected_congr
import Theorems.Thm_ThreeSum_WantedResidueKeys_selected_total_bound
set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedWanted
open Light WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits}
namespace ThreeSum.LightBalancedWanted
theorem _root_.solution {μ : ℕ → ℤ} {a b NL NR M free U d : ℕ} [NeZero M] (left right : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + NL ≤ free) (hb : b + NR ≤ free)
    (hspace : space free M left right NL NR U ≤ lim.space) (hword : (word M NL NR U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 M + NL + 6 ≤ lim.depth) (hleft : ∀ i < NL, μ (a + i) = left i)
    (hright : ∀ j < NR, μ (b + j) = right j) (hvaluesL : ∀ i < NL, |left i| ≤ (U : ℤ))
    (hvaluesR : ∀ j < NR, |right j| ≤ (U : ℤ)) :
    Meets lim program 25 d [a, b, NL, NR, M, free] μ (time M left right NL NR U)
      (fun r ν =>
        r = (free : ℤ) ∧
          LightWantedSetup.Output ν free M left right NL NR (LightOriginalOffset.selected M left right NL NR) ∧
            M * (ν free).toNat ≤ NL * NR ∧ Kept μ ν free) :=
  by
  let shift := LightOriginalOffset.selected M left right NL NR
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hshift : shift < M := LightOriginalOffset.selected_lt ..
  have hshiftAbs : |(shift : ℤ)| ≤ (M : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr (by omega)
  have hoffSpace : LightOriginalOffset.space free M (NL + NR) U ≤ lim.space := (le_max_left _ _).trans hspace
  have hwantedSpace : LightWantedSetup.space free M left right NL NR U M shift ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hoffWord : (LightOriginalOffset.word M (NL + NR) U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwantedWord : (LightSourceResidues.word M M U M : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hNWord : ((NL + NR : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold LightOriginalOffset.space at hoffSpace; omega)).trans hw
  have hselected : LightOriginalOffset.selected M (fun i => μ (a + i)) (fun j => μ (b + j)) NL NR = shift :=
    selected_congr hleft hright
  apply Meets.of_body (p := 25) (by rfl : program[25]? = some (body 0 24))
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    refine _root_.Light.Ends.setToThen (NL + NR : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have ho :=
    ((LightOriginalOffset.program_meets (d := d + 1) (μ := μ) (a := a) (b := b) (nLeft := NL) (nRight := NR) (p := M)
              (N := NL + NR) (free := free) (U := U) hw ha hb (by omega) (by omega) hoffSpace hoffWord (by omega)
              (fun i hi => by rw [hleft i hi]; exact hvaluesL i hi)
              (fun j hj => by rw [hright j hj]; exact hvaluesR j hj)).append
          (LightWantedSetup.program.map (ReportingHostRelocation.relocate 13))).append
      [body 0 24]
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
    | refine _root_.Light.Ends.callToThen (ho _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen ho ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    on_goal -1 => (rintro chosen μ₁ ⟨hchosen, hkeepO⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hchosenShift : chosen = (shift : ℤ) := hchosen.trans (congrArg Nat.cast hselected)
  have hs :=
    (ReportingHostRelocation.meets
          (LightWantedSetup.program_meets (d := d + 1) (μ := μ₁) (a := a) (b := b) (NL := NL) (NR := NR) (M := M)
            (free := free) (U := U) (D := M) (shift := shift) left right hw hM ha hb hwantedSpace hwantedWord hshiftAbs
            (by omega) (fun i hi => (hkeepO _ (by omega)).trans (hleft i hi))
            (fun j hj => (hkeepO _ (by omega)).trans (hright j hj)) hvaluesL hvaluesR)
          LightOriginalOffset.program).append
      [body 0 24]
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
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hchosenShift, shift]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hchosenShift, shift] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hchosenShift, shift] <;> omega)
    on_goal -1 => (rintro result ν ⟨hresult, houtput, hkeepS⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hresult, houtput, ?_, ?_⟩
  · change M * (ν free).toNat ≤ NL * NR
    rw [houtput.1, Int.toNat_natCast]
    exact selected_total_bound M left right NL NR
  · intro i hi
    exact (hkeepS i hi).trans (hkeepO i hi)
end ThreeSum.LightBalancedWanted
