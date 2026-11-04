-- Prove2me | solution 1 for ThreeSum.LightSourceRowFlag.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:46.941539+00:00
-- url     : https://prove2.me/submissions/02b97078-c589-4437-b6ba-d2917aaf1ca8

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Theorems.Thm_ThreeSum_LightSourceRowFlag_flag_le
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_6850731862e76136
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Theorems.Thm_ThreeSum_LightResidues_emodTime_le
import Theorems.Thm_ThreeSum_LightResidues_residue_cast
import Theorems.Thm_ThreeSum_LightResidues_residue_lt
import Theorems.Thm_ThreeSum_LightSourceFlagTest_flag_le
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_zero
import Theorems.Thm_ThreeSum_LightSourceRowScan_hash_le
import Theorems.Thm_ThreeSum_LightSourceRowScan_hash_zero
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
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
attribute [local simp] ThreeSum.LightSourceRowScan.count_zero
attribute [local simp] ThreeSum.LightSourceRowScan.hash_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowFlag
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceRowFlag
theorem _root_.solution {pMain pRow pEmod pFlag : ℕ} (hmain : P[pMain]? = some (body pRow pEmod pFlag))
    (hrow : P[pRow]? = some LightSourceRowScan.body) (hem : P[pEmod]? = some emodBody)
    (hflag : P[pFlag]? = some LightSourceFlagTest.body) {μ : ℕ → ℤ}
    {src src0 src1 L h histL histR p cap dst work U V : ℕ} (bits w0 w1 leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hp : 0 < p) (hh : h ≤ L) (hsrc : src + L ≤ work)
    (hsrc0 : src0 + L ≤ work) (hsrc1 : src1 + L ≤ work) (hleft : histL + p ≤ work) (hright : histR + p ≤ work)
    (hdst : dst + 2 ≤ work) (hspace : space work L U ≤ lim.space) (hword : (word L p U V cap : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src + i) = (bits i : ℤ)) (hread0 : ∀ i < L, μ (src0 + i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1 + i) = (w1 i : ℤ)) (hbitBound : ∀ i < L, bits i ≤ 1) (hbound0 : ∀ i < L, w0 i ≤ U)
    (hbound1 : ∀ i < L, w1 i ≤ U) (hcountL : ∀ r < p, μ (histL + r) = (leftCount r : ℤ))
    (hcountR : ∀ r < p, μ (histR + r) = (rightCount r : ℤ)) (hcountBoundL : ∀ r < p, leftCount r ≤ V)
    (hcountBoundR : ∀ r < p, rightCount r ≤ V) :
    Meets lim P pMain d [src, src0, src1, L, h, histL, histR, p, cap, dst, work] μ (time L U)
      (fun _ ν =>
        ν dst = (flag L h p cap bits w0 w1 leftCount : ℤ) ∧
          ν (dst + 1) = (flag L h p cap bits w1 w0 rightCount : ℤ) ∧ KeptBut μ ν work dst 2) :=
  by
  have hsp : work + 3 + (Nat.log 2 (L * U + 1) + 2) ≤ lim.space := hspace
  have hbudget (x : ℕ) (hx : x ≤ word L p U V cap) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hrowWord := hbudget (LightSourceRowScan.word L U) (by unfold word; omega)
  have hemWord : (4 * (L * U : ℕ) + 4 * p + 16 : ℤ) ≤ lim.word :=
    by
    have hh := hbudget (4 * (L * U) + 4 * p + 16) (by unfold word; omega)
    exact_mod_cast hh
  have hpre : Emod.Pre lim p (L * U) (work + 3) := ⟨hp, hw, hemWord, hsp⟩
  have hcBound := LightSourceRowScan.count_le bits hbitBound (j := L) le_rfl
  have hlBound := LightSourceRowScan.hash_le bits w0 w1 hbound0 hbound1 (j := L) le_rfl
  have hrBound := LightSourceRowScan.hash_le bits w1 w0 hbound1 hbound0 (j := L) le_rfl
  have hlAbs : |(LightSourceRowScan.hash bits w0 w1 L : ℤ)| ≤ ((L * U : ℕ) : ℤ) :=
    by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr hlBound
  have hrAbs : |(LightSourceRowScan.hash bits w1 w0 L : ℤ)| ≤ ((L * U : ℕ) : ℤ) :=
    by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr hrBound
  have htimeL := LightResidues.emodTime_le (p := p) hlAbs
  have htimeR := LightResidues.emodTime_le (p := p) hrAbs
  unfold emodTime LightResidues.residueBudget at htimeL htimeR
  simp only [Int.natAbs_natCast] at htimeL htimeR
  have hlog : Nat.log 2 (1 + L * U) = Nat.log 2 (L * U + 1) := by rw [Nat.add_comm]
  have hlLt := LightResidues.residue_lt hp 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)
  have hrLt := LightResidues.residue_lt hp 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)
  have hlCast := LightResidues.residue_cast hp 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)
  have hrCast := LightResidues.residue_cast hp 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)
  simp only [one_mul] at hlCast hrCast
  apply Meets.of_body hmain
  unfold body time
  have hr :=
    LightSourceRowScan.meets (d := d + 1) (μ := μ) (src := src) (src0 := src0) (src1 := src1) (L := L) (dst := work)
      (U := U) hrow bits w0 w1 hw (by omega) (by omega) (by omega) (by omega) hrowWord hbits hread0 hread1 hbitBound
      hbound0 hbound1
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
    | refine _root_.Light.Ends.callToThen (hr _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hr ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time] <;>
          omega)
    on_goal -1 =>
      (rintro q ν₁ ⟨cardRead, leftRead, rightRead, kept₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((emod_meets (x := (LightSourceRowScan.hash bits w0 w1 L : ℤ)) hem hpre hlAbs) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (emod_meets (x := (LightSourceRowScan.hash bits w0 w1 L : ℤ)) hem hpre hlAbs) ?_ ?_
          ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, leftRead, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [leftRead, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, leftRead, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time] <;>
          omega)
    on_goal -1 => (rintro l ν₂ ⟨lResult, kept₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  rw [← hlCast] at lResult
  subst l
  have rightRead₂ : ν₂ (work + 2) = (LightSourceRowScan.hash bits w1 w0 L : ℤ) := (kept₂ _ (by omega)).trans rightRead
  have rightAddr : ((work : ℤ) + 2).toNat = work + 2 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (Int.toNat_natCast (work + 2))
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((emod_meets (x := (LightSourceRowScan.hash bits w1 w0 L : ℤ)) hem hpre hrAbs) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (emod_meets (x := (LightSourceRowScan.hash bits w1 w0 L : ℤ)) hem hpre hrAbs) ?_ ?_
          ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rightRead₂, rightAddr,
            LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [rightRead₂, rightAddr, LightSourceRowScan.time, LightResidues.residueBudget,
              LightSourceFlagTest.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rightRead₂, rightAddr, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time] <;>
          omega)
    on_goal -1 => (rintro r ν₃ ⟨rResult, kept₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  rw [← hrCast] at rResult
  subst r
  have cardRead₃ : ν₃ work = (LightSourceRowScan.count bits L : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans cardRead)
  have countLRead :
    ν₃ (histL + LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)) =
      (leftCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)) : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans ((kept₁ _ (Or.inl (by omega))).trans (hcountL _ hlLt)))
  have countRRead :
    ν₃ (histR + LightResidues.residue p 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)) =
      (rightCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)) : ℤ) :=
    (kept₃ _ (by omega)).trans ((kept₂ _ (by omega)).trans ((kept₁ _ (Or.inl (by omega))).trans (hcountR _ hrLt)))
  have hflagWordL :=
    hbudget
      (LightSourceRowScan.count bits L + h +
            leftCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w0 w1 L : ℤ)) +
          cap +
        2)
      (by have := hcountBoundL _ hlLt; unfold word; omega)
  have hflagWordR :=
    hbudget
      (LightSourceRowScan.count bits L + h +
            rightCount (LightResidues.residue p 1 (LightSourceRowScan.hash bits w1 w0 L : ℤ)) +
          cap +
        2)
      (by have := hcountBoundR _ hrLt; unfold word; omega)
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
    |
      refine
        _root_.Light.Ends.callToThen ((LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordL) _ (by omega)) ?_ ?_
          ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordL) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cardRead₃, countLRead,
            LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cardRead₃, countLRead, LightSourceRowScan.time, LightResidues.residueBudget,
              LightSourceFlagTest.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cardRead₃, countLRead, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time] <;>
          omega)
    on_goal -1 => (rintro fl ν₄ ⟨flResult, hmem₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν₄
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
    |
      refine
        _root_.Light.Ends.callToThen ((LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordR) _ (by omega)) ?_ ?_
          ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightSourceFlagTest.meets (d := d + 1) hflag ν₃ hflagWordR) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cardRead₃, countRRead,
            LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cardRead₃, countRRead, LightSourceRowScan.time, LightResidues.residueBudget,
              LightSourceFlagTest.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cardRead₃, countRRead, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time] <;>
          omega)
    on_goal -1 => (rintro fr ν₅ ⟨frResult, hmem₅⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν₅
  have flEq : fl = (flag L h p cap bits w0 w1 leftCount : ℤ) := flResult
  have frEq : fr = (flag L h p cap bits w1 w0 rightCount : ℤ) := frResult
  have flBound := flag_le L h p cap bits w0 w1 leftCount
  have frBound := flag_le L h p cap bits w1 w0 rightCount
  have h1 := hbudget 1 (by unfold word; omega)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.storeToThen dst (flag L h p cap bits w0 w1 leftCount : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, flEq, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [flEq, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, flEq, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.storeToThen (dst + 1) (flag L h p cap bits w1 w0 rightCount : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, frEq, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [frEq, LightSourceRowScan.time, LightResidues.residueBudget, LightSourceFlagTest.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, frEq, LightSourceRowScan.time,
            LightResidues.residueBudget, LightSourceFlagTest.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine ⟨by simp, by simp, ?_⟩
  intro a ⟨ha, hout⟩
  simp only [Function.update_of_ne (show a ≠ dst + 1 by omega), Function.update_of_ne (show a ≠ dst by omega)]
  exact (kept₃ a (by omega)).trans ((kept₂ a (by omega)).trans (kept₁ a (Or.inl ha)))
end ThreeSum.LightSourceRowFlag
