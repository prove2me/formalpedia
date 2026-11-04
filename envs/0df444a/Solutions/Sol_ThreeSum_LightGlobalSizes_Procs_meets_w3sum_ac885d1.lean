-- Prove2me | solution 1 for ThreeSum.LightGlobalSizes.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:06.898007+00:00
-- url     : https://prove2.me/submissions/022a330f-2ebd-453d-a9c9-d74ca20185b4

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Definitions.Def_WeightedCache3SUM_Alias_2e17023b917df3d1
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightGlobalSizes
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {C p J mu dst : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d < lim.depth) (hC : 1 ≤ C) (hp : 1 ≤ p) (hspace : dst + 5 ≤ lim.space)
    (hword : (word C p J mu : ℤ) ≤ lim.word) :
    Meets lim P pMain d [C, p, J, mu, dst] μ (time C J mu)
      (fun r μ' => r = ((p ^ J : ℕ) : ℤ) ∧ Seg μ' dst (values C p J mu) ∧ SameOutside μ μ' dst 5) :=
  by
  have hMpos : 0 < C ^ J := Nat.pow_pos (by omega)
  have hRpos : 0 < p ^ J := Nat.pow_pos (by omega)
  have hDpos : 0 < divisor mu := Nat.two_pow_pos _
  have hroot : root C J ≤ C ^ J + 1 := by
    unfold root rootCeiling
    have hs := Nat.sqrt_le_self (C ^ J - 1)
    omega
  have hrootPos : 0 < root C J := rootCeiling_pos _
  have heLe : mu / 20 ≤ mu := Nat.div_le_self _ _
  have hnum : numerator C J mu ≤ C ^ J + divisor mu + 1 := by unfold numerator; omega
  have hband : band C J mu ≤ numerator C J mu := Nat.div_le_self _ _
  have hbound (x : ℕ) (hx : x ≤ word C p J mu) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hconst : (20 : ℤ) ≤ lim.word := hbound 20 (by unfold word; omega)
  have hCw := hbound C (by unfold word; omega)
  have hpw := hbound p (by unfold word; omega)
  have hJw := hbound J (by unfold word; omega)
  have hmuw := hbound mu (by unfold word; omega)
  have hMw := hbound (C ^ J) (by unfold word; omega)
  have hRw := hbound (p ^ J) (by unfold word; omega)
  have hMZpos : (0 : ℤ) < (C : ℤ) ^ J := by exact_mod_cast hMpos
  have hMZw : (C : ℤ) ^ J ≤ lim.word := by exact_mod_cast hMw
  have hRZpos : (0 : ℤ) < (p : ℤ) ^ J := by exact_mod_cast hRpos
  have hRZw : (p : ℤ) ^ J ≤ lim.word := by exact_mod_cast hRw
  have hDw := hbound (divisor mu) (by unfold word; omega)
  have hrw := hbound (root C J) (by unfold word; omega)
  have hnw := hbound (numerator C J mu) (by unfold word; omega)
  have hsumw := hbound (root C J + divisor mu) (by unfold word; omega)
  have hsumZw : (root C J : ℤ) + (divisor mu : ℤ) ≤ lim.word := by exact_mod_cast hsumw
  have hbw := hbound (band C J mu) (by unfold word; omega)
  have hew := hbound (mu / 20) (by unfold word; omega)
  have heZ : (0 : ℤ) ≤ (mu : ℤ) / 20 := by positivity
  have heZw : (mu : ℤ) / 20 ≤ lim.word := by exact_mod_cast hew
  have hpowC (i : ℕ) (hi : i ≤ J) : ((C ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hC hi)).trans hMw
  have hpowP (i : ℕ) (hi : i ≤ J) : ((p ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hp hi)).trans hRw
  have hpowD (i : ℕ) (hi : i ≤ mu / 20) : ((2 ^ i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hDw
  have hsub : ((C ^ J : ℕ) : ℤ) - 1 = ((C ^ J - 1 : ℕ) : ℤ) := by omega
  have hnumEq : (root C J : ℤ) + (divisor mu : ℤ) - 1 = (numerator C J mu : ℤ) :=
    by
    unfold numerator
    omega
  apply Meets.of_body S.main
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
    |
      refine
        _root_.Light.Ends.callToThen ((LightNatPower.meets (d := d + 1) S.power μ hJw hpowC) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightNatPower.meets (d := d + 1) S.power μ hJw hpowC) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNatPower.time, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNatPower.time, LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro mval μ₁ ⟨hmval, hmem₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₁
  have hmvalZ : mval = (C : ℤ) ^ J := by simpa only [Nat.cast_pow] using hmval
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
        _root_.Light.Ends.callToThen ((LightNatPower.meets (d := d + 1) S.power μ hJw hpowP) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightNatPower.meets (d := d + 1) S.power μ hJw hpowP) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNatPower.time, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNatPower.time, LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro rval μ₂ ⟨hrval, hmem₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  have hrvalZ : rval = (p : ℤ) ^ J := by simpa only [Nat.cast_pow] using hrval
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
          ((LightSmallDivide.meets (d := d + 1) (a := mu) (b := 20) S.divide μ (hbound _ (by unfold word; omega))) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightSmallDivide.meets (d := d + 1) (a := mu) (b := 20) S.divide μ (hbound _ (by unfold word; omega))) ?_ ?_
          ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNatPower.time, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNatPower.time, LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro e μ₃ ⟨he, hmem₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₃
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
        _root_.Light.Ends.callToThen ((LightNatPower.meets (d := d + 1) S.power μ hew hpowD) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (LightNatPower.meets (d := d + 1) S.power μ hew hpowD) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, he, LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [he, LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, he, LightNatPower.time,
            LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro dval μ₄ ⟨hdval, hmem₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₄
  have hdval' : dval = (divisor mu : ℤ) := hdval
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
          ((sqrt_meets (d := d + 1) (K := C ^ J - 1) S.sqrt μ (hbound _ (by unfold word; omega))) _ (by omega)) ?_ ?_ ?_
          ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (sqrt_meets (d := d + 1) (K := C ^ J - 1) S.sqrt μ (hbound _ (by unfold word; omega))) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmvalZ, hsub, LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hmvalZ, hsub, LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmvalZ, hsub, LightNatPower.time,
            LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro s μ₅ ⟨hs, hmem₅⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₅
  have hs' : s + 1 = (root C J : ℤ) := by simpa [root, rootCeiling] using congrArg (fun z : ℤ => z + 1) hs
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (root C J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs', LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hs', LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs', LightNatPower.time,
            LightSmallDivide.time] <;>
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
    refine _root_.Light.Ends.setToThen (numerator C J mu : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdval', hnumEq, LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hdval', hnumEq, LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdval', hnumEq, LightNatPower.time,
            LightSmallDivide.time] <;>
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
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightSmallDivide.meets (d := d + 1) (a := numerator C J mu) (b := divisor mu) S.divide μ
              (hbound _ (by unfold word; omega)))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightSmallDivide.meets (d := d + 1) (a := numerator C J mu) (b := divisor mu) S.divide μ
            (hbound _ (by unfold word; omega)))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdval', LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hdval', LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdval', LightNatPower.time,
            LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro bval μ₆ ⟨hbval, hmem₆⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₆
  have hbval' : bval = (band C J mu : ℤ) := hbval
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.storeToThen dst (C ^ J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmvalZ, LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hmvalZ, LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmvalZ, LightNatPower.time,
            LightSmallDivide.time] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 1) (p ^ J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrvalZ, LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hrvalZ, LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrvalZ, LightNatPower.time,
            LightSmallDivide.time] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 2) (root C J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightNatPower.time, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightNatPower.time, LightSmallDivide.time] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 3) (divisor mu : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdval', LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hdval', LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdval', LightNatPower.time,
            LightSmallDivide.time] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 4) (band C J mu : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbval', LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbval', LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbval', LightNatPower.time,
            LightSmallDivide.time] <;>
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
    refine _root_.Light.Ends.setToThen (p ^ J : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrvalZ, LightNatPower.time,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hrvalZ, LightNatPower.time, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrvalZ, LightNatPower.time,
            LightSmallDivide.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact
    ⟨rfl, by simp [values, seg_cons], by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_10858688129295574720 hx_p2m_10858688129295574720
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_10195453533263706299);
                  (try have := h_p2m_10195453533263706299 x_p2m_10858688129295574720 (by omega));
                  revert h_p2m_10195453533263706299)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_10858688129295574720;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_5136683869609203295);
                  (try have := h_p2m_5136683869609203295 x_p2m_10858688129295574720 (by omega));
                  revert h_p2m_5136683869609203295)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_10921254571393915071);
                  (try have := h_p2m_10921254571393915071 x_p2m_10858688129295574720 (by omega));
                  revert h_p2m_10921254571393915071)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))⟩
end Procs
end ThreeSum.LightGlobalSizes
