-- Prove2me | solution 1 for ThreeSum.LightScales.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:17.257934+00:00
-- url     : https://prove2.me/submissions/d3c308d6-fd98-41c2-9f1e-352fec908102

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_ThreeSum_LightScales_inputBits_le_self
import Theorems.Thm_ThreeSum_LightScales_microSize_le_self
import Theorems.Thm_ThreeSum_LightScales_microHalf_le_self
import Theorems.Thm_ThreeSum_LightScales_blockCount_le
import Theorems.Thm_ThreeSum_LightScales_totalSize_le_self
import Theorems.Thm_ThreeSum_LightScales_half_cbrtLeast
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_9d7f2f54359d5431
import Theorems.Thm_Light_cbrtLeast_le_self
import Definitions.Def_WeightedCache3SUM_Alias_11e81edb1af807be
import Definitions.Def_WeightedCache3SUM_Alias_5c7a134a153cf44a
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Definitions.Def_WeightedCache3SUM_Alias_3f3326597d4f4ccd
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightScales
theorem _root_.solution {pMain pLog pCube pHalf pDiv : ℕ} (hmain : P[pMain]? = some (body pLog pCube pHalf pDiv))
    (hlog : P[pLog]? = some log2Body) (hcube : P[pCube]? = some cbrtCeilBody) (hhalf : P[pHalf]? = some halfBody)
    (hdiv : P[pDiv]? = some LightSmallDivide.body) {μ : ℕ → ℤ} {n dst d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : dst + 5 ≤ lim.space) (hword : ((1000 * (n + 1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [n, dst] μ (time n)
      (fun r μ' => r = (mu n : ℤ) ∧ Seg μ' dst (values n) ∧ SameOutside μ μ' dst 5) :=
  by
  have hm : (inputBits n) ≤ n := inputBits_le_self n
  have hm₀ : microSize (inputBits n) ≤ (inputBits n) := microSize_le_self (inputBits n)
  have hh : microHalf (inputBits n) ≤ (inputBits n) := microHalf_le_self (inputBits n)
  have hJ : blockCount (inputBits n) ≤ 20 * (inputBits n) := blockCount_le (inputBits n)
  have hmu : totalSize (inputBits n) ≤ (inputBits n) := totalSize_le_self (inputBits n)
  have hu : cbrtLeast ((inputBits n) + 1) ≤ (inputBits n) + 1 := cbrtLeast_le_self ((inputBits n) + 1)
  have hall (x : ℕ) (hx : x ≤ 1000 * (n + 1)) : (x : ℤ) ≤ lim.word :=
    by
    have hz : (x : ℤ) ≤ ((1000 * (n + 1) : ℕ) : ℤ) := by exact_mod_cast hx
    exact hz.trans hword
  have hmWord := hall (inputBits n) (by omega)
  have hhWord := hall (microHalf (inputBits n)) (by omega)
  have hm₀Word := hall (microSize (inputBits n)) (by omega)
  have hJWord := hall (blockCount (inputBits n)) (by omega)
  have hmuWord := hall (totalSize (inputBits n)) (by omega)
  have hdenWord : (100 : ℤ) * (microSize (inputBits n) : ℤ) ≤ lim.word := by
    simpa using hall (100 * microSize (inputBits n)) (by omega)
  have hproductWord : (blockCount (inputBits n) : ℤ) * (microSize (inputBits n) : ℤ) ≤ lim.word := by
    simpa [totalSize] using hmuWord
  have hproductNonneg : (0 : ℤ) ≤ (blockCount (inputBits n) : ℤ) * (microSize (inputBits n) : ℤ) := by positivity
  have hsizeEq : (2 : ℤ) * (microHalf (inputBits n) : ℤ) = (microSize (inputBits n) : ℤ) := by
    simp [microSize, microHalf]
  have hcountEq :
    (20 : ℤ) * ((inputBits n / (100 * microSize (inputBits n)) : ℕ) : ℤ) = (blockCount (inputBits n) : ℤ) := by
    simp [blockCount]
  have hproductEq : (blockCount (inputBits n) : ℤ) * (microSize (inputBits n) : ℤ) = (totalSize (inputBits n) : ℤ) := by
    simp [totalSize]
  apply Meets.of_body hmain
  unfold body time
  have hlogCall := log2_meets (d := d + 1) (x := n) hlog μ (hall _ (by omega))
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
    | refine _root_.Light.Ends.callToThen (hlogCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hlogCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cbrtCeilTime, halfTime,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cbrtCeilTime, halfTime, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cbrtCeilTime, halfTime,
            LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro bits μ₁ ⟨hbits, hmem₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₁
  have hbits' : bits = ((inputBits n) : ℤ) := by simpa [inputBits, Nat.log2_eq_log_two] using hbits
  have hcubeCall := cbrtCeil_meets (d := d + 1) (n := (inputBits n) + 1) hcube μ (hall _ (by omega))
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
    | refine _root_.Light.Ends.callToThen (hcubeCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hcubeCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbits', cbrtCeilTime, halfTime,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbits', cbrtCeilTime, halfTime, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbits', cbrtCeilTime, halfTime,
            LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro cube μ₂ ⟨hc, hmem₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  have hhalfCall := half_meets (d := d + 1) (h := cbrtLeast ((inputBits n) + 1)) hhalf μ (hall _ (by omega))
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
    | refine _root_.Light.Ends.callToThen (hhalfCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hhalfCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hc, cbrtCeilTime, halfTime,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hc, cbrtCeilTime, halfTime, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc, cbrtCeilTime, halfTime,
            LightSmallDivide.time] <;>
          omega)
    on_goal -1 => (rintro half μ₃ ⟨hv, hmem₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₃
  have hv' : half = ((microHalf (inputBits n) + 1 : ℕ) : ℤ) := by simpa [half_cbrtLeast] using hv
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (microHalf (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hv', cbrtCeilTime, halfTime,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hv', cbrtCeilTime, halfTime, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hv', cbrtCeilTime, halfTime,
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
    refine _root_.Light.Ends.setToThen (microSize (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsizeEq, cbrtCeilTime, halfTime,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hsizeEq, cbrtCeilTime, halfTime, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsizeEq, cbrtCeilTime, halfTime,
            LightSmallDivide.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  have hdivCall :=
    LightSmallDivide.meets (d := d + 1) (a := (inputBits n)) (b := 100 * microSize (inputBits n)) hdiv μ
      (hall _ (by omega))
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
    | refine _root_.Light.Ends.callToThen (hdivCall _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hdivCall ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbits', cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbits', cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbits', cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero] <;>
          omega)
    on_goal -1 => (rintro q μ₄ ⟨hq, hmem₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₄
  have hquotNonneg : (0 : ℤ) ≤ (inputBits n : ℤ) / (100 * (microSize (inputBits n) : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv] using
      (Int.natCast_nonneg (inputBits n / (100 * microSize (inputBits n))))
  have hquotWord : (20 : ℤ) * ((inputBits n : ℤ) / (100 * (microSize (inputBits n) : ℤ))) ≤ lim.word := by
    simpa only [blockCount, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv] using hJWord
  have hqZ : q = (inputBits n : ℤ) / (100 * (microSize (inputBits n) : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv] using hq
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (blockCount (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hqZ, hcountEq, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hqZ, hcountEq, cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hqZ, hcountEq, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero] <;>
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
    refine _root_.Light.Ends.setToThen (totalSize (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hproductEq, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hproductEq, cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hproductEq, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero] <;>
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
    refine _root_.Light.Ends.storeToThen dst ((inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbits', cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hbits', cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbits', cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 1) (microHalf (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cbrtCeilTime, halfTime, LightSmallDivide.time,
            muZero] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 2) (microSize (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cbrtCeilTime, halfTime, LightSmallDivide.time,
            muZero] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 3) (blockCount (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cbrtCeilTime, halfTime, LightSmallDivide.time,
            muZero] <;>
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
    refine _root_.Light.Ends.storeToThen (dst + 4) (totalSize (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cbrtCeilTime, halfTime, LightSmallDivide.time,
            muZero] <;>
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
    refine _root_.Light.Ends.setToThen (totalSize (inputBits n) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, cbrtCeilTime, halfTime,
            LightSmallDivide.time, muZero]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [cbrtCeilTime, halfTime, LightSmallDivide.time, muZero] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, cbrtCeilTime, halfTime, LightSmallDivide.time,
            muZero] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    ⟨by simp [mu], ?_, by
      ( try refine _root_.Light.SameOn.cell ?_
        intro x_p2m_17151795883310691848 hx_p2m_17151795883310691848
        first
        | ((  repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_17107844187396732588);
                  (try have := h_p2m_17107844187396732588 x_p2m_17151795883310691848 (by omega));
                  revert h_p2m_17107844187396732588)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        |
          (simp [] at hx_p2m_17151795883310691848;
            ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_18289632499786071000);
                  (try have := h_p2m_18289632499786071000 x_p2m_17151795883310691848 (by omega));
                  revert h_p2m_18289632499786071000)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
        | ( ( repeat
                ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_11517749340592794852);
                  (try have := h_p2m_11517749340592794852 x_p2m_17151795883310691848 (by omega));
                  revert h_p2m_11517749340592794852)
              intros
              try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
            fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                        SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                        its condition K x does not follow from the hypotheses."))⟩
  simp [values, seg_cons, muZero, mu]
end ThreeSum.LightScales
