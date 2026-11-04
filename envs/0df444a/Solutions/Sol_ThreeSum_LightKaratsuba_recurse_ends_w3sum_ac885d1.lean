-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.recurse_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:39.89247+00:00
-- url     : https://prove2.me/submissions/b183bca4-f3e3-4de9-b926-a4569eb2c0fd

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Definitions.Def_WeightedCache3SUM_Alias_1ef7cad0b2ec0925
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_588c6b2213aee404
import Theorems.Thm_ThreeSum_LightKaratsuba_wordBound_monoU
import Theorems.Thm_ThreeSum_LightKaratsuba_wordBound_child
import Theorems.Thm_ThreeSum_LightKaratsuba_wordBound_ge_twice
import Theorems.Thm_ThreeSum_LightKaratsuba_ten_temp_le_word
import Theorems.Thm_ThreeSum_LightKaratsuba_linear_plus_segment
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_Seg_congr
import Definitions.Def_WeightedCache3SUM_Alias_11e81edb1af807be
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_drop
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_plus
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_take
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Definitions.Def_WeightedCache3SUM_Alias_a7357418fd94c5da
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}
set_option maxHeartbeats 2000000
namespace ThreeSum.LightKaratsuba
theorem _root_.solution (C : Procs P pSelf pHalf pLinear pFill) {d k m a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hmPow : m = 2 ^ k) (hw : (lim.space : ℤ) ≤ lim.word) (hAlen : as.length = 2 * m) (hBlen : bs.length = 2 * m)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs) (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 * m ≤ work) (hbf : b + 2 * m ≤ work) (hof : out + 2 * (2 * m) ≤ work)
    (hspace : work + 8 * (2 * m) ≤ lim.space) (hword : (wordBound (2 * m) U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (ih :
      ∀ (a' b' out' work' U' : ℕ) (as' bs' : List ℤ) (μ' : ℕ → ℤ),
        as'.length = m →
          bs'.length = m →
            Seg μ' a' as' →
              Seg μ' b' bs' →
                CoeffBound as' (U' : ℤ) →
                  CoeffBound bs' (U' : ℤ) →
                    a' + m ≤ work' →
                      b' + m ≤ work' →
                        out' + 2 * m ≤ work' →
                          work' + 8 * m ≤ lim.space →
                            (wordBound m U' : ℤ) ≤ lim.word →
                              Meets lim P pSelf (d + 1) [m, a', b', out', work'] μ' (time k)
                                (fun _ μ'' => Result μ' out' m work' as' bs' μ'')) :
    Ends lim P d (recurseBody pSelf pHalf pLinear pFill) ⟨frame [2 * m, a, b, out, work], μ⟩ (time (k + 1) - 4)
      (fun σ' => Result μ out (2 * m) work as bs σ'.mem) :=
  by
  have hm : 0 < m := hmPow ▸ Nat.pow_pos (by decide)
  have hAU0 := hA.take m
  have hAU1 := hA.drop m
  have hBU0 := hB.take m
  have hBU1 := hB.drop m
  have hAs : CoeffBound (plus (as.take m) (as.drop m)) ((2 * U : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using hAU0.plus hAU1
  have hBs : CoeffBound (plus (bs.take m) (bs.drop m)) ((2 * U : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using hBU0.plus hBU1
  have ha0 : (as.take m).length = m := by simp only [List.length_take, hAlen]; omega
  have ha1 : (as.drop m).length = m := by simp only [List.length_drop, hAlen]; omega
  have hb0 : (bs.take m).length = m := by simp only [List.length_take, hBlen]; omega
  have hb1 : (bs.drop m).length = m := by simp only [List.length_drop, hBlen]; omega
  have has : (plus (as.take m) (as.drop m)).length = m := by simp only [length_plus, ha0, ha1, max_self]
  have hbs : (plus (bs.take m) (bs.drop m)).length = m := by simp only [length_plus, hb0, hb1, max_self]
  have hword2 : 2 * (U : ℤ) ≤ lim.word :=
    by
    have hh : 2 * (U : ℤ) ≤ wordBound (2 * m) U := by exact_mod_cast wordBound_ge_twice (2 * m) U (by omega)
    exact hh.trans hword
  have hchild2 : (wordBound m (2 * U) : ℤ) ≤ lim.word :=
    by
    have hc : (wordBound m (2 * U) : ℤ) ≤ wordBound (2 * m) U := by exact_mod_cast wordBound_child m U
    exact hc.trans hword
  have hchild1 : (wordBound m U : ℤ) ≤ lim.word :=
    by
    have hc : (wordBound m U : ℤ) ≤ wordBound m (2 * U) := by
      exact_mod_cast wordBound_monoU (n := m) (by omega : U ≤ 2 * U)
    exact hc.trans hchild2
  have hhalfeq : (2 * m + 1) / 2 = m := by omega
  have hhalfword : ((2 * m + 1 : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : ((2 * m + 1 : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (show 2 * m + 1 ≤ lim.space by omega)
    exact hh.trans hw
  have hhalf := half_meets (lim := lim) (d := d + 1) C.half μ (h := 2 * m) hhalfword
  simp only [halfTime, hhalfeq] at hhalf
  unfold recurseBody
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
    | refine _root_.Light.Ends.callToThen (hhalf _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hhalf ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time] <;> omega)
    on_goal -1 => (rintro _ μ₀ ⟨rfl, hμ₀⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₀
  have hsA0 := hAseg.take m
  have hsA1 := hAseg.drop m
  have hsumA :=
    LightArray.linear_bounded_meets (d := d + 1) C.linear (μ := μ) (srcA := a) (srcB := a + m) (dst :=
      work + 3 * (2 * m)) (n := m) (U := U) (c := 1) hw (by omega) (by omega) (by omega) (Or.inr (by omega))
      (Or.inr (by omega)) (by norm_num) hword2
      (fun i hi => ⟨by rw [hsA0.getD (by omega) 0]; exact hAU0 i, by rw [hsA1.getD (by omega) 0]; exact hAU1 i⟩)
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
    | refine _root_.Light.Ends.callToThen (hsumA _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsumA ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₁ ⟨hrA, hkA⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hsuma := linear_plus_segment hsA0 hsA1 ha0 ha1 hrA
  have hBseg1 : Seg μ₁ b bs := hBseg.congr (fun i hi => hkA _ (by omega))
  have hsB0 := hBseg1.take m
  have hsB1 := hBseg1.drop m
  have hsumB :=
    LightArray.linear_bounded_meets (d := d + 1) C.linear (μ := μ₁) (srcA := b) (srcB := b + m) (dst :=
      work + 3 * (2 * m) + m) (n := m) (U := U) (c := 1) hw (by omega) (by omega) (by omega) (Or.inr (by omega))
      (Or.inr (by omega)) (by norm_num) hword2
      (fun i hi => ⟨by rw [hsB0.getD (by omega) 0]; exact hBU0 i, by rw [hsB1.getD (by omega) 0]; exact hBU1 i⟩)
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
    | refine _root_.Light.Ends.callToThen (hsumB _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hsumB ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₂ ⟨hrB, hkB⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hsumb := linear_plus_segment hsB0 hsB1 hb0 hb1 hrB
  have hsuma2 : Seg μ₂ (work + 3 * (2 * m)) (plus (as.take m) (as.drop m)) := hsuma.congr (fun i hi => hkB _ (by omega))
  have hAseg2 : Seg μ₂ a as := hAseg.congr (fun i hi => (hkB _ (by omega)).trans (hkA _ (by omega)))
  have hBseg2 : Seg μ₂ b bs := hBseg1.congr (fun i hi => hkB _ (by omega))
  have hprod0 :=
    ih a b work (work + 4 * (2 * m)) U (as.take m) (bs.take m) μ₂ ha0 hb0 (hAseg2.take m) (hBseg2.take m) hAU0 hBU0
      (by omega) (by omega) (by omega) (by omega) hchild1
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
    | refine _root_.Light.Ends.callToThen (hprod0 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hprod0 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₃ ⟨hp0, hkp0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hAseg3 : Seg μ₃ a as := hAseg2.congr (fun i hi => hkp0 _ ⟨by omega, by omega⟩)
  have hBseg3 : Seg μ₃ b bs := hBseg2.congr (fun i hi => hkp0 _ ⟨by omega, by omega⟩)
  have hprod2 :=
    ih (a + m) (b + m) (work + 2 * m) (work + 4 * (2 * m)) U (as.drop m) (bs.drop m) μ₃ ha1 hb1 (hAseg3.drop m)
      (hBseg3.drop m) hAU1 hBU1 (by omega) (by omega) (by omega) (by omega) hchild1
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
    | refine _root_.Light.Ends.callToThen (hprod2 _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hprod2 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₄ ⟨hp2, hkp2⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hp04 : ProductAt μ₄ work m (as.take m) (bs.take m) := hp0.congr (fun j hj => hkp2 _ ⟨by omega, by omega⟩)
  have hsuma4 : Seg μ₄ (work + 3 * (2 * m)) (plus (as.take m) (as.drop m)) :=
    hsuma2.congr (fun i hi => (hkp2 _ ⟨by omega, by omega⟩).trans (hkp0 _ ⟨by omega, by omega⟩))
  have hsumb4 : Seg μ₄ (work + 3 * (2 * m) + m) (plus (bs.take m) (bs.drop m)) :=
    hsumb.congr (fun i hi => (hkp2 _ ⟨by omega, by omega⟩).trans (hkp0 _ ⟨by omega, by omega⟩))
  have hprodm :=
    ih (work + 3 * (2 * m)) (work + 3 * (2 * m) + m) (work + 2 * (2 * m)) (work + 4 * (2 * m)) (2 * U)
      (plus (as.take m) (as.drop m)) (plus (bs.take m) (bs.drop m)) μ₄ has hbs hsuma4 hsumb4 hAs hBs (by omega)
      (by omega) (by omega) (by omega) hchild2
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
    | refine _root_.Light.Ends.callToThen (hprodm _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen hprodm ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, LightArray.linearTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [time, LightArray.linearTime] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, time, LightArray.linearTime] <;> omega)
    on_goal -1 => (rintro _ μ₅ ⟨hpm, hkpm⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hp05 : ProductAt μ₅ work m (as.take m) (bs.take m) := hp04.congr (fun j hj => hkpm _ ⟨by omega, by omega⟩)
  have hp25 : ProductAt μ₅ (work + 2 * m) m (as.drop m) (bs.drop m) :=
    hp2.congr (fun j hj => hkpm _ ⟨by omega, by omega⟩)
  have htword : 10 * ((4 * (2 * m) * U ^ 2 : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : 10 * ((4 * (2 * m) * U ^ 2 : ℕ) : ℤ) ≤ wordBound (2 * m) U := by
      exact_mod_cast ten_temp_le_word (2 * m) U (by omega)
    exact hh.trans hword
  have htemp :
    ∀ i < 2 * m,
      |μ₅ (work + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) ∧
        |μ₅ (work + 2 * m + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) ∧
          |μ₅ (work + 2 * (2 * m) + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) :=
    by
    intro i hi
    have h₀ := hp05.bound ha0.le hb0.le hAU0 hBU0 i hi
    have h₂ := hp25.bound ha1.le hb1.le hAU1 hBU1 i hi
    have hₘ := hpm.bound has.le hbs.le hAs hBs i hi
    push_cast at hₘ ⊢
    constructor
    · nlinarith [sq_nonneg (U : ℤ)]
    constructor
    · nlinarith [sq_nonneg (U : ℤ)]
    · nlinarith
  refine
    (join_ends C.linear C.fill (n := 2 * m) (half := m) (U := 4 * (2 * m) * U ^ 2) (by omega) rfl hw hof (by omega)
          htword htemp hd).mono
      (by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time, joinTime,
              LightArray.linearTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time, joinTime, LightArray.linearTime] <;>
              first
              | omega
              | (ring_nf; omega)))
      ?_
  intro σ' hj
  constructor
  · intro j hjj
    exact (hj.1 j hjj).trans (joined_product rfl hAlen hBlen hp05 hp25 hpm j)
  · intro j hjj
    rw [hj.2 j hjj, hkpm j ⟨by omega, by omega⟩, hkp2 j ⟨by omega, by omega⟩, hkp0 j ⟨by omega, by omega⟩,
      hkB j (by omega), hkA j (by omega)]
end ThreeSum.LightKaratsuba
