-- Prove2me | solution 1 for ThreeSum.LightExtensionMultiplyCell.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:34.427006+00:00
-- url     : https://prove2.me/submissions/ba5e9a0e-4ac7-4323-bb03-b9612a3af4d1

import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_header_kept
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMultiplyCell
open Light LightExtensionQuotientPredicate
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000
attribute [local instance] ThreeSum.LightExtensionMultiplyCell._p2m_local_instance_2d48f70718_8
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionMultiplyCell
theorem _root_.solution {proc pDecode pSearch pDigit pDivide ctx q x y : ℕ} (C : Layout)
    (hmain : P[proc]? = some (body pDecode pSearch pDigit))
    (hdecode : P[pDecode]? = some (LightCoefficientDecode.body pDigit))
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide)) (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ) (mul : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 7 < lim.depth)
    (hp : 1 < C.p) (hq : 0 < q) (hx : x < q) (hy : y < q) (H : Seg μ ctx (header C)) (hctx : ctx + 10 ≤ C.a)
    (hpow : C.powers + (2 * C.dim + 1) ≤ C.a) (hmod : C.modulus + (C.dim + 1) ≤ C.a) (hab : C.a + C.dim ≤ C.b)
    (hbh : C.b + C.dim ≤ C.h) (hh : C.h + C.dim ≤ C.remainder) (hr : C.remainder + 2 * C.dim ≤ C.productWork)
    (hprod : C.productWork + 2 * C.dim ≤ C.sumWork) (hspace : C.sumWork + 2 * C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2 * C.dim, μ (C.powers + i) = ((C.p ^ i : ℕ) : ℤ))
    (hfRead : ∀ i < C.dim + 1, μ (C.modulus + i) = (f i : ℤ)) (hfBound : ∀ i < C.dim + 1, f i < C.p)
    (hword : (word C q ctx : ℤ) ≤ lim.word)
    (hspec :
      ∀ a < q,
        ∀ b < q,
          let z :=
            LightPairSearch.first
              (LightPairSearch.goodCode q (LightExtensionQuotientSearch.good C (digits C.p a) (digits C.p b) f)) (q * q)
          0 < z ∧ z ≤ q * q ∧ (z - 1) % q = mul a b)
    (hsearch :
      ∀ ν,
        Seg ν ctx (header C) →
          (∀ i ≤ 2 * C.dim, ν (C.powers + i) = ((C.p ^ i : ℕ) : ℤ)) →
            (∀ i < C.dim, ν (C.a + i) = (digits C.p x i : ℤ)) →
              (∀ i < C.dim, ν (C.b + i) = (digits C.p y i : ℤ)) →
                (∀ i < C.dim + 1, ν (C.modulus + i) = (f i : ℤ)) →
                  Meets lim P pSearch (depth + 1) [q, ctx] ν (searchTime C q)
                    (fun z ξ =>
                      z =
                          (LightPairSearch.first
                              (LightPairSearch.goodCode q
                                (LightExtensionQuotientSearch.good C (digits C.p x) (digits C.p y) f))
                              (q * q) :
                            ℤ) ∧
                        Kept ν ξ C.h)) :
    Meets lim P proc depth [x, y, ctx, C.p, C.dim, C.powers, C.a, C.b, q] μ (time C q)
      (fun z ν => z = (mul x y : ℤ) ∧ Kept μ ν C.a) :=
  by
  have hbudget (n : ℕ) (hn : n ≤ word C q ctx) : (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hn).trans hword
  have hdword : (LightCoefficientDecode.word C.dim C.p q 0 1 : ℤ) ≤ lim.word := hbudget _ (by unfold word; omega)
  have hwx : (LightCoefficientDecode.word C.dim C.p x 0 1 : ℤ) ≤ lim.word := by
    apply hbudget
    unfold word LightCoefficientDecode.word; omega
  have hwy : (LightCoefficientDecode.word C.dim C.p y 0 1 : ℤ) ≤ lim.word := by
    apply hbudget
    unfold word LightCoefficientDecode.word; omega
  have hs := hspec x hx y hy
  let z :=
    LightPairSearch.first
      (LightPairSearch.goodCode q (LightExtensionQuotientSearch.good C (digits C.p x) (digits C.p y) f)) (q * q)
  have hzpos : 0 < z := hs.1
  have hzle : z ≤ q * q := hs.2.1
  have hzmod : (z - 1) % q = mul x y := hs.2.2
  have hzw : ((z : ℕ) : ℤ) ≤ lim.word := hbudget _ (by unfold word; omega)
  have hzmw : (LightRadixDigit.word (z - 1) 1 q : ℤ) ≤ lim.word := by
    apply hbudget; unfold word LightRadixDigit.word
    omega
  have hdecx :=
    LightCoefficientDecode.meets (d := depth + 1) (W := C.dim) (p := C.p) (k := x) (powers := C.powers) (start := 0)
      (stride := 1) (dst := C.a) (n := C.dim) hdecode hdigit hdivide hw (by omega) (by omega) (by omega) (by omega)
      (Or.inl (by omega)) hwx (by intro i hi; omega) (fun i hi => hpowRead i (by omega))
  have hdecTime (k : ℕ) (hk : k ≤ q) : LightCoefficientDecode.time C.dim k ≤ LightCoefficientDecode.time C.dim q :=
    by
    unfold LightCoefficientDecode.time LightRadixDigit.time
    gcongr
  apply Meets.of_body hmain
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
    first
    | refine _root_.Light.Ends.callToThen ((hdecx.mono_time (hdecTime x hx.le)) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hdecx.mono_time (hdecTime x hx.le)) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightCoefficientDecode.time,
            LightRadixDigit.time, pow_two]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightCoefficientDecode.time, LightRadixDigit.time, pow_two] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightCoefficientDecode.time,
            LightRadixDigit.time, pow_two] <;> omega)
    on_goal -1 => (rintro X μ₁ ⟨hxValues, keep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have k1 : Kept μ μ₁ C.a := fun a ha => keep₁ a (Or.inl ha)
  have pow₁ (i : ℕ) (hi : i ≤ 2 * C.dim) := (k1 _ (by omega)).trans (hpowRead i hi)
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
    |
      refine
        _root_.Light.Ends.callToThen
          (((LightCoefficientDecode.meets (d := depth + 1) (W := C.dim) (p := C.p) (k := y) (powers := C.powers)
                  (start := 0) (stride := 1) (dst := C.b) (n := C.dim) hdecode hdigit hdivide hw (by omega) (by omega)
                  (by omega) (by omega) (Or.inl (by omega)) hwy (by intro i hi; omega)
                  (fun i hi => pow₁ i (by omega))).mono_time
              (hdecTime y hy.le))
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightCoefficientDecode.meets (d := depth + 1) (W := C.dim) (p := C.p) (k := y) (powers := C.powers)
                (start := 0) (stride := 1) (dst := C.b) (n := C.dim) hdecode hdigit hdivide hw (by omega) (by omega)
                (by omega) (by omega) (Or.inl (by omega)) hwy (by intro i hi; omega)
                (fun i hi => pow₁ i (by omega))).mono_time
            (hdecTime y hy.le))
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightCoefficientDecode.time,
            LightRadixDigit.time, pow_two]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightCoefficientDecode.time, LightRadixDigit.time, pow_two] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightCoefficientDecode.time,
            LightRadixDigit.time, pow_two] <;> omega)
    on_goal -1 => (rintro Y μ₂ ⟨hyValues, keep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have k2 : Kept μ₁ μ₂ C.b := fun a ha => keep₂ a (Or.inl ha)
  have H₂ := header_kept (header_kept H hctx k1) (by omega) k2
  have pow₂ (i : ℕ) (hi : i ≤ 2 * C.dim) := (k2 _ (by omega)).trans (pow₁ i hi)
  have x₂ (i : ℕ) (hi : i < C.dim) : μ₂ (C.a + i) = (digits C.p x i : ℤ) := by
    rw [k2 _ (by omega)]
    simpa [digits] using hxValues i hi
  have y₂ (i : ℕ) (hi : i < C.dim) : μ₂ (C.b + i) = (digits C.p y i : ℤ) := by simpa [digits] using hyValues i hi
  have f₂ (i : ℕ) (hi : i < C.dim + 1) := (k2 _ (by omega)).trans ((k1 _ (by omega)).trans (hfRead i hi))
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
    | refine _root_.Light.Ends.callToThen ((hsearch μ₂ H₂ pow₂ x₂ y₂ f₂) _ (by omega)) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen (hsearch μ₂ H₂ pow₂ x₂ y₂ f₂) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [searchTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
    on_goal -1 => (rintro Z μ₃ ⟨hZ, keep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hZ' : Z = (z : ℤ) := hZ
  subst Z
  have hsub : (z : ℤ) - 1 = ((z - 1 : ℕ) : ℤ) := by omega
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
    |
      refine
        _root_.Light.Ends.callToThen
          ((LightRadixDigit.meets (d := depth + 1) (k := z - 1) (b := 1) (p := q) hdigit hdivide μ₃ (by omega) hzmw) _
            (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (LightRadixDigit.meets (d := depth + 1) (k := z - 1) (b := 1) (p := q) hdigit hdivide μ₃ (by omega) hzmw) ?_
          ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsub, LightRadixDigit.time, hzle, pow_two]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hsub, LightRadixDigit.time, hzle, pow_two] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsub, LightRadixDigit.time, hzle, pow_two] <;> omega)
    on_goal -1 => (rintro R ν ⟨hR, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  refine ⟨?_, ?_⟩
  · simpa [hzmod] using hR
  · intro a ha
    exact (keep₃ a (by omega)).trans ((k2 a (by omega)).trans (k1 a ha))
end ThreeSum.LightExtensionMultiplyCell
