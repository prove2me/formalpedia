-- Prove2me | solution 1 for ThreeSum.LightExtensionMultiplyTable.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:22:39.697398+00:00
-- url     : https://prove2.me/submissions/bc88a7ec-7322-44bf-bd8f-7871f0bea410

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyCell
import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Theorems.Thm_Light_LocalsBut_update
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_frame_append_zeros
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
import Theorems.Thm_ThreeSum_LightExtensionMultiplyCell_meets
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_Procs_meets
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
open ThreeSum ThreeSum.LightExtensionMultiplyTable
attribute [local instance] ThreeSum.LightExtensionMultiplyTable._p2m_local_instance_2a3ffe096f_5
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionMultiplyTable
theorem _root_.solution {proc pCell pDigit pDivide q ctx p dim powers a b table T : ℕ}
    (hp : P[proc]? = some (body pCell pDigit pDivide)) (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : depth + 1 < lim.depth) (hq : 0 < q) (hspace : table + q * q ≤ lim.space) (hctxSpace : ctx ≤ lim.space)
    (hpowersSpace : powers ≤ lim.space) (haSpace : a ≤ lim.space) (hbSpace : b ≤ lim.space)
    (hword : (word q ctx p dim powers a b : ℤ) ≤ lim.word) (hmul : ∀ x < q, ∀ y < q, mul x y < q)
    (hcell :
      ∀ x < q,
        ∀ y < q,
          ∀ ν,
            Kept μ ν table →
              Meets lim P pCell (depth + 1) [x, y, ctx, p, dim, powers, a, b, q] ν T
                (fun z ξ => z = (mul x y : ℤ) ∧ Kept ν ξ (table + q * q))) :
    Meets lim P proc depth [q, ctx, p, dim, powers, a, b, table] μ (time q T)
      (fun _ ν => (∀ x < q, ∀ y < q, ν (table + x * q + y) = (mul x y : ℤ)) ∧ Kept μ ν table) :=
  by
  have hb (z : ℕ) (hz : z ≤ word q ctx p dim powers a b) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hctxWord := (Int.ofNat_le.mpr hctxSpace).trans hw
  have hpowersWord := (Int.ofNat_le.mpr hpowersSpace).trans hw
  have haWord := (Int.ofNat_le.mpr haSpace).trans hw
  have hbWord := (Int.ofNat_le.mpr hbSpace).trans hw
  have hqWord := hb q (by unfold word; omega)
  have hQQWord := hb (q * q) (by unfold word; omega)
  apply Meets.of_body hp
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
    refine _root_.Light.Ends.setToThen (q * q : ℕ) ?_ ?_ ?_
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
  refine
    Ends.for
      (fun i σ =>
        ∃ X Y Z ν,
          σ = ⟨frame [q, ctx, p, dim, powers, a, b, table, q * q, i, X, Y, Z], ν⟩ ∧
            (∀ j < i, ν (table + j) = (mul (j / q) (j % q) : ℤ)) ∧ Kept μ ν table)
      (q * q) (T + 60 * (q * q) + 390) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, 0, 0, μ, ?_, ?_, SameOn.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 3).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨oldX, oldY, oldZ, ν, rfl, written, kept⟩
    have hx : i / q < q := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    have hy : i % q < q := Nat.mod_lt _ hq
    have hquotient : i / q ≤ i := Nat.div_le_self i q
    have hquotientInt : (i : ℤ) / (q : ℤ) ≤ (i : ℤ) := by exact_mod_cast hquotient
    have hiWord := hb i (by unfold word; omega)
    have hdivWord := hb (i + q + 2) (by unfold word; omega)
    have hdigitWord : (LightRadixDigit.word i 1 q : ℤ) ≤ lim.word := by
      apply hb; unfold LightRadixDigit.word word
      omega
    have hmulWord : (mul (i / q) (i % q) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (hmul _ hx _ hy).le).trans hqWord
    have haddrWord : ((table + i : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show table + i ≤ lim.space by omega)).trans hw
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
            ((LightSmallDivide.meets (d := depth + 1) (a := i) (b := q) hdivide ν hdivWord) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen (LightSmallDivide.meets (d := depth + 1) (a := i) (b := q) hdivide ν hdivWord) ?_
            ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSmallDivide.time, LightRadixDigit.time, pow_two, Nat.mul_assoc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSmallDivide.time, LightRadixDigit.time, pow_two, Nat.mul_assoc] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time, LightRadixDigit.time,
              pow_two, Nat.mul_assoc] <;> omega)
      on_goal -1 => (rintro X ν₁ ⟨hX, hν₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν₁; subst X
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
            ((LightRadixDigit.meets (d := depth + 1) (k := i) (b := 1) (p := q) hdigit hdivide ν (by omega) hdigitWord)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightRadixDigit.meets (d := depth + 1) (k := i) (b := 1) (p := q) hdigit hdivide ν (by omega) hdigitWord)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSmallDivide.time, LightRadixDigit.time, pow_two, Nat.mul_assoc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSmallDivide.time, LightRadixDigit.time, pow_two, Nat.mul_assoc] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time, LightRadixDigit.time,
              pow_two, Nat.mul_assoc] <;> omega)
      on_goal -1 => (rintro Y ν₂ ⟨hY, hν₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν₂
    have hY' : Y = ((i % q : ℕ) : ℤ) := by simpa using hY
    subst Y
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
      | refine _root_.Light.Ends.callToThen ((hcell _ hx _ hy ν kept) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (hcell _ hx _ hy ν kept) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSmallDivide.time, LightRadixDigit.time, pow_two, Nat.mul_assoc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSmallDivide.time, LightRadixDigit.time, pow_two, Nat.mul_assoc] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time, LightRadixDigit.time,
              pow_two, Nat.mul_assoc] <;> omega)
      on_goal -1 => (rintro Z ξ ⟨hZ, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst Z
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        (repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_))
      refine _root_.Light.Ends.storeToThen (table + i) (mul (i / q) (i % q)) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSmallDivide.time, LightRadixDigit.time, pow_two, Nat.mul_assoc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSmallDivide.time, LightRadixDigit.time, pow_two, Nat.mul_assoc] <;> first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time, LightRadixDigit.time,
              pow_two, Nat.mul_assoc] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, (i / q : ℕ), (i % q : ℕ), (mul (i / q) (i % q) : ℕ),
        Function.update ξ (table + i) (mul (i / q) (i % q)), by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega), hkeep _ (by omega), written j hj]
      · simp
    · intro c hc
      rw [Function.update_of_ne (by omega), hkeep c (by omega), kept c hc]
  case done =>
    rintro _ _ ⟨X, Y, Z, ν, rfl, written, kept⟩
    refine ⟨?_, kept⟩
    intro x hx y hy
    have hj : x * q + y < q * q := by nlinarith
    have hx' : (x * q + y) / q = x := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hy, Nat.zero_add]
    have hy' : (x * q + y) % q = y := by rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hy]
    simpa [hx', hy', Nat.add_assoc] using written (x * q + y) hj
  case bound =>
    rintro i _ _ _ ⟨X, Y, Z, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightExtensionMultiplyTable
