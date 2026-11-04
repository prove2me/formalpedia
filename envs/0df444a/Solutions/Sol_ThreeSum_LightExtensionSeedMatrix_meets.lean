-- Prove2me | solution 1 for ThreeSum.LightExtensionSeedMatrix.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:30:25.335011+00:00
-- url     : https://prove2.me/submissions/a65cd4c9-7298-48ad-894a-b58c63cc3f68

import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
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
import Theorems.Thm_ThreeSum_LightExtensionSeedRow_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionSeedMatrix
open Light
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionSeedMatrix
theorem _root_.solution {proc pRow pDigit pDivide table q p dst len : ℕ}
    (hp : P[proc]? = some (body pRow pDigit pDivide)) (hrow : P[pRow]? = some (LightExtensionSeedRow.body pDigit))
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide)) (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (μ : ℕ → ℤ) (mul : ℕ → ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 2 < lim.depth) (hq : 0 < q)
    (hmod : 0 < p) (htable : table + q * q ≤ dst) (hspace : dst + q * q * len ≤ lim.space)
    (hread : ∀ a < q, ∀ b < q, μ (table + a * q + b) = (mul a b : ℤ)) (hmul : ∀ a < q, ∀ b < q, mul a b < q)
    (hword : (word len q p : ℤ) ≤ lim.word) :
    Meets lim P proc depth [table, q, p, dst, len] μ (time len q)
      (fun _ ν =>
        (∀ i < q * q, ∀ j < len, ν (dst + i * len + j) = (value mul q p i j : ℤ)) ∧
          SameOutside μ ν dst (q * q * len)) :=
  by
  have hb (z : ℕ) (hz : z ≤ word len q p) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hqWord := hb q (by unfold word; omega)
  have hpWord := hb p (by unfold word; omega)
  have hQQWord := hb (q * q) (by unfold word; omega)
  have hprod : q * q * len ≤ word len q p := by unfold word; omega
  have h1 : (1 : ℤ) ≤ lim.word := by unfold word at hword; omega
  apply Meets.of_body hp
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
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.for (Inv μ table q p dst len mul) (q * q) (LightExtensionSeedRow.time len q + 60 * (q * q) + 390) ?start ?round
      ?done ?bound
  case start =>
    refine ⟨0, 0, 0, μ, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 3).symm)
    · intro r hr; omega
  case round =>
    rintro i _ hi _ ⟨oldX, oldY, oldZ, ν, rfl, written, kept⟩
    have hquotient : i / q ≤ i := Nat.div_le_self i q
    have hquotientInt : (i : ℤ) / (q : ℤ) ≤ (i : ℤ) := by exact_mod_cast hquotient
    have hx : i / q < q := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    have hy : i % q < q := Nat.mod_lt _ hq
    have hiWord := hb i (by unfold word; omega)
    have hxWord := (Int.ofNat_le.mpr hx.le).trans hqWord
    have hyWord := (Int.ofNat_le.mpr hy.le).trans hqWord
    have hdivWord := hb (i + q + 2) (by unfold word; omega)
    have hdigitWord : (LightRadixDigit.word i 1 q : ℤ) ≤ lim.word := by
      apply hb; unfold LightRadixDigit.word word
      omega
    have hrowWord : (LightExtensionSeedRow.word len q p : ℤ) ≤ lim.word := by
      apply hb
      unfold LightExtensionSeedRow.word word; omega
    have hdivideTime : LightSmallDivide.time i q ≤ 20 * (q * q) + 40 :=
      (LightSmallDivide.time_bound i q).trans (by omega)
    have hdigitTime : LightRadixDigit.time i ≤ 40 * (q * q) + 140 := by unfold LightRadixDigit.time; omega
    have hrowEnd : i * len + len ≤ q * q * len :=
      by
      have hm := Nat.mul_le_mul_right len (show i + 1 ≤ q * q by omega)
      nlinarith
    have hoffWord := hb (i * len) (by omega)
    have haddrWord : ((dst + i * len : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (show dst + i * len ≤ lim.space by omega)).trans hw
    have hreadν (a : ℕ) (ha : a < q) (b : ℕ) (hbb : b < q) : ν (table + a * q + b) = (mul a b : ℤ) :=
      by
      have hoff : a * q + b < q * q := by nlinarith
      rw [kept _ (Or.inl (by omega)), hread a ha b hbb]
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
            ((LightSmallDivide.meets (d := depth + 1) (a := i) (b := q) hdivide ν hdivWord) _ (by omega)) ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen (LightSmallDivide.meets (d := depth + 1) (a := i) (b := q) hdivide ν hdivWord) ?_
            ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSmallDivide.time, LightRadixDigit.time, LightExtensionSeedRow.time, pow_two, Nat.mul_assoc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSmallDivide.time, LightRadixDigit.time, LightExtensionSeedRow.time, pow_two, Nat.mul_assoc] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time, LightRadixDigit.time,
              LightExtensionSeedRow.time, pow_two, Nat.mul_assoc] <;>
            omega)
      on_goal -1 => (rintro X ν₁ ⟨hX, hν₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν₁
    subst X
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
              LightSmallDivide.time, LightRadixDigit.time, LightExtensionSeedRow.time, pow_two, Nat.mul_assoc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSmallDivide.time, LightRadixDigit.time, LightExtensionSeedRow.time, pow_two, Nat.mul_assoc] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time, LightRadixDigit.time,
              LightExtensionSeedRow.time, pow_two, Nat.mul_assoc] <;>
            omega)
      on_goal -1 => (rintro Y ν₂ ⟨hY, hν₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst ν₂
    have hY' : Y = ((i % q : ℕ) : ℤ) := by simpa using hY
    subst Y
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
            ((LightExtensionSeedRow.meets (depth := depth + 1) (table := table) (q := q) (p := p) (x := i / q) (y :=
                i % q) (dst := dst + i * len) (len := len) hrow hdigit hdivide ν mul hw (by omega) hx hy hmod (by omega)
                (by omega) hreadν hmul hrowWord)
              _ (by omega))
            ?_ ?_ ?_ ?_
      |
        refine
          _root_.Light.Ends.callToThen
            (LightExtensionSeedRow.meets (depth := depth + 1) (table := table) (q := q) (p := p) (x := i / q) (y :=
              i % q) (dst := dst + i * len) (len := len) hrow hdigit hdivide ν mul hw (by omega) hx hy hmod (by omega)
              (by omega) hreadν hmul hrowWord)
            ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightSmallDivide.time, LightRadixDigit.time, LightExtensionSeedRow.time, pow_two, Nat.mul_assoc]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightSmallDivide.time, LightRadixDigit.time, LightExtensionSeedRow.time, pow_two, Nat.mul_assoc] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time, LightRadixDigit.time,
              LightExtensionSeedRow.time, pow_two, Nat.mul_assoc] <;>
            omega)
      on_goal -1 => (rintro Z ξ ⟨hZ, hvalues, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, (i / q : ℕ), (i % q : ℕ), Z, ξ, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro r hr j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · have hoff : r * len + j < i * len :=
          by
          have hm := Nat.mul_le_mul_right len (show r + 1 ≤ i by omega)
          nlinarith
        rw [hkeep _ (Or.inl (by omega)), written r hr j hj]
      · simpa [value, Nat.add_assoc] using hvalues j hj
    · intro a ha
      rw [hkeep a (by omega), kept a ha]
  case done => rintro _ _ ⟨X, Y, Z, ν, rfl, written, kept⟩; exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨X, Y, Z, ν, rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end ThreeSum.LightExtensionSeedMatrix
