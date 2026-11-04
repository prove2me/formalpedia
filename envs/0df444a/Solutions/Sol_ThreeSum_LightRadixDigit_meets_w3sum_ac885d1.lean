-- Prove2me | solution 1 for ThreeSum.LightRadixDigit.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:28.998983+00:00
-- url     : https://prove2.me/submissions/1afc3f75-e899-4b41-9356-3f7763c13794

import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixDigit
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightRadixDigit
theorem _root_.solution {pMain pDivide k b p : ℕ} (hmain : P[pMain]? = some (body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ) (hd : d < lim.depth)
    (hword : (word k b p : ℤ) ≤ lim.word) :
    Meets lim P pMain d [k, b, p] μ (time k) (fun r μ' => r = (((k / b) % p : ℕ) : ℤ) ∧ μ' = μ) :=
  by
  have hq : k / b ≤ k := Nat.div_le_self k b
  have hq2 : (k / b) / p ≤ k / b := Nat.div_le_self (k / b) p
  have hprod : ((k / b) / p) * p ≤ k / b := Nat.div_mul_le_self (k / b) p
  have hbudget (x : ℕ) (hx : x ≤ word k b p) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hw1 := hbudget (k + b + 2) (by unfold word; omega)
  have hw2 := hbudget (k / b + p + 2) (by unfold word; omega)
  have hkWord := hbudget k (by unfold word; omega)
  have hbWord := hbudget b (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hqWord := hbudget (k / b) (by unfold word; omega)
  have hq2Word := hbudget ((k / b) / p) (by unfold word; omega)
  have hprodWord : (((k / b) / p : ℕ) : ℤ) * (p : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast hprod : (((k / b) / p : ℕ) : ℤ) * (p : ℤ) ≤ (k / b : ℕ)).trans hqWord
  have hprodNonneg : (0 : ℤ) ≤ (((k / b) / p : ℕ) : ℤ) * (p : ℤ) := by positivity
  have hrem : ((k / b : ℕ) : ℤ) - (((k / b) / p : ℕ) : ℤ) * p = (((k / b) % p : ℕ) : ℤ) :=
    by
    have hh := Nat.mod_add_div (k / b) p
    have he : (k / b) % p + ((k / b) / p) * p = k / b := by simpa only [Nat.mul_comm] using hh
    exact_mod_cast (by omega : k / b - ((k / b) / p) * p = (k / b) % p)
  have hprodIntWord : (k : ℤ) / (b : ℤ) / (p : ℤ) * (p : ℤ) ≤ lim.word := by
    simpa only [Int.natCast_ediv] using hprodWord
  have hprodIntNonneg : (0 : ℤ) ≤ (k : ℤ) / (b : ℤ) / (p : ℤ) * (p : ℤ) := by
    simpa only [Int.natCast_ediv] using hprodNonneg
  have hremInt : (k : ℤ) / (b : ℤ) - (k : ℤ) / (b : ℤ) / (p : ℤ) * p = (((k / b) % p : ℕ) : ℤ) := by
    simpa only [Int.natCast_ediv] using hrem
  have hqNonneg : (0 : ℤ) ≤ (k : ℤ) / (b : ℤ) := by
    rw [← Int.natCast_ediv]
    exact Int.natCast_nonneg _
  have hq2Nonneg : (0 : ℤ) ≤ (k : ℤ) / (b : ℤ) / (p : ℤ) :=
    by
    rw [← Int.natCast_ediv, ← Int.natCast_ediv]
    exact Int.natCast_nonneg _
  have hmodWord :=
    hbudget ((k / b) % p)
      (by
        have hm := Nat.mod_le (k / b) p
        unfold word
        omega)
  have hmodIntNonneg : (0 : ℤ) ≤ (k : ℤ) / (b : ℤ) % (p : ℤ) := by exact_mod_cast Nat.zero_le ((k / b) % p)
  have hmodIntWord : (k : ℤ) / (b : ℤ) % (p : ℤ) ≤ lim.word := by
    simpa only [Int.natCast_ediv, Int.natCast_emod] using hmodWord
  have htime1 : LightSmallDivide.time k b ≤ 20 * (k + 1) + 20 :=
    by
    unfold LightSmallDivide.time
    omega
  have htime2 : LightSmallDivide.time (k / b) p ≤ 20 * (k + 1) + 20 :=
    by
    unfold LightSmallDivide.time
    omega
  apply Meets.of_body hmain
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
        _root_.Light.Ends.callToThen
          ((LightSmallDivide.meets (d := d + 1) (a := k) (b := b) hdivide μ hw1) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (LightSmallDivide.meets (d := d + 1) (a := k) (b := b) hdivide μ hw1) ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time] <;> omega)
    on_goal -1 => (rintro q μ₁ ⟨hqval, hmem₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₁
  subst q
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
          ((LightSmallDivide.meets (d := d + 1) (a := k / b) (b := p) hdivide μ hw2) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (LightSmallDivide.meets (d := d + 1) (a := k / b) (b := p) hdivide μ hw2) ?_ ?_ ?_
          ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSmallDivide.time] <;> omega)
    on_goal -1 => (rintro q2 μ₂ ⟨hq2val, hmem₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst μ₂
  subst q2
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen ((k / b) % p : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrem, hremInt, LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hrem, hremInt, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrem, hremInt, LightSmallDivide.time] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, rfl⟩
end ThreeSum.LightRadixDigit
