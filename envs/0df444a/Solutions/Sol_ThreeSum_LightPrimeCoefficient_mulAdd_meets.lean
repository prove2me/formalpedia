-- Prove2me | solution 1 for ThreeSum.LightPrimeCoefficient.mulAdd_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:16:20.256592+00:00
-- url     : https://prove2.me/submissions/e6112424-c576-44d3-969b-ddf9679408ed

import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightPrimeCoefficient
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
open ThreeSum ThreeSum.LightPrimeCoefficient
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimeCoefficient
theorem _root_.solution {pMain pDivide acc x y p : ℕ} (hmain : P[pMain]? = some (mulAddBody pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ) (hd : d < lim.depth) (hp : 0 < p) (ha : acc < p)
    (hx : x < p) (hy : y < p) (hword : (word p : ℤ) ≤ lim.word) :
    Meets lim P pMain d [acc, x, y, p] μ (mulAddTime p) (fun r ν => r = (((acc + x * y) % p : ℕ) : ℤ) ∧ ν = μ) :=
  by
  let n := acc + x * y
  have hn : n ≤ (p + 1) ^ 2 := by dsimp [n]; nlinarith
  have hprod : (n / p) * p ≤ n := Nat.div_mul_le_self n p
  have hq : n / p ≤ n := Nat.div_le_self n p
  have hmod : n % p ≤ n := Nat.mod_le n p
  have hb (z : ℕ) (hz : z ≤ word p) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hacc := hb acc (by unfold word; nlinarith)
  have hxx := hb x (by unfold word; nlinarith)
  have hyy := hb y (by unfold word; nlinarith)
  have hpp := hb p (by unfold word; nlinarith)
  have hxy := hb (x * y) (by unfold word; nlinarith)
  have hnn := hb n (by unfold word; nlinarith)
  have hqq := hb (n / p) (by unfold word; nlinarith)
  have hpprod := hb ((n / p) * p) (by unfold word; nlinarith)
  have hmodWord := hb (n % p) (by unfold word; nlinarith)
  have hdivideWord := hb (n + p + 2) (by unfold word; nlinarith)
  have hnInt : (acc : ℤ) + (x : ℤ) * (y : ℤ) = (n : ℤ) := by simp [n]
  have hprodInt : (((n / p : ℕ) : ℤ) * (p : ℤ)) = (((n / p) * p : ℕ) : ℤ) := by push_cast; rfl
  have hrem : (n : ℤ) - ((n / p : ℕ) : ℤ) * (p : ℤ) = ((n % p : ℕ) : ℤ) :=
    by
    have hh : n % p + (n / p) * p = n := by simpa only [Nat.mul_comm] using Nat.mod_add_div n p
    have hz : ((n % p : ℕ) : ℤ) + ((n / p : ℕ) : ℤ) * (p : ℤ) = (n : ℤ) := by exact_mod_cast hh
    omega
  have htimeBound : (acc + x * y) / p ≤ p ^ 2 + 2 * p + 1 := by have hh := hq.trans hn; dsimp [n] at hh; nlinarith
  have hprodIntWord : (n : ℤ) / (p : ℤ) * (p : ℤ) ≤ lim.word := by
    simpa only [Int.natCast_mul, Int.natCast_ediv] using hpprod
  have hprodIntNonneg : 0 ≤ (n : ℤ) / (p : ℤ) * (p : ℤ) := by positivity
  apply Meets.of_body hmain
  unfold mulAddBody mulAddTime
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
          ((LightSmallDivide.meets (d := d + 1) (a := n) (b := p) hdivide μ hdivideWord) _ (by omega)) ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen (LightSmallDivide.meets (d := d + 1) (a := n) (b := p) hdivide μ hdivideWord) ?_ ?_
          ?_ ?_
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
    on_goal -1 => (rintro q ν ⟨hqval, hν⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  subst ν
  subst q
  have hremExpanded : (acc : ℤ) + (x : ℤ) * (y : ℤ) - ((n / p : ℕ) : ℤ) * (p : ℤ) = ((n % p : ℕ) : ℤ) := by
    simpa only [hnInt] using hrem
  simp only [Int.natCast_ediv] at hremExpanded
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (n % p : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hprodInt, hremExpanded,
            LightSmallDivide.time]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [hprodInt, hremExpanded, LightSmallDivide.time] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hprodInt, hremExpanded,
            LightSmallDivide.time] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  exact ⟨rfl, rfl⟩
end ThreeSum.LightPrimeCoefficient
