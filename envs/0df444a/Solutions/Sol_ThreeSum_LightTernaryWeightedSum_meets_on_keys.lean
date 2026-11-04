-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedSum.meets_on_keys
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:13.56772+00:00
-- url     : https://prove2.me/submissions/90cbacd2-5fc4-4672-ad14-9723f3af4c1b

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_succ
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_abs_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_setLast
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedSum
open Light Finset
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryWeightedSum
theorem _root_.solution {p ws ks table n pcount U : ℕ} (hmain : P[p]? = some body) (μ : ℕ → ℤ) (weights keys : ℕ → ℕ)
    (f : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hws : ws + n ≤ lim.space) (hks : ks + n ≤ lim.space)
    (htable : table + pcount ≤ lim.space) (hweights : ∀ i < n, μ (ws + i) = (weights i : ℤ))
    (hkeys : ∀ i < n, μ (ks + i) = (keys i : ℤ)) (hrange : ∀ i < n, keys i < pcount)
    (hread : ∀ i < n, μ (table + keys i) = f (keys i)) (hweight : ∀ i < n, weights i ≤ 2)
    (hvalue : ∀ i < n, |f (keys i)| ≤ U) (hword : 2 * (n + 1) * (U : ℤ) + 3 ≤ lim.word) :
    Meets lim P p d [ws, ks, table, n, pcount] μ (time n) (fun r μ' => r = sum weights keys f n ∧ μ' = μ) :=
  by
  have hf : ∀ i < n, |f (keys i)| ≤ U := hvalue
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
    refine _root_.Light.Ends.setToThen 0 ?_ ?_ ?_
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
    Ends.pieceThen
      (Ends.for (T := 40 * n + 6) (Q := fun σ => σ = ⟨frame [ws, ks, table, n, pcount, sum weights keys f n, n], μ⟩)
        (fun j σ => σ = ⟨frame [ws, ks, table, n, pcount, sum weights keys f j, j], μ⟩) n 30 ?start ?round ?done ?bound
        (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega))))
      ?after
  case start => simp [sum_zero, update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have hwr := hweights j hj
    have hkr := hkeys j hj
    have hkRange := hrange j hj
    have hr := hread j hj
    have hwrange := hweight j hj
    have hfrange := abs_le.mp (hf j hj)
    have hprod : |(weights j : ℤ) * f (keys j)| ≤ 2 * (U : ℤ) :=
      by
      rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
      exact mul_le_mul (by exact_mod_cast hwrange) (hf j hj) (abs_nonneg _) (by norm_num)
    have hprodb := abs_le.mp hprod
    have hprodWord : 2 * (U : ℤ) ≤ lim.word := by nlinarith [Int.natCast_nonneg n, Int.natCast_nonneg U]
    have hsum := abs_le.mp (sum_abs_le weights keys f hweight hf (j := j + 1) (by omega))
    have hsum0 := abs_le.mp (sum_abs_le weights keys f hweight hf (j := j) (by omega))
    have hsumcast := sum_succ weights keys f j
    have hmul : 2 * (j + 1) * (U : ℤ) ≤ 2 * (n + 1) * (U : ℤ) := by gcongr
    have hmulcast : 2 * ((j + 1 : ℕ) : ℤ) * (U : ℤ) ≤ 2 * (n + 1) * (U : ℤ) :=
      by
      push_cast
      exact hmul
    have hsw : |sum weights keys f (j + 1)| ≤ lim.word :=
      (sum_abs_le weights keys f hweight hf (j := j + 1) (by omega)).trans (hmulcast.trans (by omega))
    have hswbounds := abs_le.mp hsw
    have hmul0 : 2 * (j : ℤ) * (U : ℤ) ≤ 2 * (n + 1) * (U : ℤ) := by gcongr; omega
    have hsw0 : |sum weights keys f j| ≤ lim.word :=
      (sum_abs_le weights keys f hweight hf (j := j) (by omega)).trans (hmul0.trans (by omega))
    have hsw0bounds := abs_le.mp hsw0
    unfold loopBody
    refine
      Ends.setLast ?_ (hs := by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hwr, hkr, hr, ← hsumcast] <;> omega)) (hT :=
        by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [] <;>
              first
              | omega
              | (ring_nf; omega)))
    simp [hwr, hkr, hr, ← hsumcast, update_frame_setLocal]
  case done => intro σ hcounter hshape; exact hshape
  case bound =>
    rintro j _ hj _ rfl
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  case after =>
    intro σ hshape
    rw [hshape]
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (sum weights keys f n) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
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
    exact ⟨rfl, rfl⟩
end ThreeSum.LightTernaryWeightedSum
