-- Prove2me | solution 1 for ThreeSum.LightLookupSum.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:24:31.190318+00:00
-- url     : https://prove2.me/submissions/835aca0d-f0b7-4520-b8e9-99303a40a8e1

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Theorems.Thm_ThreeSum_LightLookupSum_prefixSum_zero
import Theorems.Thm_ThreeSum_LightLookupSum_prefixSum_succ
import Theorems.Thm_ThreeSum_LightLookupSum_prefixSum_le
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_setLast
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
set_option autoImplicit false
open ThreeSum ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightLookupSum
theorem _root_.solution {pThis : ℕ} (hThis : P[pThis]? = some body) {μ : ℕ → ℤ} {keys table n p B : ℕ} (key f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hkeys : keys + n ≤ lim.space) (htable : table + p ≤ lim.space)
    (hkey : ∀ i < n, μ (keys + i) = (key i : ℤ)) (hrange : ∀ i < n, key i < p)
    (hread : ∀ r < p, μ (table + r) = (f r : ℤ)) (hvalue : ∀ r < p, f r ≤ B) (hword : (n * B : ℕ) ≤ lim.word) :
    Meets lim P pThis d [keys, table, n, p] μ (time n) fun r μ' => r = (prefixSum f key n : ℤ) ∧ μ' = μ :=
  by
  have hv : ∀ i < n, f (key i) ≤ B := fun i hi => hvalue (key i) (hrange i hi)
  apply Meets.of_body hThis
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
      (Ends.for (T := 24 * n + 6) (Q := fun σ => σ = ⟨frame [(keys : ℤ), table, n, p, prefixSum f key n, n], μ⟩)
        (fun j σ => σ = ⟨frame [(keys : ℤ), table, n, p, prefixSum f key j, j], μ⟩) n 16 ?_ ?_ ?_ ?_ (hT := by
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
      ?_
  · simp [prefixSum_zero, update_frame_setLocal]
  · rintro j _ hj _ rfl
    have hkr := hrange j hj
    have hkeyread := hkey j hj
    have htread := hread (key j) hkr
    have hsum := prefixSum_le f key hv (j := j + 1) (by omega)
    have hsumword : (prefixSum f key (j + 1) : ℤ) ≤ lim.word :=
      by
      have hmul : (j + 1) * B ≤ n * B := Nat.mul_le_mul_right B (by omega)
      exact (by exact_mod_cast hsum.trans hmul : (prefixSum f key (j + 1) : ℤ) ≤ (n * B : ℕ)).trans hword
    have hsumcast : (prefixSum f key j : ℤ) + f (key j) = prefixSum f key (j + 1) := by
      rw [prefixSum_succ, Nat.cast_add]
    unfold loopBody
    refine
      Ends.setLast ?_ (hs := by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkeyread, htread, hsumcast] <;> omega)) (hT :=
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
    simp [hkeyread, htread, hsumcast, update_frame_setLocal]
  · intro σ hcounter hshape
    exact hshape
  · rintro j _ hj _ rfl
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  · intro σ hshape
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
      refine _root_.Light.Ends.setToThen (prefixSum f key n) ?_ ?_ ?_
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
end ThreeSum.LightLookupSum
