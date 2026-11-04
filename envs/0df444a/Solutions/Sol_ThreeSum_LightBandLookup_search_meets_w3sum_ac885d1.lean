-- Prove2me | solution 1 for ThreeSum.LightBandLookup.search_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:20.745197+00:00
-- url     : https://prove2.me/submissions/74f309f0-aca2-4fba-987a-cf86a23fc0a7

import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandLookup
open Light ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandLookup
theorem _root_.solution {pSearch a n powers W : ℕ} {x : ℤ} (hprog : P[pSearch]? = some (searchBody pSearch)) (μ : ℕ → ℤ)
    (f : ℕ → ℤ) (K : ℕ) (hw : (lim.space : ℤ) ≤ lim.word) (ha : a + n ≤ lim.space)
    (hspace : powers + (W + 1) ≤ lim.space) (hword : ((n + 2 ^ (W + 1) + 16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a + i) = f i) (hpowers : Powers μ powers W) (hpart : BinarySearch.Partition f x n K) :
    ∀ L k : ℕ,
      L ≤ W →
        k ≤ K →
          K < k + 2 ^ L →
            ∀ d,
              d + L ≤ lim.depth →
                Meets lim P pSearch d [a, n, x, powers, L, k] μ (searchTime L) (fun r μ' => r = (K : ℤ) ∧ μ' = μ) :=
  by
  obtain ⟨hKn, hpre, hpost⟩ := hpart
  have hnWord : (n : ℤ) ≤ lim.word := by exact (Int.ofNat_le.mpr (by omega : n ≤ lim.space)).trans hw
  intro L
  induction L with
  | zero =>
    intro k hL hk hgap d hd
    have heq : k = K := by simp only [Nat.pow_zero] at hgap; omega
    apply Meets.of_body hprog
    unfold searchBody searchTime
    refine Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (k : ℕ) ?_ ?_ ?_
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
    exact ⟨by simp [heq], rfl⟩
  | succ L ih =>
    intro k hL hk hgap d hd
    have hLW : L ≤ W := by omega
    have hpower := hpowers L hLW
    have hpPos : 0 < (2 : ℕ) ^ L := Nat.two_pow_pos _
    have hpLe : 2 ^ L ≤ 2 ^ (W + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hmidWord : ((k + 2 ^ L : ℕ) : ℤ) ≤ lim.word := by
      exact (Int.ofNat_le.mpr (by omega : k + 2 ^ L ≤ n + 2 ^ (W + 1) + 16)).trans hword
    have hmidCast : (k : ℤ) + μ (powers + L) = ((k + 2 ^ L : ℕ) : ℤ) :=
      by
      rw [hpower]
      push_cast
      rfl
    have hpowerNonneg : (0 : ℤ) ≤ μ (powers + L) := by
      rw [hpower]
      exact Int.natCast_nonneg _
    have hpowerWord : μ (powers + L) ≤ lim.word := by
      rw [hpower]
      exact (Int.ofNat_le.mpr (by omega : 2 ^ L ≤ n + 2 ^ (W + 1) + 16)).trans hword
    have hmidNonneg : (0 : ℤ) ≤ (k : ℤ) + μ (powers + L) := by omega
    have hmidBound : (k : ℤ) + μ (powers + L) ≤ lim.word :=
      by
      rw [hmidCast]
      exact hmidWord
    have hpowerIntNonneg : (0 : ℤ) ≤ (2 : ℤ) ^ L := by positivity
    have hmidIntBound : (k : ℤ) + (2 : ℤ) ^ L ≤ lim.word := by exact_mod_cast hmidWord
    have hdouble : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by ring
    rw [hdouble] at hgap
    apply Meets.of_body hprog
    unfold searchBody searchTime
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (L : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
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
      refine _root_.Light.Ends.setToThen (k + 2 ^ L : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmidCast,
              searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hmidCast, searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmidCast, searchTime] <;> omega)
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
      refine _root_.Light.Ends.iteIffThen (((k + 2 ^ L : ℕ) : ℤ) ≤ (n : ℤ)) (fun hmnZ => ?_) (fun hmnZ => ?_) ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [searchTime] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
      all_goals
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_
    · have hmn : k + 2 ^ L ≤ n := by exact_mod_cast hmnZ
      have hmRead := hread (k + 2 ^ L - 1) (by omega)
      have hmAddr : (a : ℤ) + ((k + 2 ^ L : ℕ) : ℤ) - 1 = ((a + (k + 2 ^ L - 1) : ℕ) : ℤ) := by omega
      have hmNat : ((a : ℤ) + ((k + 2 ^ L : ℕ) : ℤ) - 1).toNat = a + (k + 2 ^ L - 1) := by
        rw [hmAddr, Int.toNat_natCast]
      have hmNat' : ((a : ℤ) + ((k : ℤ) + (2 : ℤ) ^ L) - 1).toNat = a + (k + 2 ^ L - 1) := by
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hmNat
      have hmIntBound : (a : ℤ) + ((k : ℤ) + (2 : ℤ) ^ L) ≤ lim.word :=
        by
        have hn : a + (k + 2 ^ L) ≤ lim.space := by omega
        exact (by exact_mod_cast hn : (a : ℤ) + ((k : ℤ) + (2 : ℤ) ^ L) ≤ (lim.space : ℤ)).trans hw
      have hmIntLower : 1 ≤ (a : ℤ) + ((k : ℤ) + (2 : ℤ) ^ L) :=
        by
        have hp : 0 < (2 : ℤ) ^ L := by positivity
        omega
      have hmIntSpace : (a : ℤ) + ((k : ℤ) + (2 : ℤ) ^ L) ≤ (lim.space : ℤ) := by
        exact_mod_cast (show a + (k + 2 ^ L) ≤ lim.space by omega)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.iteIffThen (x < f (k + 2 ^ L - 1)) (fun htest => ?_) (fun htest => ?_) ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmNat', hmRead,
                searchTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [hmNat', hmRead, searchTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmNat', hmRead, searchTime] <;> omega)
        all_goals
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_
      · have hkm : K < k + 2 ^ L := by
          by_contra h
          have hh := hpre (k + 2 ^ L - 1) (by omega)
          omega
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
          | refine _root_.Light.Ends.callToThen ((ih k hLW hk hkm (d + 1) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
          | refine _root_.Light.Ends.callToThen (ih k hLW hk hkm (d + 1) (by omega)) ?_ ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [searchTime] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
          on_goal -1 => (rintro r μ' ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        exact ⟨hr, hmem⟩
      · have hmk : k + 2 ^ L ≤ K := by
          by_contra h
          exact htest (hpost (k + 2 ^ L - 1) (by omega) (by omega))
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
              _root_.Light.Ends.callToThen ((ih (k + 2 ^ L) hLW hmk (by omega) (d + 1) (by omega)) _ (by omega)) ?_ ?_
                ?_ ?_
          | refine _root_.Light.Ends.callToThen (ih (k + 2 ^ L) hLW hmk (by omega) (d + 1) (by omega)) ?_ ?_ ?_ ?_
          on_goal -1 =>
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [searchTime] <;>
                  first
                  | omega
                  | (ring_nf; omega))
          on_goal -1 => omega
          on_goal -1 =>
            ( (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
          on_goal -1 => (rintro r μ' ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
        exact ⟨hr, hmem⟩
    · have hkm : K < k + 2 ^ L := by omega
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
        | refine _root_.Light.Ends.callToThen ((ih k hLW hk hkm (d + 1) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
        | refine _root_.Light.Ends.callToThen (ih k hLW hk hkm (d + 1) (by omega)) ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, searchTime]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [searchTime] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, searchTime] <;> omega)
        on_goal -1 => (rintro r μ' ⟨hr, hmem⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      exact ⟨hr, hmem⟩
end ThreeSum.LightBandLookup
