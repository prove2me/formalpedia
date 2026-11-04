-- Prove2me | solution 1 for ThreeSum.LightPrimality.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:44.233298+00:00
-- url     : https://prove2.me/submissions/a2735566-1639-47d3-a3ab-b8dd847c2196

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
import Theorems.Thm_ThreeSum_LightPrimality_flag_le_one
import Theorems.Thm_ThreeSum_LightPrimality_flag_eq_answer
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_pieceThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_of_body
import Definitions.Def_WeightedCache3SUM_Alias_6850731862e76136
import Theorems.Thm_Light_frame_append_zeros
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightResidues_emodTime_le
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimality
theorem _root_.solution {pMain pEmod : ℕ} (hmain : P[pMain]? = some (body pEmod)) (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {n free maxValue : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 2 ≤ n)
    (hmax : n ≤ maxValue) (hspace : free + (Nat.log 2 (maxValue + 1) + 2) ≤ lim.space)
    (hword : (8 * maxValue + 16 : ℕ) ≤ lim.word) :
    Meets lim P pMain d [n, free] μ (time n maxValue) (fun r μ' => r = (answer n : ℤ) ∧ Kept μ μ' free) :=
  by
  have hwordZ : (8 * (maxValue : ℤ) + 16) ≤ lim.word := by exact_mod_cast hword
  have hnWord : (n : ℤ) ≤ lim.word := by omega
  have hrounds : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hx : |(n : ℤ)| ≤ (maxValue : ℤ) := by simpa using Int.ofNat_le.mpr hmax
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
    refine _root_.Light.Ends.setToThen 1 ?_ ?_ ?_
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
      (Ends.for (T := (n - 2) * (residueBudget maxValue + 70) + 20) (Q := Inv μ n free (n - 2)) (Inv μ n free) (n - 2)
        (residueBudget maxValue + 50) ?_ ?_ ?_ ?_ (hT := by
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
  · refine ⟨0, μ, ?_, fun _ _ => rfl⟩
    simp only [flag, update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc, μ⟩ : State)) (frame_append_zeros _ 1).symm
  · rintro i _ hi _ ⟨rval, ν, rfl, hkept⟩
    have hm : i + 2 ≤ maxValue := by omega
    have hmWord : ((i + 2 : ℕ) : ℤ) ≤ lim.word := by omega
    have hf := flag_le_one n i
    have hpre : Emod.Pre lim (i + 2) maxValue free := ⟨by omega, hw, by push_cast; omega, hspace⟩
    have ht := emodTime_le (p := i + 2) hx
    simp only [Int.natAbs_natCast] at ht
    unfold emodTime residueBudget at ht
    have hlog : Nat.log 2 (1 + maxValue) = Nat.log 2 (maxValue + 1) := by rw [Nat.add_comm]
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
          _root_.Light.Ends.callToThen ((emod_meets (d := d + 1) (x := (n : ℤ)) hem hpre hx) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (emod_meets (d := d + 1) (x := (n : ℤ)) hem hpre hx) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [residueBudget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, residueBudget] <;> omega)
      on_goal -1 => (rintro result ν₁ ⟨hresult, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst result
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j hj).trans (hkept j hj)
    refine
      Ends.iteLast (fun hdiv => ?_) (fun hnot => ?_)
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
        (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [residueBudget] <;>
              first
              | omega
              | (ring_nf; omega)))
    · have hdiv' : i + 2 ∣ n :=
        by
        have hh : (n : ℤ) % ((i + 2 : ℕ) : ℤ) = 0 := by simpa using hdiv
        exact Int.natCast_dvd_natCast.mp (Int.dvd_of_emod_eq_zero hh)
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
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, residueBudget]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [residueBudget] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, residueBudget] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      refine ⟨by simp, (n : ℤ) % ((i + 2 : ℕ) : ℤ), ν₁, ?_, hkept₁⟩
      simp [flag, hdiv', update_frame_setLocal]
    · have hnot' : ¬i + 2 ∣ n := by
        intro hh
        apply hnot
        have he := Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mpr hh)
        simpa using he
      apply Ends.skip
      refine ⟨by simp, (n : ℤ) % ((i + 2 : ℕ) : ℤ), ν₁, ?_, hkept₁⟩
      simp [flag, hnot', update_frame_setLocal]
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨rval, ν, rfl, hkept⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
  · rintro σ ⟨rval, ν, rfl, hkept⟩
    have hf := flag_le_one n (n - 2)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (flag n (n - 2)) ?_ ?_ ?_
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
    exact ⟨by simp [flag_eq_answer hn], hkept⟩
end ThreeSum.LightPrimality
