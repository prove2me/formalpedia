-- Prove2me | solution 1 for ThreeSum.LightResidues.residues_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:31.597991+00:00
-- url     : https://prove2.me/submissions/44ec1669-6932-445d-8f44-6d165eeab566

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightResidues
import Theorems.Thm_ThreeSum_LightResidues_residue_cast
import Theorems.Thm_ThreeSum_LightResidues_residue_lt
import Theorems.Thm_ThreeSum_LightResidues_emodTime_le
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
import Definitions.Def_WeightedCache3SUM_Alias_6850731862e76136
import Theorems.Thm_Light_frame_append_zeros
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
open ThreeSum ThreeSum.LightResidues
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightResidues
theorem _root_.solution {pEmod : ℕ} (hem : P[pEmod]? = some emodBody) {μ : ℕ → ℤ} {src dst n p work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hp : 0 < p) (hsrc : src + n ≤ work) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space) (hsep : Apart src n dst n) (hc : |c| ≤ 1)
    (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word) (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Ends lim P d (residuesBody pEmod) ⟨frame [src, dst, n, p, work, c], μ⟩ (residuesTime n U) fun σ' =>
      (∀ i < n, σ'.mem (dst + i) = (residue p c (μ (src + i)) : ℤ)) ∧ KeptBut μ σ'.mem work dst n :=
  by
  have hpre : Emod.Pre lim p U work := ⟨hp, hw, hword, hspace⟩
  have hprod : ∀ i < n, |c * μ (src + i)| ≤ (U : ℤ) := by
    intro i hi
    rw [abs_mul]
    exact (mul_le_mul hc (hvalues i hi) (abs_nonneg _) (by omega)).trans (by simp)
  unfold residuesBody residuesTime
  refine Ends.for (Inv μ src dst n p work c) n (residueBudget U + 22) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, μ, ?_, ?_, fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro j hj
      omega
  case round =>
    rintro i _ hi _ ⟨r, μ', rfl, written, kept⟩
    have hread : μ' (src + i) = μ (src + i) := kept _ ⟨by omega, by omega⟩
    have hproduct := hprod i hi
    have hmul := abs_le.mp hproduct
    have hval := abs_le.mp (hvalues i hi)
    have hsign := abs_le.mp hc
    have htime := emodTime_le (p := p) hproduct
    unfold emodTime residueBudget at htime
    have hlog : Nat.log 2 (1 + U) = Nat.log 2 (U + 1) := by rw [Nat.add_comm]
    have hmodlt := residue_lt hp c (μ (src + i))
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
          _root_.Light.Ends.callToThen ((emod_meets (x := c * μ (src + i)) hem hpre hproduct) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (emod_meets (x := c * μ (src + i)) hem hpre hproduct) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread,
              residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hread, residueBudget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, residueBudget] <;> omega)
      on_goal -1 => (rintro _ μ₁ ⟨hresult, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    rw [← residue_cast hp] at hresult
    subst_vars
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i) (residue p c (μ (src + i)) : ℕ) ?_ ?_ ?_
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
    refine
      ⟨by simp, residue p c (μ (src + i)), Function.update μ₁ (dst + i) (residue p c (μ (src + i)) : ℕ), by
        simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (hkept _ (by omega)).trans (written j hj)
      · simp
    · intro a ⟨ha, hout⟩
      rw [Function.update_of_ne (by omega)]
      exact (hkept a ha).trans (kept a ⟨ha, hout⟩)
  case done =>
    rintro _ _ ⟨r, μ', rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨r, μ', rfl, _, _⟩
    simp
end ThreeSum.LightResidues
