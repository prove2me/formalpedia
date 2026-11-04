-- Prove2me | solution 1 for ThreeSum.LightSourceResidues.ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:32.7616+00:00
-- url     : https://prove2.me/submissions/569db72e-8b05-4d73-9393-30e53f82b122

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Theorems.Thm_ThreeSum_LightSourceResidues_key_cast
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_LocalsBut_update
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
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightSourceResidues
theorem _root_.solution {pEmod : ℕ} (hem : P[pEmod]? = some emodBody) {μ : ℕ → ℤ} {src dst n p m work U D : ℕ}
    {shift : ℤ} (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hp : 0 < p) (hm : 0 < m) (hsrc : src + n ≤ work)
    (hdst : dst + n ≤ work) (hspace : space work p U D ≤ lim.space) (hsep : Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D : ℤ) ≤ lim.word) (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Ends lim P d (body pEmod) ⟨frame [src, dst, n, p, m, work, shift], μ⟩ (time n p U D)
      (fun σ => (∀ i < n, σ.mem (dst + i) = (key p m shift (μ (src + i)) : ℤ)) ∧ KeptBut μ σ.mem work dst n) :=
  by
  have hspace0 : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space := (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hspace1 : work + (Nat.log 2 (p + D + 1) + 2) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hword0 : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word :=
    by
    have hb : 4 * U + 4 * p + 16 ≤ word p m U D := by unfold word; omega
    exact (by exact_mod_cast hb : (4 * U + 4 * p + 16 : ℤ) ≤ (word p m U D : ℤ)).trans hword
  have hword1 : (4 * (p + D) + 4 * m + 16 : ℤ) ≤ lim.word :=
    by
    have hb : 4 * (p + D) + 4 * m + 16 ≤ word p m U D := by unfold word; omega
    exact (by exact_mod_cast hb : (4 * (p + D) + 4 * m + 16 : ℤ) ≤ (word p m U D : ℤ)).trans hword
  have hpre0 : Emod.Pre lim p U work := ⟨hp, hw, hword0, hspace0⟩
  have hpre1 : Emod.Pre lim m (p + D) work := ⟨hm, hw, hword1, hspace1⟩
  have hshift' := abs_le.mp hshift
  unfold body time
  refine
    Ends.for (Inv μ src dst n p m work shift) n
      (LightResidues.residueBudget U + LightResidues.residueBudget (p + D) + 92) ?start ?round ?done ?bound
  case start =>
    refine ⟨0, 0, μ, ?_, ?_, fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 2).symm)
    · intro j hj
      omega
  case round =>
    rintro i _ hi _ ⟨r0, r1, ν, rfl, written, kept⟩
    have hread : ν (src + i) = μ (src + i) := kept _ ⟨by omega, by omega⟩
    have hx := hvalues i hi
    have hx' := abs_le.mp hx
    have hmod0 : 0 ≤ μ (src + i) % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
    have hmodp : μ (src + i) % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
    have hsum : |μ (src + i) % (p : ℤ) + shift| ≤ ((p + D : ℕ) : ℤ) :=
      by
      rw [Nat.cast_add]
      exact abs_le.mpr ⟨by omega, by omega⟩
    have hsum' := abs_le.mp hsum
    have htime0 := LightResidues.emodTime_le (p := p) hx
    have htime1 := LightResidues.emodTime_le (p := m) hsum
    unfold emodTime LightResidues.residueBudget at htime0 htime1
    have hlog0 : Nat.log 2 (1 + U) = Nat.log 2 (U + 1) := by rw [Nat.add_comm]
    have hlog1 : Nat.log 2 (1 + (p + D)) = Nat.log 2 (p + D + 1) := by rw [Nat.add_comm]
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
      | refine _root_.Light.Ends.callToThen ((emod_meets (x := μ (src + i)) hem hpre0 hx) _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (emod_meets (x := μ (src + i)) hem hpre0 hx) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread,
              LightResidues.residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hread, LightResidues.residueBudget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, LightResidues.residueBudget] <;> omega)
      on_goal -1 => (rintro q0 ν₁ ⟨hresult0, hkeep0⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    subst q0
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
          _root_.Light.Ends.callToThen ((emod_meets (x := μ (src + i) % (p : ℤ) + shift) hem hpre1 hsum) _ (by omega))
            ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen (emod_meets (x := μ (src + i) % (p : ℤ) + shift) hem hpre1 hsum) ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightResidues.residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightResidues.residueBudget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightResidues.residueBudget] <;> omega)
      on_goal -1 => (rintro q1 ν₂ ⟨hresult1, hkeep1⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    rw [← key_cast hm] at hresult1
    subst q1
    have hlt := key_lt (p := p) hm shift (μ (src + i))
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (dst + i) (key p m shift (μ (src + i)) : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil,
              LightResidues.residueBudget]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [LightResidues.residueBudget] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightResidues.residueBudget] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    refine
      ⟨by simp, μ (src + i) % (p : ℤ), (key p m shift (μ (src + i)) : ℤ),
        Function.update ν₂ (dst + i) (key p m shift (μ (src + i)) : ℕ), by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (hkeep1 _ (by omega)).trans ((hkeep0 _ (by omega)).trans (written j hj))
      · simp
    · intro a ⟨ha, hout⟩
      rw [Function.update_of_ne (by omega)]
      exact (hkeep1 a ha).trans ((hkeep0 a ha).trans (kept a ⟨ha, hout⟩))
  case done =>
    rintro _ _ ⟨r0, r1, ν, rfl, written, kept⟩
    exact ⟨written, kept⟩
  case bound =>
    rintro i _ _ _ ⟨r0, r1, ν, rfl, _, _⟩
    simp
end ThreeSum.LightSourceResidues
