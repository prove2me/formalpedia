-- Prove2me | solution 1 for ThreeSum.LightWeightGather.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:10.586977+00:00
-- url     : https://prove2.me/submissions/a26772fb-ddbf-4ea2-95bf-cd796342a971

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightWeightGather
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_copy_meets
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
open ThreeSum ThreeSum.LightWeightGather
open Light
set_option maxHeartbeats 1000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightGather
namespace Procs
theorem _root_.solution {pMain : ℕ} (S : Procs P pMain) {μ : ℕ → ℤ} {indices src dst N rows width : ℕ} (select : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hindices : indices + rows ≤ dst)
    (hsrc : src + N * width ≤ dst) (hspace : dst + rows * width ≤ lim.space)
    (hword : (word N rows width : ℤ) ≤ lim.word) (hselect : ∀ i < rows, select i < N)
    (hread : ∀ i < rows, μ (indices + i) = (select i : ℤ)) :
    Meets lim P pMain d [indices, src, dst, rows, width] μ (time rows width)
      (fun _ μ' =>
        (∀ i < rows, ∀ a < width, μ' (dst + i * width + a) = μ (src + select i * width + a)) ∧
          SameOutside μ μ' dst (rows * width)) :=
  by
  have hbudget (x : ℕ) (hx : x ≤ word N rows width) : (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hNWord := hbudget N (by unfold word; omega)
  have hrowsWord := hbudget rows (by unfold word; omega)
  have hwidthWord := hbudget width (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  apply Meets.of_body S.main
  unfold body time
  refine Ends.for (Inv μ indices src dst rows width select) rows (copyTime width + 92) ?_ ?_ ?_ ?_
  · refine ⟨0, 0, μ, ?_, ?_, SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc, μ⟩ : State)) ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 2).symm)
    · intro j hj; omega
  · rintro i _ hi _ ⟨x, r, μ', rfl, written, kept⟩
    have hs := hselect i hi
    have hsi := Nat.mul_le_mul_right width (show select i + 1 ≤ N by omega)
    have hdi := Nat.mul_le_mul_right width (show i + 1 ≤ rows by omega)
    simp only [Nat.add_mul, one_mul] at hsi hdi
    have hsource : src + select i * width + width ≤ dst := by omega
    have hdest : dst + i * width + width ≤ lim.space := by omega
    have hselWord : (select i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (Nat.le_of_lt hs)).trans hNWord
    have hmulSrc : (select i : ℤ) * width ≤ lim.word :=
      by
      have h : select i * width ≤ lim.space := by omega
      exact (by exact_mod_cast h : (select i : ℤ) * width ≤ (lim.space : ℤ)).trans hw
    have hmulDst : (i : ℤ) * width ≤ lim.word :=
      by
      have h : i * width ≤ lim.space := by omega
      exact (by exact_mod_cast h : (i : ℤ) * width ≤ (lim.space : ℤ)).trans hw
    have hr : μ' (indices + i) = (select i : ℤ) :=
      by
      rw [kept _ (Or.inl (by omega))]
      exact hread i hi
    have hsourceAddr : ((src : ℤ) + (select i : ℤ) * width).toNat = src + select i * width := by norm_cast
    have hdestAddr : ((dst : ℤ) + (i : ℤ) * width).toNat = dst + i * width := by norm_cast
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (select i : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hr] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    have hcall :=
      copy_meets (d := d + 1) (μ := μ') (src := src + select i * width) (dst := dst + i * width) (n := width) S.copy hw
        (by omega) hdest (Or.inl (by omega))
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
      | refine _root_.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
      | refine _root_.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsourceAddr,
              hdestAddr]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [hsourceAddr, hdestAddr] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 => omega
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsourceAddr, hdestAddr] <;> omega)
      on_goal -1 => (rintro value μ₁ ⟨hcopied, hkept⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
    refine ⟨by simp, select i, value, μ₁, by simp [update_frame_setLocal], ?_, ?_⟩
    · intro j hj a ha
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hjm := Nat.mul_le_mul_right width (show j + 1 ≤ i by omega)
        simp only [Nat.add_mul, one_mul] at hjm
        rw [hkept _ (Or.inl (by omega))]
        exact written j hj a ha
      · rw [hcopied a ha, kept _ (Or.inl (by omega))]
    · intro a ha
      rw [hkept a (by unfold Outside at *; omega)]
      exact kept a ha
  · rintro _ _ ⟨x, r, μ', rfl, written, kept⟩
    exact ⟨written, kept⟩
  · rintro i _ _ _ ⟨x, r, μ', rfl, _, _⟩
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
end Procs
end ThreeSum.LightWeightGather
