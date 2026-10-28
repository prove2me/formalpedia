-- Prove2me | solution 1 for StructEstMDP.FiniteTime.display_35
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:57:38.201856+00:00
-- url     : https://prove2.me/submissions/a5fe2bf8-338d-4f9a-832f-4b2afb850a43

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_StructEstMDP_FiniteTime_Setting

open FoundationsML.ReinforcementLearning MeasureTheory

namespace Aux_StructEst_d35
open StructEstMDP.FiniteTime

theorem entry_le {S A : Type*} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (f : S → A → ℝ) (s : S) (a : A) : |f s a| ≤ supNorm f := by
  have hmem : (s, a) ∈ (Finset.univ : Finset (S × A)) := Finset.mem_univ _
  exact Finset.le_sup' (s := Finset.univ) (fun x : S × A => |f x.1 x.2|) hmem

theorem lse_le {S A : Type*} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (Q1 Q2 : S → A → ℝ) (s : S) :
    Real.log (∑ b, Real.exp (Q1 s b)) ≤ supNorm (Q1 - Q2) + Real.log (∑ b, Real.exp (Q2 s b)) := by
  have hpos2 : 0 < ∑ b, Real.exp (Q2 s b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hpos1 : 0 < ∑ b, Real.exp (Q1 s b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  have hsum : ∑ b, Real.exp (Q1 s b) ≤ Real.exp (supNorm (Q1 - Q2)) * ∑ b, Real.exp (Q2 s b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := entry_le (Q1 - Q2) s b
    simp only [Pi.sub_apply] at this
    have := le_abs_self (Q1 s b - Q2 s b)
    linarith
  calc Real.log (∑ b, Real.exp (Q1 s b))
      ≤ Real.log (Real.exp (supNorm (Q1 - Q2)) * ∑ b, Real.exp (Q2 s b)) :=
        Real.log_le_log hpos1 hsum
    _ = supNorm (Q1 - Q2) + Real.log (∑ b, Real.exp (Q2 s b)) := by
        rw [Real.log_mul (Real.exp_pos _).ne' hpos2.ne', Real.log_exp]

theorem supNorm_comm {S A : Type*} [Fintype S] [Nonempty S] [Fintype A] [Nonempty A]
    (Q1 Q2 : S → A → ℝ) : supNorm (Q1 - Q2) = supNorm (Q2 - Q1) := by
  unfold supNorm
  congr 1
  funext x
  simp only [Pi.sub_apply]
  exact abs_sub_comm _ _

theorem log_softmax {S A : Type*} [Fintype A] [Nonempty A] (Q : S → A → ℝ) (s : S) (a : A) :
    Real.log (softmax Q s a) = Q s a - Real.log (∑ b, Real.exp (Q s b)) := by
  unfold softmax
  have hpos : 0 < ∑ b, Real.exp (Q s b) :=
    Finset.sum_pos (fun b _ => Real.exp_pos _) Finset.univ_nonempty
  rw [Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp]

end Aux_StructEst_d35

open StructEstMDP.FiniteTime Aux_StructEst_d35 in
theorem solution {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (γ : ℝ) {p : ℕ} (r : S → A → EuclideanSpace ℝ (Fin p) → ℝ)
    (θ : EuclideanSpace ℝ (Fin p)) (Qhat Q : S → A → ℝ) (ε : ℝ)
    (hQ : supNorm (Qhat - Q) ≤ ε) :
    supNorm (fun s a => Real.log (softmax Qhat s a) - Real.log (optPolicy P γ r θ s a)) ≤
        2 * supNorm (Qhat - optQ P γ r θ) ∧
      2 * supNorm (Qhat - optQ P γ r θ) ≤ 2 * ε + 2 * supNorm (Q - optQ P γ r θ) := by
  set Q2 := optQ P γ r θ with hQ2
  constructor
  · unfold supNorm
    apply Finset.sup'_le
    intro x _
    show |Real.log (softmax Qhat x.1 x.2) - Real.log (softmax Q2 x.1 x.2)| ≤ _
    rw [log_softmax, log_softmax]
    have h1 := entry_le (Qhat - Q2) x.1 x.2
    simp only [Pi.sub_apply] at h1
    have h2 := lse_le Qhat Q2 x.1
    have h3 := lse_le Q2 Qhat x.1
    rw [← supNorm_comm] at h3
    have hd : supNorm (Qhat - Q2) =
        Finset.univ.sup' Finset.univ_nonempty (fun x : S × A => |(Qhat - Q2) x.1 x.2|) := rfl
    rw [← hd]
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  · have htri : supNorm (Qhat - Q2) ≤ supNorm (Qhat - Q) + supNorm (Q - Q2) := by
      apply Finset.sup'_le
      intro x _
      have a1 := entry_le (Qhat - Q) x.1 x.2
      have a2 := entry_le (Q - Q2) x.1 x.2
      show |(Qhat - Q2) x.1 x.2| ≤ _
      simp only [Pi.sub_apply] at a1 a2 ⊢
      have := abs_sub_le (Qhat x.1 x.2) (Q x.1 x.2) (Q2 x.1 x.2)
      linarith
    linarith
