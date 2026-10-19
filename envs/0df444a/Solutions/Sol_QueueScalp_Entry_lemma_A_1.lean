-- Prove2me | solution 1 for QueueScalp.Entry.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:55:49.440825+00:00
-- url     : https://prove2.me/submissions/2105575a-39f0-4c72-b909-b4cfbf5e8bcb

import Definitions.Def_QueueScalp_Entry_Model
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Function
import Lean.Elab.Tactic.Omega
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

open QueueScalp.Entry

theorem solution (P : Params) (hS : P.Standing) (Lam : ℝ)
    (hLam : 0 < Lam) (price lam q cS ct : ℝ)
    (heq : IsCustEq P Lam price lam q cS ct) :
    cS = cSOf P Lam := by
  have hV : 0 < P.V := lt_trans (one_div_pos.mpr hS.1) hS.2.1
  have hd : 0 < P.mu - lam := sub_pos.mpr heq.stable
  have hct : ct = cS * (1-q) := by
    rw [heq.rate]
    field_simp [heq.cS_pos.ne']
    ring
  have hw : cS * W1 P.mu lam q + price = cS / (P.mu-lam) := by
    calc
      cS * W1 P.mu lam q + price =
          cS * (q * W1 P.mu lam q + (1-q) * W2 P.mu lam q) := by
        rw [heq.indiff,hct]
        ring
      _ = cS / (P.mu-lam) := by unfold W1 W2; ring
  have hj : cS / (P.mu-lam) ≤ P.V := by linarith [heq.join]
  have hclear : cS ≤ P.V * (P.mu-lam) := (div_le_iff₀ hd).mp hj
  have hslack : (1-cS)*(P.V-cS/(P.mu-lam))=0 := by
    have hz : P.V-cS/(P.mu-lam)=P.V-cS*W1 P.mu lam q-price := by linarith
    rw [hz]
    exact heq.slack
  rcases mul_eq_zero.mp hslack with hfull | hroot
  · have hc : cS=1 := by linarith
    have hthr : 1/P.V ≤ P.mu-Lam :=
      (div_le_iff₀ hV).mpr (by rw [heq.thru,hc] at hclear; nlinarith)
    have hb : Lam ≤ P.mu-1/P.V := by linarith
    unfold cSOf
    rw [if_pos hb]
    exact hc
  · have he : P.V*(P.mu-lam)=cS :=
      (eq_div_iff hd.ne').mp (show P.V=cS/(P.mu-lam) by linarith)
    have he2 : cS*(1+Lam*P.V)=P.mu*P.V := by rw [heq.thru] at he; nlinarith
    have hd2 : 0 < 1+Lam*P.V := by positivity
    have hcs : cS=P.mu*P.V/(1+Lam*P.V) :=
      (eq_div_iff hd2.ne').mpr he2
    by_cases hb : Lam ≤ P.mu-1/P.V
    · have hthreshold : 1+Lam*P.V ≤ P.mu*P.V := by
        have hh := (div_le_iff₀ hV).mp (show 1/P.V ≤ P.mu-Lam by linarith)
        nlinarith
      have hc : cS=1 := by
        by_contra hne
        have hcLt : cS<1 := lt_of_le_of_ne heq.cS_le_one hne
        have hh := mul_lt_mul_of_pos_right hcLt hd2
        nlinarith
      unfold cSOf
      rw [if_pos hb]
      exact hc
    · unfold cSOf
      rw [if_neg hb]
      exact hcs



