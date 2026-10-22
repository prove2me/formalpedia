-- Prove2me | solution 1 for RobustFPA.VarBid.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T16:22:40.83958+00:00
-- url     : https://prove2.me/submissions/e0974f2d-3717-4d7a-917a-fbad7b8cf5d3

/-
Robust first-price bidding: exact analytic maximizer of uPlus on [L,infinity).
Original mathematics: Bernhard Kasberger and Karl H. Schlag. Platform formulation:
mikedeng1; prior statement confirmation: Shuze Chen (not proof review).
Platform cites September3,2022; source check uses author-hosted March27,2023,
whose identical maximizer formula is on p22. The 2022 PDF was unavailable.
This does not identify actual worst-case auction distributions or prove minimax optimality.
Alexander Richard Towell: research direction and archive stewardship.
OpenAI Codex: substantial proof construction, verification and documentation.
Lean/Mathlib contributors: calculus and proof infrastructure.
Established mathematics formalized; no mathematical novelty or independent human review claimed.
-/
import Mathlib
import Definitions.Def_RobustFPA_VarBid_ClosedForms

open Set
open RobustFPA.VarBid
set_option autoImplicit false

namespace RobustBidResearch

lemma base_pos (τ L v b : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hLv : L < v) (hb : L ≤ b) : 0 < 1-τ+τ*((b-L)/(v-L)) := by
  have hp := mul_nonneg hτ0.le (div_nonneg (sub_nonneg.mpr hb) (sub_pos.mpr hLv).le)
  linarith

lemma plus_cont (n : ℕ) (τ L v : ℝ) : Continuous (uPlus n τ L v) := by
  unfold uPlus
  fun_prop

lemma plus_deriv (n : ℕ) (hn : 2 ≤ n) (τ L v b : ℝ)
    (hτ0 : 0 < τ) (hLv : L < v) :
    HasDerivAt (uPlus n τ L v)
      ((1-τ+τ*((b-L)/(v-L)))^(n-2) * ((n:ℝ)*τ/(v-L)) * (bTilde n τ L v-b)) b := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n=k+2 := ⟨n-2,by omega⟩
  have hnum : (k:ℝ)+2 ≠ 0 := by positivity
  have hd : v-L ≠ 0 := ne_of_gt (sub_pos.mpr hLv)
  have ht : τ ≠ 0 := ne_of_gt hτ0
  have ha : HasDerivAt (fun z : ℝ => 1-τ+τ*((z-L)/(v-L))) (τ/(v-L)) b := by
    convert (hasDerivAt_const b (1-τ)).add ((((hasDerivAt_id b).sub_const L).div_const (v-L)).const_mul τ) using 1 <;> first | rfl | ring
  have h := ((hasDerivAt_const b v).sub (hasDerivAt_id b)).mul (ha.pow (k+1))
  unfold uPlus bTilde
  simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,Nat.cast_add,Nat.cast_ofNat]
  convert h using 1 <;> try rfl
  simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply,Pi.sub_apply,id_eq,pow_succ]
  field_simp [hd,ht,hnum]
  <;> ring

lemma plus_maximum (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    IsMaxOn (uPlus n τ L v) (Ici L) (max (bTilde n τ L v) L) := by
  have hc := plus_cont n τ L v
  have hp : 0 ≤ (n:ℝ)*τ/(v-L) := div_nonneg (mul_nonneg (Nat.cast_nonneg n) hτ0.le) (sub_pos.mpr hLv).le
  apply isMaxOn_Ici_of_deriv hc.continuousAt hc.continuousAt
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    exact (plus_deriv n hn τ L v b hτ0 hLv).differentiableAt.differentiableWithinAt
  · intro b hb
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    have hbt : b < bTilde n τ L v := by
      rcases lt_max_iff.mp hb.2 with h | h
      · exact h
      · linarith [hb.1]
    exact mul_nonneg (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hb.1.le).le _) hp)
      (sub_nonneg.mpr hbt.le)
  · intro b hb
    have hbt : bTilde n τ L v ≤ b := (le_max_left _ _).trans hb.le
    have hLb : L ≤ b := (le_max_right _ _).trans hb.le
    rw [(plus_deriv n hn τ L v b hτ0 hLv).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (pow_nonneg (base_pos τ L v b hτ0 hτ1 hLv hLb).le _) hp)
      (sub_nonpos.mpr hbt)

end RobustBidResearch

theorem solution (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hLv : L < v) :
    L ≤ max (bTilde n τ L v) L ∧
    ∀ b : ℝ, L ≤ b → uPlus n τ L v b ≤ uPlus n τ L v (max (bTilde n τ L v) L) := by
  exact ⟨le_max_right _ _,fun b hb => RobustBidResearch.plus_maximum n hn τ L v hτ0 hτ1 hLv hb⟩

#print axioms solution
