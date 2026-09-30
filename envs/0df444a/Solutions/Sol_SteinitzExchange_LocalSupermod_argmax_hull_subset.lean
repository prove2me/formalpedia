-- Prove2me | solution 1 for SteinitzExchange.LocalSupermod.argmax_hull_subset
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T10:29:25.110641+00:00
-- url     : https://prove2.me/submissions/704aa4e7-e4f3-4ba1-8fe5-21a5ad6c505c

import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange
import Mathlib.Tactic
open SteinitzExchange.LocalSupermod

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ) (z : V → ℤ),
    toReal z ∈ hull (argmaxB B g) → z ∈ argmaxB B g) := by
  classical
  intro h
  let f0 : PUnit → ℤ := fun _ => 0
  let f2 : PUnit → ℤ := fun _ => 2
  let z : PUnit → ℤ := fun _ => 1
  let B : Finset (PUnit → ℤ) := {f0,f2}
  have ha : argmaxB B (fun _ => 0)=B := by ext q;simp [argmaxB]
  have h0 : toReal f0 ∈ hull B := subset_convexHull ℝ _ ⟨f0,by simp [B],rfl⟩
  have h2 : toReal f2 ∈ hull B := subset_convexHull ℝ _ ⟨f2,by simp [B],rfl⟩
  have hm : toReal z ∈ hull B := by
    have hh:=(convex_convexHull ℝ (toReal '' (B : Set (PUnit → ℤ)))) h0 h2
      (show 0 ≤ (1/2:ℝ) by norm_num) (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num)
    convert! hh using 1
    funext v
    norm_num [toReal,z,f0,f2]
  have hh:=h B (fun _ => 0) z (by simpa only [ha] using hm)
  rw [ha] at hh
  norm_num [B,z,f0,f2,funext_iff] at hh
