-- Prove2me | solution 1 for collatz_mergers_lift_from_two_binary_representatives
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T21:06:04.617674+00:00
-- url     : https://prove2.me/submissions/f8d66075-5676-41f8-8a78-5f35dacb0ccb

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

private theorem stepEven (n : ℕ) (h : n % 2 = 0) : collatzStep n = n / 2 := by
  rw [collatzStep, if_pos (Nat.even_iff.mpr h)]

private theorem stepOdd (n : ℕ) (h : n % 2 = 1) : collatzStep n = 3*n+1 := by
  rw [collatzStep, if_neg (by rw [Nat.even_iff, h]; decide)]

private def runShortcut (x : ℕ) : ℕ :=
  if x%2=0 then x/2 else (3*x+1)/2

private theorem runShortcut_reachable (x : ℕ) :
    ∃ t : ℕ, collatzStep^[t] x=runShortcut x := by
  by_cases he : x%2=0
  · exact ⟨1,by rw [Function.iterate_one,stepEven _ he,runShortcut,if_pos he]⟩
  · have ho : x%2=1 := by omega
    refine ⟨2,?_⟩
    rw [show 2=1+1 by decide,Function.iterate_succ_apply',Function.iterate_one,
      stepOdd _ ho,stepEven _ (by omega),runShortcut,if_neg he]

private theorem shortcutIterate_ordinary (x t : ℕ) :
    ∃ j : ℕ, collatzStep^[j] x=runShortcut^[t] x := by
  induction t with
  | zero => exact ⟨0,rfl⟩
  | succ t ih =>
    obtain ⟨j,hj⟩ := ih
    obtain ⟨s,hs⟩ := runShortcut_reachable (runShortcut^[t] x)
    exact ⟨s+j,by rw [Function.iterate_add_apply,hj,hs,Function.iterate_succ_apply']⟩

/-- The first coordinate is the coefficient of the free binary lift.
The second coordinate is the shortcut image of the representative. -/
private def collatzShortcutAffinePair : ℕ → ℕ → ℕ × ℕ
  | 0, x => (1,x)
  | t+1, x =>
    let p := collatzShortcutAffinePair t (runShortcut x)
    (if x%2=0 then p.1 else 3*p.1,p.2)

private theorem shortcut_binary_lift_step (t q x : ℕ) :
    runShortcut (2^(t+1)*q+x)=
      2^t*(if x%2=0 then q else 3*q)+runShortcut x := by
  have hpow : 2^(t+1)*q=2*(2^t*q) := by rw [pow_succ]; ring
  by_cases hx : x%2=0
  · rw [runShortcut,if_pos (by omega : (2^(t+1)*q+x)%2=0),if_pos hx,
      runShortcut,if_pos hx,hpow]
    omega
  · rw [runShortcut,if_neg (by omega : (2^(t+1)*q+x)%2≠0),if_neg hx,
      runShortcut,if_neg hx,hpow]
    have hm : 2^t*(3*q)=3*(2^t*q) := by ring
    rw [hm]
    omega

private theorem collatzShortcutAffinePair_sound (t q x : ℕ) :
    runShortcut^[t] (2^t*q+x)=
      (collatzShortcutAffinePair t x).1*q+(collatzShortcutAffinePair t x).2 := by
  induction t generalizing q x with
  | zero => simp [collatzShortcutAffinePair]
  | succ t ih =>
    rw [Function.iterate_succ_apply,shortcut_binary_lift_step,ih]
    simp only [collatzShortcutAffinePair]
    split <;> ring

/-- Equal images at lifts zero and one force equality of the entire
shortcut affine expressions. The gap and the width are arbitrary. -/
private theorem collatz_shortcut_merger_lifts_from_two_representatives (n d m : ℕ)
    (hn : d<n) (hr : d≤n%2^m)
    (hzero : runShortcut^[m] (n%2^m)=runShortcut^[m] (n%2^m-d))
    (hone : runShortcut^[m] (2^m+n%2^m)=runShortcut^[m] (2^m+n%2^m-d)) :
    runShortcut^[m] n=runShortcut^[m] (n-d) := by
  let r := n%2^m
  let q := n/2^m
  have hr' : d≤r := hr
  have hbase : n=2^m*q+r := by
    rw [Nat.add_comm]
    exact (Nat.mod_add_div n (2^m)).symm
  have hlift : n-d=2^m*q+(r-d) := by omega
  have he₀ (x : ℕ) : runShortcut^[m] x=(collatzShortcutAffinePair m x).2 := by
    simpa using collatzShortcutAffinePair_sound m 0 x
  have he₁ (x : ℕ) : runShortcut^[m] (2^m+x)=
      (collatzShortcutAffinePair m x).1+(collatzShortcutAffinePair m x).2 := by
    simpa using collatzShortcutAffinePair_sound m 1 x
  have hz : runShortcut^[m] r=runShortcut^[m] (r-d) := hzero
  have ho : runShortcut^[m] (2^m+r)=runShortcut^[m] (2^m+(r-d)) := by
    change runShortcut^[m] (2^m+r)=runShortcut^[m] (2^m+r-d) at hone
    rwa [show 2^m+r-d=2^m+(r-d) by omega] at hone
  rw [he₀,he₀] at hz
  rw [he₁,he₁] at ho
  have hs : (collatzShortcutAffinePair m r).1=(collatzShortcutAffinePair m (r-d)).1 := by omega
  calc
    runShortcut^[m] n = (collatzShortcutAffinePair m r).1*q+(collatzShortcutAffinePair m r).2 :=
      (congrArg (runShortcut^[m]) hbase).trans (collatzShortcutAffinePair_sound m q r)
    _ = (collatzShortcutAffinePair m (r-d)).1*q+(collatzShortcutAffinePair m (r-d)).2 := by rw [hs,hz]
    _ = runShortcut^[m] (n-d) :=
      ((congrArg (runShortcut^[m]) hlift).trans (collatzShortcutAffinePair_sound m q (r-d))).symm

/-- Every verified binary lift yields a merger for the ordinary map. -/
private theorem collatz_merger_lifts_from_two_representatives (n d m : ℕ)
    (hd : 0<d) (hn : d<n) (hr : d≤n%2^m)
    (hzero : runShortcut^[m] (n%2^m)=runShortcut^[m] (n%2^m-d))
    (hone : runShortcut^[m] (2^m+n%2^m)=runShortcut^[m] (2^m+n%2^m-d)) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  obtain ⟨a,ha⟩ := shortcutIterate_ordinary n m
  obtain ⟨b,hb⟩ := shortcutIterate_ordinary (n-d) m
  refine ⟨n-d,a,b,by omega,by omega,?_⟩
  rw [ha,hb]
  exact collatz_shortcut_merger_lifts_from_two_representatives n d m hn hr hzero hone

theorem solution (n d m : ℕ) (hd : 0<d) (hn : d<n) :
    let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let r := n%2^m
    (d≤r ∧ S^[m] r=S^[m] (r-d) ∧ S^[m] (2^m+r)=S^[m] (2^m+r-d)) →
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  change (_ ∧ runShortcut^[m] (n%2^m)=runShortcut^[m] (n%2^m-d) ∧
    runShortcut^[m] (2^m+n%2^m)=runShortcut^[m] (2^m+n%2^m-d)) → _
  rintro ⟨hr,hzero,hone⟩
  exact collatz_merger_lifts_from_two_representatives n d m hd hn hr hzero hone
