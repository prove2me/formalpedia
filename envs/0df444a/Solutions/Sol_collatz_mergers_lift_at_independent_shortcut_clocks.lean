-- Prove2me | solution 1 for collatz_mergers_lift_at_independent_shortcut_clocks
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T21:14:04.194636+00:00
-- url     : https://prove2.me/submissions/0eaa1981-4fd6-4bb5-8da4-9565503c8b41

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

/-- The two lifts may use different binary widths and different positive
multipliers. Equal images at parameters zero and one fix both affine
image functions. -/
private theorem collatz_shortcut_affine_merger_independent_clocks
    (a b u v r s q : ℕ)
    (hzero : runShortcut^[a] r=runShortcut^[b] s)
    (hone : runShortcut^[a] (2^a*u+r)=runShortcut^[b] (2^b*v+s)) :
    runShortcut^[a] ((2^a*u)*q+r)=runShortcut^[b] ((2^b*v)*q+s) := by
  have left_zero : runShortcut^[a] r=(collatzShortcutAffinePair a r).2 := by
    simpa using collatzShortcutAffinePair_sound a 0 r
  have right_zero : runShortcut^[b] s=(collatzShortcutAffinePair b s).2 := by
    simpa using collatzShortcutAffinePair_sound b 0 s
  have hconstant : (collatzShortcutAffinePair a r).2=(collatzShortcutAffinePair b s).2 :=
    left_zero.symm.trans (hzero.trans right_zero)
  rw [collatzShortcutAffinePair_sound,collatzShortcutAffinePair_sound,hconstant] at hone
  have hcoeff : (collatzShortcutAffinePair a r).1*u=(collatzShortcutAffinePair b s).1*v := by
    omega
  rw [Nat.mul_assoc,Nat.mul_assoc,collatzShortcutAffinePair_sound,collatzShortcutAffinePair_sound]
  simp only [←Nat.mul_assoc,hcoeff,hconstant]

/-- A pair of independent-width affine certificates gives a smaller
ordinary merger on the entire original progression. -/
private theorem collatz_affine_merger_independent_clocks (n a b u v r s : ℕ)
    (hsize : 0<s ∧ s<r) (hstride : 2^b*v≤2^a*u) (hres : n%(2^a*u)=r)
    (hzero : runShortcut^[a] r=runShortcut^[b] s)
    (hone : runShortcut^[a] (2^a*u+r)=runShortcut^[b] (2^b*v+s)) :
    ∃ k i j : ℕ, 0<k ∧ k<n ∧ collatzStep^[i] n=collatzStep^[j] k := by
  let q := n/(2^a*u)
  let k := (2^b*v)*q+s
  have hn : n=(2^a*u)*q+r := by
    rw [Nat.add_comm,←hres]
    exact (Nat.mod_add_div _ _).symm
  have hk : 0<k := by dsimp [k]; omega
  have hkn : k<n := by
    rw [hn]
    exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right q hstride) hsize.2
  obtain ⟨i,hi⟩ := shortcutIterate_ordinary n a
  obtain ⟨j,hj⟩ := shortcutIterate_ordinary k b
  refine ⟨k,i,j,hk,hkn,?_⟩
  rw [hi,hj,hn]
  exact collatz_shortcut_affine_merger_independent_clocks a b u v r s q hzero hone

theorem solution (n a b u v s : ℕ) :
    let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let P := 2^a*u
    let Q := 2^b*v
    let r := n%P
    (0<s ∧ s<r ∧ Q≤P ∧ S^[a] r=S^[b] s ∧ S^[a] (P+r)=S^[b] (Q+s)) →
    ∃ k i j : ℕ, 0<k ∧ k<n ∧ collatzStep^[i] n=collatzStep^[j] k := by
  dsimp only
  rintro ⟨hs,hsr,hstride,hzero,hone⟩
  exact collatz_affine_merger_independent_clocks n a b u v _ s
    ⟨hs,hsr⟩ hstride rfl hzero hone
