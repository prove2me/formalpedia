-- Prove2me | solution 1 for collatz_capped_first_meeting_height_sixfold_plus_fifty
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:32:44.722619+00:00
-- url     : https://prove2.me/submissions/9dd22449-fd7e-4c82-a5a5-a0d0c25663c7

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring

private def traceProgression : ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, a, b => some (a, b)
  | t + 1, a, b =>
    if a % 2 = 0 then
      if b % 2 = 0 then traceProgression t (a / 2) (b / 2)
      else traceProgression t (3 * a) (3 * b + 1)
    else none

private theorem traceProgression_sound (t a b u v : ℕ)
    (h : traceProgression t a b = some (u, v)) (q : ℕ) :
    collatzStep^[t] (a * q + b) = u * q + v := by
  induction t generalizing a b with
  | zero =>
    simp [traceProgression] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ t ih =>
    simp only [traceProgression] at h
    split at h
    · rename_i ha
      have ha' : a = 2 * (a / 2) := by omega
      rw [Function.iterate_succ_apply]
      split at h
      · rename_i hb
        have hb' : b = 2 * (b / 2) := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) := by
          calc
            a * q + b = (2 * (a / 2)) * q + 2 * (b / 2) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        rw [hx]
        simpa [collatzStep] using ih _ _ h
      · rename_i hb
        have hb' : b = 2 * (b / 2) + 1 := by omega
        have hx : a * q + b = 2 * ((a / 2) * q + b / 2) + 1 := by
          calc
            a * q + b = (2 * (a / 2)) * q + (2 * (b / 2) + 1) := congrArg₂ (· + ·) (congrArg (· * q) ha') hb'
            _ = _ := by ring
        have hodd : ¬ Even (a * q + b) := by simp [hx]
        rw [collatzStep, if_neg hodd]
        convert ih _ _ h using 2
        ring
    · contradiction

private theorem stepEven (n : ℕ) (h : n % 2 = 0) : collatzStep n = n / 2 := by
  rw [collatzStep, if_pos (Nat.even_iff.mpr h)]

private theorem stepOdd (n : ℕ) (h : n % 2 = 1) : collatzStep n = 3*n+1 := by
  rw [collatzStep, if_neg (by rw [Nat.even_iff, h]; decide)]

private theorem powerHalvings (s k : ℕ) : collatzStep^[s] (2^s*k) = k := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hf : 2^(s+1)*k = 2*(2^s*k) := by rw [pow_succ]; ring
    rw [Function.iterate_succ_apply, hf, stepEven _ (by omega)]
    simpa using ih

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

/-- Connectivity by shortcut Collatz edges with both ends strictly below the cap. -/
private def collatzBelowCap (cap : ℕ) : ℕ → ℕ → Prop :=
  Relation.EqvGen (fun a b => a<cap ∧ b<cap ∧ runShortcut a=b)

private theorem belowCap_equivalence (cap : ℕ) : Equivalence (collatzBelowCap cap) :=
  Relation.EqvGen.is_equivalence _

private theorem belowCap_lift {R : ℕ → ℕ → Prop} (hR : Equivalence R) (f : ℕ → ℕ)
    {cap a b : ℕ} (h : collatzBelowCap cap a b)
    (hedge : ∀ x y : ℕ, x<cap → y<cap → runShortcut x=y → R (f x) (f y)) :
    R (f a) (f b) := by
  induction h with
  | rel x y h => exact hedge x y h.1 h.2.1 h.2.2
  | refl x => exact hR.refl _
  | symm _ _ _ ih => exact hR.symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact hR.trans ih₁ ih₂

private theorem shortcutIterate_ordinary (x t : ℕ) :
    ∃ j : ℕ, collatzStep^[j] x=runShortcut^[t] x := by
  induction t with
  | zero => exact ⟨0,rfl⟩
  | succ t ih =>
    obtain ⟨j,hj⟩ := ih
    obtain ⟨s,hs⟩ := runShortcut_reachable (runShortcut^[t] x)
    exact ⟨s+j,by rw [Function.iterate_add_apply,hj,hs,Function.iterate_succ_apply']⟩

private theorem shortcut_preimage_cases {a b : ℕ} (h : runShortcut a=b) :
    a=2*b ∨ (b%3=2 ∧ 3*a+1=2*b) := by
  by_cases he : a%2=0
  · rw [runShortcut,if_pos he] at h
    exact Or.inl (by omega)
  · rw [runShortcut,if_neg he] at h
    have hmul : 3*a+1=2*b := by omega
    exact Or.inr ⟨by omega,hmul⟩

/-- A directed shortcut path whose entire trace is below the cap. -/
private def collatzShortcutReachesBelow (H x y : ℕ) : Prop :=
  ∃ t : ℕ, (runShortcut^[t] x = y) ∧ ∀ i : ℕ, i ≤ t → runShortcut^[i] x < H

private theorem shortcutReach_belowCap {H x y : ℕ}
    (h : collatzShortcutReachesBelow H x y) :
    collatzBelowCap H x y := by
  obtain ⟨t,ht,hcap⟩ := h
  rw [←ht]
  clear ht
  induction t with
  | zero => exact (belowCap_equivalence _).refl _
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    apply (belowCap_equivalence H).trans (ih (fun i hi => hcap i (by omega)))
    exact .rel _ _ ⟨hcap t (by omega),
      by simpa only [Function.iterate_succ_apply'] using hcap (t+1) (by omega),rfl⟩

private theorem shortcutReachBelow_trans {H a b c : ℕ}
    (hab : collatzShortcutReachesBelow H a b) (hbc : collatzShortcutReachesBelow H b c) :
    collatzShortcutReachesBelow H a c := by
  obtain ⟨t,ht,hpath⟩ := hab
  obtain ⟨u,hu,hrest⟩ := hbc
  refine ⟨u+t,by rwa [Function.iterate_add_apply,ht],?_⟩
  intro i hi
  by_cases hsmall : i≤t
  · exact hpath i hsmall
  · rw [show i=(i-t)+t by omega,Function.iterate_add_apply,ht]
    exact hrest (i-t) (by omega)

private theorem shortcutReachBelow_suffix {H x y z j t : ℕ}
    (hle : j≤t) (hj : runShortcut^[j] x=y) (ht : runShortcut^[t] x=z)
    (h : ∀ i : ℕ, i≤t → runShortcut^[i] x<H) :
    collatzShortcutReachesBelow H y z := by
  refine ⟨t-j,?_ ,?_⟩
  · rw [←hj,←Function.iterate_add_apply,show (t-j)+j=t by omega]
    exact ht
  · intro i hi
    rw [←hj,←Function.iterate_add_apply]
    exact h (i+j) (by omega)

private theorem shortcutReachBelow_align {H x y z : ℕ}
    (hy : collatzShortcutReachesBelow H x y) (hz : collatzShortcutReachesBelow H x z) :
    collatzShortcutReachesBelow H y z ∨ collatzShortcutReachesBelow H z y := by
  obtain ⟨j,hj,hpath⟩ := hy
  obtain ⟨t,ht,hrest⟩ := hz
  rcases le_total j t with h | h
  · exact Or.inl (shortcutReachBelow_suffix h hj ht hrest)
  · exact Or.inr (shortcutReachBelow_suffix h ht hj hpath)

private def cappedCoal (H a b : ℕ) : Prop :=
  a=b ∨ ∃ z : ℕ, collatzShortcutReachesBelow H a z ∧ collatzShortcutReachesBelow H b z

private theorem cappedCoal_equivalence (H : ℕ) : Equivalence (cappedCoal H) := by
  constructor
  · exact fun _ => Or.inl rfl
  · rintro a b (h | ⟨z,ha,hb⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨z,hb,ha⟩
  · rintro a b c (rfl | ⟨y,ha,hby⟩) (rfl | ⟨z,hbz,hc⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨z,hbz,hc⟩
    · exact Or.inr ⟨y,ha,hby⟩
    · rcases shortcutReachBelow_align hby hbz with h | h
      · exact Or.inr ⟨z,shortcutReachBelow_trans ha h,hc⟩
      · exact Or.inr ⟨y,ha,shortcutReachBelow_trans hc h⟩

/-- Connectivity of two bounded vertices is equivalent to a meeting of
directed trajectories that stay below the same cap. -/
private theorem collatz_below_cap_iff_bounded_meeting (H a b : ℕ) (ha : a<H) :
    collatzBelowCap H a b ↔
      ∃ z : ℕ, collatzShortcutReachesBelow H a z ∧ collatzShortcutReachesBelow H b z := by
  constructor
  · intro h
    have hh : cappedCoal H (id a) (id b) := by
      refine belowCap_lift (cappedCoal_equivalence H) id h ?_
      intro x y hx hy edge
      refine Or.inr ⟨y,⟨1,by simpa using edge,?_⟩,⟨0,rfl,?_⟩⟩
      · intro i hi
        have hei : i=0 ∨ i=1 := by omega
        rcases hei with rfl | rfl
        · exact hx
        · simpa [edge] using hy
      · intro i hi
        have he : i=0 := by omega
        simpa [he] using hy
    rcases hh with he | ⟨z,h₁,h₂⟩
    · change a=b at he
      subst b
      have hrefl : collatzShortcutReachesBelow H a a := ⟨0,rfl,fun i hi => by
        have he : i=0 := by omega
        simpa [he] using ha⟩
      exact ⟨a,hrefl,hrefl⟩
    · exact ⟨z,h₁,h₂⟩
  · rintro ⟨z,h₁,h₂⟩
    exact (belowCap_equivalence H).trans (shortcutReach_belowCap h₁)
      ((belowCap_equivalence H).symm (shortcutReach_belowCap h₂))

private theorem oddStepThenHalves (x y a : ℕ) (ha : 0<a)
    (h : 3*x+1=2^a*y) : collatzStep^[a+1] x=y := by
  have he : (3*x+1)%2=0 := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
    have heq : 2^(j+1)*y=2*(2^j*y) := by rw [pow_succ]; ring
    rw [h,heq]
    omega
  have ho : x%2=1 := by omega
  rw [Function.iterate_add_apply,Function.iterate_one,stepOdd _ ho,h,powerHalvings]

private theorem collatz_no_second_visitor_requires_later_original_clock (n : ℕ)
    (hno : ¬∃ k t : ℕ, 0<k ∧ k<n ∧ collatzStep^[t] k=collatzStep^[2] n)
    (k a b : ℕ) (hk : 0<k) (hkn : k<n)
    (h : collatzStep^[a] n=collatzStep^[b] k) : 2<a := by
  by_contra! he
  apply hno
  refine ⟨k,(2-a)+b,hk,hkn,?_⟩
  rw [Function.iterate_add_apply,←h,←Function.iterate_add_apply]
  rw [show (2-a)+a=2 by omega]

private theorem fourfold_in_shortcut_trace {H u a y : ℕ} (hne : u≠2*y)
    (hy : y%3=2) (h : runShortcut^[a] u=2*y)
    (hcap : ∀ i : ℕ, i≤a → runShortcut^[i] u<H) : 4*y<H := by
  cases a with
  | zero => exact (hne h).elim
  | succ a =>
    rw [Function.iterate_succ_apply'] at h
    rcases shortcut_preimage_cases h with hdouble | ⟨hmod,_⟩
    · have hp := hcap a (by omega)
      rw [hdouble] at hp
      omega
    · omega

/-- At the first touch of two capped shortcut traces, one route comes
from an odd parent and the other passes through four times the target. -/
private theorem collatz_capped_contact_has_odd_parent (H n k : ℕ)
    (hnH : n<H) (hodd : n%2=1) (hkn : k<n)
    (hstay : ∀ j : ℕ, n≤runShortcut^[j] n)
    (hnoStart : ∀ b : ℕ, runShortcut^[b] k≠n)
    (hconn : collatzBelowCap H n k) :
    ∃ a b q : ℕ, runShortcut^[a] n=runShortcut^[b] k ∧
      q%2=1 ∧ 3*q+1=2*(runShortcut^[a] n) ∧ 6*q+2<H := by
  classical
  let Good := fun a : ℕ => ∃ b : ℕ, runShortcut^[a] n=runShortcut^[b] k ∧
    (∀ i : ℕ, i≤a → runShortcut^[i] n<H) ∧
    (∀ i : ℕ, i≤b → runShortcut^[i] k<H)
  obtain ⟨y,⟨a,ha,haH⟩,⟨b,hb,hbH⟩⟩ :=
    (collatz_below_cap_iff_bounded_meeting H n k hnH).mp hconn
  have hex : ∃ a, Good a := ⟨a,b,ha.trans hb.symm,haH,hbH⟩
  let a := Nat.find hex
  obtain ⟨b,hab,hpath,hvisit⟩ := Nat.find_spec hex
  change runShortcut^[a] n=runShortcut^[b] k at hab
  change ∀ i : ℕ, i≤a → runShortcut^[i] n<H at hpath
  have ha0 : a≠0 := by
    intro he
    rw [he] at hab
    exact hnoStart b hab.symm
  have hlow : n≤runShortcut^[a] n := hstay a
  have hb0 : b≠0 := by
    intro he
    rw [he] at hab
    change runShortcut^[a] n=k at hab
    omega
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero ha0
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hb0
  let y := runShortcut^[a] n
  let x := runShortcut^[i] n
  let z := runShortcut^[j] k
  have hx : runShortcut x=y := by dsimp [x,y]; rw [hi,Function.iterate_succ_apply']
  have hz : runShortcut z=y := by
    calc
      runShortcut z = runShortcut^[j.succ] k := (Function.iterate_succ_apply' _ _ _).symm
      _ = y := by rw [←hj]; exact hab.symm
  have hdiff : x≠z := by
    intro he
    have hg : Good i := ⟨j,he,fun l hl => hpath l (by omega),fun l hl => hvisit l (by omega)⟩
    have hmin : a≤i := Nat.find_min' hex hg
    omega
  rcases shortcut_preimage_cases hx with hx' | ⟨hmy,hx'⟩
  · rcases shortcut_preimage_cases hz with hz' | ⟨hmy,hz'⟩
    · exact (hdiff (hx'.trans hz'.symm)).elim
    · have h4 := fourfold_in_shortcut_trace (by omega : n≠2*y) hmy hx'
        (fun l hl => hpath l (by omega))
      exact ⟨a,b,z,hab,by omega,hz',by omega⟩
  · rcases shortcut_preimage_cases hz with hz' | ⟨_,hz'⟩
    · have h4 := fourfold_in_shortcut_trace (by omega : k≠2*y) hmy hz'
        (fun l hl => hvisit l (by omega))
      exact ⟨a,b,x,hab,by omega,hx',by omega⟩
    · exact (hdiff (by omega)).elim

private theorem first_three_nearby_odd_starts_descend (n q : ℕ)
    (hn : 32≤n) (hc : n%16=15) (hodd : q%2=1) (hlo : n<q) (hhi : q<n+8) :
    ∃ t : ℕ, 2≤t ∧ collatzStep^[t] q<n := by
  let m := n/16
  have hm : n=16*m+15 := by dsimp [m]; omega
  have hcases : q=n+2 ∨ q=n+4 ∨ q=n+6 := by omega
  rcases hcases with h | h | h
  · have hq : q=16*m+17 := by omega
    refine ⟨3,by decide,?_⟩
    rw [hq,traceProgression_sound 3 16 17 12 13 (by decide) m]
    omega
  · have hq : q=16*m+19 := by omega
    refine ⟨6,by decide,?_⟩
    rw [hq,traceProgression_sound 6 16 19 9 11 (by decide) m]
    omega
  · have hq : q=16*m+21 := by omega
    refine ⟨3,by decide,?_⟩
    rw [hq,traceProgression_sound 3 16 21 12 16 (by decide) m]
    omega

/-- When the original trace never descends and has no smaller visitor
to its second iterate or through an odd pair, any capped merger must
reach height at least 6n+50. The cap here is exclusive. -/
private theorem collatz_frontier_capped_merge_height (H n k : ℕ)
    (hnH : n<H) (hlarge : 32≤n) (hclass : n%16=15)
    (hstay : ∀ a : ℕ, n≤collatzStep^[a] n)
    (hno : ¬∃ k t : ℕ, 0<k ∧ k<n ∧ collatzStep^[t] k=collatzStep^[2] n)
    (hpair : ∀ q a : ℕ, 0<q → q<n → q%2=1 → collatzStep^[2] q≠collatzStep^[a] n)
    (hk : 0<k) (hkn : k<n) (hconn : collatzBelowCap H n k) :
    6*n+50<H := by
  have hshortcut : ∀ j : ℕ, n≤runShortcut^[j] n := by
    intro j
    obtain ⟨t,ht⟩ := shortcutIterate_ordinary n j
    exact ht ▸ hstay t
  have hnostart : ∀ b : ℕ, runShortcut^[b] k≠n := by
    intro b hb
    obtain ⟨t,ht⟩ := shortcutIterate_ordinary k b
    have hfirst : collatzStep^[0] n=collatzStep^[t] k := (ht.trans hb).symm
    have hbad := collatz_no_second_visitor_requires_later_original_clock n hno k 0 t hk hkn hfirst
    omega
  obtain ⟨a,b,q,hmeet,ho,hq,hH⟩ :=
    collatz_capped_contact_has_odd_parent H n k hnH (by omega) hkn hshortcut hnostart hconn
  obtain ⟨t,ht⟩ := shortcutIterate_ordinary n a
  have hq2 : collatzStep^[2] q=runShortcut^[a] n :=
    oddStepThenHalves q (runShortcut^[a] n) 1 (by decide) (by simpa using hq)
  have hnq : n≤q := by
    by_contra! hsmall
    exact hpair q t (by omega) hsmall ho (hq2.trans ht.symm)
  have hne : q≠n := by
    intro hsame
    obtain ⟨j,hj⟩ := shortcutIterate_ordinary k b
    rw [hsame] at hq2
    exact hno ⟨k,j,hk,hkn,hj.trans (hmeet.symm.trans hq2.symm)⟩
  have hgap : n+8≤q := by
    by_contra! hsmall
    obtain ⟨j,hj,hbelow⟩ := first_three_nearby_odd_starts_descend n q
      hlarge hclass ho (by omega) hsmall
    have heq : collatzStep^[(j-2)+t] n=collatzStep^[j] q := by
      rw [Function.iterate_add_apply,ht,←hq2,←Function.iterate_add_apply,
        show (j-2)+2=j by omega]
    have hbad := hstay ((j-2)+t)
    rw [heq] at hbad
    omega
  omega

theorem solution (H n k : ℕ)
    (hnH : n<H) (hlarge : 32≤n) (hclass : n%16=15)
    (hstay : ∀ a : ℕ, n≤collatzStep^[a] n)
    (hno : ¬∃ q t : ℕ, 0<q ∧ q<n ∧ collatzStep^[t] q=collatzStep^[2] n)
    (hpair : ∀ q a : ℕ, 0<q → q<n → q%2=1 → collatzStep^[2] q≠collatzStep^[a] n)
    (hk : 0<k) (hkn : k<n) :
    let shortcut : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    Relation.EqvGen (fun x y : ℕ => x<H ∧ y<H ∧ shortcut x=y) n k → 6*n+50<H := by
  change collatzBelowCap H n k → 6*n+50<H
  exact collatz_frontier_capped_merge_height H n k hnH hlarge hclass hstay hno hpair hk hkn
