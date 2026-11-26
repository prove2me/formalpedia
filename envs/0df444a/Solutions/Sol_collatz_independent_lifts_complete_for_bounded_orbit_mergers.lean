-- Prove2me | solution 1 for collatz_independent_lifts_complete_for_bounded_orbit_mergers
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:51:11.044875+00:00
-- url     : https://prove2.me/submissions/16e57cfb-9d57-4031-a61d-d78604cc1ab6

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Lattice

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

private abbrev shortcutMultiplier (t x : ℕ) : ℕ := (collatzShortcutAffinePair t x).1

private theorem shortcutMultiplier_pos (t x : ℕ) : 0<shortcutMultiplier t x := by
  induction t generalizing x with
  | zero => simp [shortcutMultiplier,collatzShortcutAffinePair]
  | succ t ih =>
    simp only [shortcutMultiplier,collatzShortcutAffinePair]
    split
    · exact ih _
    · exact Nat.mul_pos (by decide) (ih _)

private theorem shortcutMultiplier_add (a b x : ℕ) :
    shortcutMultiplier (a+b) x=shortcutMultiplier a x*shortcutMultiplier b (runShortcut^[a] x) := by
  induction a generalizing x with
  | zero => simp [shortcutMultiplier,collatzShortcutAffinePair]
  | succ a ih =>
    rw [show a.succ+b=(a+b).succ by omega,Function.iterate_succ_apply]
    change (if x%2=0 then shortcutMultiplier (a+b) (runShortcut x)
      else 3*shortcutMultiplier (a+b) (runShortcut x)) =
      (if x%2=0 then shortcutMultiplier a (runShortcut x)
        else 3*shortcutMultiplier a (runShortcut x))*shortcutMultiplier b (runShortcut^[a] (runShortcut x))
    rw [ih]
    split <;> ring

private theorem shortcutMultiplier_lower (t x : ℕ) :
    shortcutMultiplier t x*x≤2^t*runShortcut^[t] x ∧
      (shortcutMultiplier t x≠1 → shortcutMultiplier t x*x<2^t*runShortcut^[t] x) := by
  induction t generalizing x with
  | zero => simp [shortcutMultiplier,collatzShortcutAffinePair]
  | succ t ih =>
    let y := runShortcut x
    let z := runShortcut^[t] y
    let A := shortcutMultiplier t y
    obtain ⟨hle,hlt⟩ := ih y
    change A*y≤2^t*z at hle
    change A≠1 → A*y<2^t*z at hlt
    rw [Function.iterate_succ_apply]
    change (if x%2=0 then A else 3*A)*x≤2^(t+1)*z ∧
      ((if x%2=0 then A else 3*A)≠1 → (if x%2=0 then A else 3*A)*x<2^(t+1)*z)
    by_cases h : x%2=0
    · have hx : x=2*y := by dsimp [y]; rw [runShortcut,if_pos h]; omega
      have hl : A*x=2*(A*y) := by rw [hx]; ring
      have hr : (2:ℕ)^(t+1)*z=2*(2^t*z) := by rw [pow_succ]; ring
      rw [if_pos h,hl,hr]
      exact ⟨Nat.mul_le_mul_left _ hle,fun h => Nat.mul_lt_mul_of_pos_left (hlt h) (by decide)⟩
    · have hx : 2*y=3*x+1 := by dsimp [y]; rw [runShortcut,if_neg h]; omega
      have hr : (2:ℕ)^(t+1)*z=2*(2^t*z) := by rw [pow_succ]; ring
      rw [if_neg h,hr]
      have hfinal : (3*A)*x<2*(2^t*z) := calc
        _ = A*(3*x) := by ring
        _ < A*(2*y) := by rw [hx]; exact Nat.mul_lt_mul_of_pos_left (by omega) (shortcutMultiplier_pos t y)
        _ = 2*(A*y) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hle
      exact ⟨hfinal.le,fun _ => hfinal⟩

private theorem shortcut_return_multiplier_lt (p x : ℕ) (hp : 0<p)
    (hret : runShortcut^[p] x=x) : shortcutMultiplier p x<2^p := by
  by_cases h : shortcutMultiplier p x=1
  · rw [h]
    have htwo : (2:ℕ)^1≤2^p := Nat.pow_le_pow_right (by decide) hp
    omega
  · have hlt := (shortcutMultiplier_lower p x).2 h
    rw [hret] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt

private theorem shortcut_return_repeats (p x m : ℕ) (hret : runShortcut^[p] x=x) :
    runShortcut^[p*m] x=x ∧ shortcutMultiplier (p*m) x=(shortcutMultiplier p x)^m := by
  induction m with
  | zero => simp [shortcutMultiplier,collatzShortcutAffinePair]
  | succ m ih =>
    constructor
    · rw [Nat.mul_succ,Function.iterate_add_apply,hret,ih.1]
    · rw [Nat.mul_succ,shortcutMultiplier_add,ih.1,ih.2,pow_succ]

/-- A strict ratio between positive natural numbers separates any fixed
positive factors after a sufficiently large common power. -/
private theorem nat_gaps_dominate_fixed_factors (A B U V m₀ : ℕ)
    (hA : 0<A) (hAB : A<B) (hV : 0<V) :
    ∃ m : ℕ, m₀≤m ∧ A^m*U < B^m*V := by
  have hprod (m : ℕ) : A^m*(A+m)≤B^m*A := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hm : A*(A+m.succ)≤B*(A+m) := calc
        _ ≤ (A+1)*(A+m) := by
          have he : (A+1)*(A+m)=A*(A+m.succ)+m := by simp only [Nat.succ_eq_add_one]; ring
          rw [he]
          omega
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      calc
        _ = A^m*(A*(A+m.succ)) := by simp only [pow_succ,Nat.succ_eq_add_one]; ring
        _ ≤ A^m*(B*(A+m)) := Nat.mul_le_mul_left _ hm
        _ = B*(A^m*(A+m)) := by ring
        _ ≤ B*(B^m*A) := Nat.mul_le_mul_left _ ih
        _ = B^m.succ*A := by rw [pow_succ]; ring
  let m := U*A+m₀+1
  have hlt : (A^m*U)*A<(B^m*V)*A := calc
    _ = A^m*(U*A) := by ring
    _ < A^m*(A+m) := Nat.mul_lt_mul_of_pos_left (by dsimp [m]; omega) (Nat.pow_pos hA)
    _ ≤ B^m*A := hprod m
    _ ≤ _ := by
      have hV' : B^m≤B^m*V := Nat.le_mul_of_pos_right _ hV
      exact Nat.mul_le_mul_right _ hV'
  exact ⟨m,by dsimp [m]; omega,Nat.lt_of_mul_lt_mul_right hlt⟩

private def shortcutCoal (a b : ℕ) : Prop := ∃ i j : ℕ, runShortcut^[i] a=runShortcut^[j] b

private theorem shortcutCoal_symm {a b : ℕ} (h : shortcutCoal a b) : shortcutCoal b a := by
  obtain ⟨i,j,he⟩ := h
  exact ⟨j,i,he.symm⟩

private theorem shortcutCoal_trans {a b c : ℕ} (h₁ : shortcutCoal a b)
    (h₂ : shortcutCoal b c) : shortcutCoal a c := by
  obtain ⟨s,t,hab⟩ := h₁
  obtain ⟨u,v,hbc⟩ := h₂
  refine ⟨u+s,t+v,?_⟩
  rw [Function.iterate_add_apply,Function.iterate_add_apply,hab,←hbc,
    ←Function.iterate_add_apply,←Function.iterate_add_apply,Nat.add_comm u t]

private theorem ordinary_step_shortcutCoal (x : ℕ) : shortcutCoal x (collatzStep x) := by
  by_cases he : x%2=0
  · exact ⟨1,0,by rw [Function.iterate_one,runShortcut,if_pos he,stepEven _ he]; rfl⟩
  · have ho : x%2=1 := by omega
    exact ⟨1,1,by rw [Function.iterate_one,stepOdd _ ho,runShortcut,if_neg he,
      runShortcut,if_pos (by omega : (3*x+1)%2=0)]⟩

private theorem ordinary_iterate_shortcutCoal (n t : ℕ) : shortcutCoal n (collatzStep^[t] n) := by
  induction t with
  | zero => exact ⟨0,0,rfl⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact shortcutCoal_trans ih (ordinary_step_shortcutCoal _)

private theorem ordinary_merger_to_shortcutCoal (n k i j : ℕ)
    (he : collatzStep^[i] n=collatzStep^[j] k) : shortcutCoal n k := by
  have h := ordinary_iterate_shortcutCoal k j
  rw [←he] at h
  exact shortcutCoal_trans (ordinary_iterate_shortcutCoal n i) (shortcutCoal_symm h)

private def collatzIndependentLift (n : ℕ) : Prop :=
  ∃ a b u v s : ℕ, 0<u ∧ 0<v ∧ a≠b ∧
    let P := 2^a*u
    let Q := 2^b*v
    let r := n%P
    0<s ∧ s<r ∧ Q≤P ∧ runShortcut^[a] r=runShortcut^[b] s ∧
      runShortcut^[a] (P+r)=runShortcut^[b] (Q+s)

private theorem independent_lift_of_shortcut_multiplier_order (n k a b : ℕ)
    (hk : 0<k) (hkn : k<n) (hab : a≠b)
    (hmeet : runShortcut^[a] n=runShortcut^[b] k)
    (horder : 2^b*shortcutMultiplier a n≤2^a*shortcutMultiplier b k) :
    collatzIndependentLift n := by
  let A := shortcutMultiplier a n
  let B := shortcutMultiplier b k
  let w := n+1
  let u := B*w
  let v := A*w
  have hu : 0<u := Nat.mul_pos (shortcutMultiplier_pos b k) (by dsimp [w]; omega)
  have hv : 0<v := Nat.mul_pos (shortcutMultiplier_pos a n) (by dsimp [w]; omega)
  have hbig : n<2^a*u := calc
    _ < w := by dsimp [w]; omega
    _ ≤ u := Nat.le_mul_of_pos_left _ (shortcutMultiplier_pos b k)
    _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hstride : 2^b*v≤2^a*u := by
    simpa only [u,v,←Nat.mul_assoc] using Nat.mul_le_mul_right w horder
  refine ⟨a,b,u,v,k,hu,hv,hab,?_⟩
  dsimp only
  rw [Nat.mod_eq_of_lt hbig]
  refine ⟨hk,hkn,hstride,hmeet,?_⟩
  have hfirst : runShortcut^[a] n=(collatzShortcutAffinePair a n).2 := by
    simpa using collatzShortcutAffinePair_sound a 0 n
  have hsecond : runShortcut^[b] k=(collatzShortcutAffinePair b k).2 := by
    simpa using collatzShortcutAffinePair_sound b 0 k
  have hconst := hfirst.symm.trans (hmeet.trans hsecond)
  rw [collatzShortcutAffinePair_sound,collatzShortcutAffinePair_sound,hconst]
  change (A*(B*w))+(collatzShortcutAffinePair b k).2=
    (B*(A*w))+(collatzShortcutAffinePair b k).2
  ring

private theorem shortcut_bounded_has_return (n H : ℕ)
    (hbound : ∀ t : ℕ, runShortcut^[t] n≤H) :
    ∃ a p : ℕ, 0<p ∧ runShortcut^[p] (runShortcut^[a] n)=runShortcut^[a] n := by
  by_contra! h
  let f : Fin (H+2) → Fin (H+1) := fun i => ⟨runShortcut^[i.val] n,by have hb := hbound i.val; omega⟩
  have hm : ∀ a b : ℕ, a<b → runShortcut^[a] n≠runShortcut^[b] n := by
    intro a b hab he
    apply h a (b-a) (by omega)
    rw [←Function.iterate_add_apply,show b-a+a=b by omega]
    exact he.symm
  have hinj : Function.Injective f := by
    intro a b hf
    have hv : runShortcut^[a.val] n=runShortcut^[b.val] n := congrArg Fin.val hf
    apply Fin.ext
    by_contra! hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact hm a.val b.val hl hv
    · exact hm b.val a.val hl hv.symm
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  omega

/-- A bounded original orbit can pad one side of an existing merger
by full returns. Each return reduces the normalized multiplier. -/
private theorem collatz_bounded_ordinary_merger_iff_independent_lift (n H : ℕ)
    (hbound : ∀ t : ℕ, collatzStep^[t] n≤H) :
    (∃ k i j : ℕ, 0<k ∧ k<n ∧ collatzStep^[i] n=collatzStep^[j] k) ↔ collatzIndependentLift n := by
  constructor
  · rintro ⟨k,i,j,hk,hkn,hij⟩
    obtain ⟨a,b,hab⟩ := ordinary_merger_to_shortcutCoal n k i j hij
    have hs : ∀ t : ℕ, runShortcut^[t] n≤H := by
      intro t
      obtain ⟨v,hv⟩ := shortcutIterate_ordinary n t
      exact hv ▸ hbound v
    obtain ⟨s,p,hp,hcycle⟩ := shortcut_bounded_has_return n H hs
    let c := runShortcut^[a+s] n
    have hmeet : c=runShortcut^[b+s] k := by
      dsimp [c]
      rw [Nat.add_comm a s,Nat.add_comm b s,Function.iterate_add_apply,Function.iterate_add_apply,hab]
    have hret : runShortcut^[p] c=c := by
      dsimp [c]
      rw [Function.iterate_add_apply,←Function.iterate_add_apply,Nat.add_comm p a,
        Function.iterate_add_apply,hcycle]
    let A := shortcutMultiplier (a+s) n
    let B := shortcutMultiplier (b+s) k
    let M := shortcutMultiplier p c
    obtain ⟨m,hm,hratio⟩ := nat_gaps_dominate_fixed_factors M (2^p) (2^(b+s)*A) (2^(a+s)*B)
      (b+s+1) (shortcutMultiplier_pos p c) (shortcut_return_multiplier_lt p c hp hret)
      (Nat.mul_pos (Nat.two_pow_pos _) (shortcutMultiplier_pos (b+s) k))
    obtain ⟨hloop,hmult⟩ := shortcut_return_repeats p c m hret
    have hpad : runShortcut^[(a+s)+p*m] n=c := by
      rw [Nat.add_comm (a+s) (p*m),Function.iterate_add_apply]
      exact hloop
    have hnew : shortcutMultiplier ((a+s)+p*m) n=A*M^m := by
      rw [shortcutMultiplier_add]
      change A*shortcutMultiplier (p*m) c=A*M^m
      rw [hmult]
    have hstrict : 2^(b+s)*shortcutMultiplier ((a+s)+p*m) n<
        2^((a+s)+p*m)*shortcutMultiplier (b+s) k := by
      have hpw : (2:ℕ)^((a+s)+p*m)=2^(a+s)*(2^p)^m := by rw [pow_add,pow_mul]
      rw [hnew,hpw]
      calc
        _ = M^m*(2^(b+s)*A) := by ring
        _ < (2^p)^m*(2^(a+s)*B) := hratio
        _ = _ := by dsimp [B]; ring
    have hclock : b+s<(a+s)+p*m := by
      have hm' : m≤p*m := Nat.le_mul_of_pos_left _ hp
      omega
    exact independent_lift_of_shortcut_multiplier_order n k ((a+s)+p*m) (b+s) hk hkn
      (Nat.ne_of_gt hclock) (hpad.trans hmeet) hstrict.le
  · rintro ⟨a,b,u,v,k,_,_,_,hk,hkn,hstride,hzero,hone⟩
    exact collatz_affine_merger_independent_clocks n a b u v _ k ⟨hk,hkn⟩ hstride rfl hzero hone

private theorem ordinary_repeat_gives_bounded_orbit (n a b : ℕ) (hab : a<b)
    (he : collatzStep^[a] n=collatzStep^[b] n) :
    ∃ H : ℕ, ∀ t : ℕ, collatzStep^[t] n≤H := by
  let p := b-a
  let x := collatzStep^[a] n
  have hp : 0<p := by dsimp [p]; omega
  have hret : collatzStep^[p] x=x := by
    change collatzStep^[p] (collatzStep^[a] n)=collatzStep^[a] n
    rw [←Function.iterate_add_apply,show p+a=b by dsimp [p]; omega]
    exact he.symm
  have hloop (q : ℕ) : collatzStep^[p*q] x=x := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ,Function.iterate_add_apply,hret,ih]
  refine ⟨(Finset.range b).sup (fun j => collatzStep^[j] n),?_⟩
  intro t
  by_cases ht : t<a
  · exact Finset.le_sup (f:=fun j => collatzStep^[j] n) (Finset.mem_range.mpr (by omega))
  · let r := (t-a)%p
    let q := (t-a)/p
    have hdiv : r+p*q=t-a := Nat.mod_add_div _ _
    have hr : r<p := Nat.mod_lt _ hp
    have heq : collatzStep^[t] n=collatzStep^[r+a] n := by
      calc
        _ = collatzStep^[r] (collatzStep^[p*q] x) := by
          rw [←Function.iterate_add_apply]
          change collatzStep^[t] n=collatzStep^[r+p*q] (collatzStep^[a] n)
          rw [←Function.iterate_add_apply,show r+p*q+a=t by omega]
        _ = collatzStep^[r+a] n := by rw [hloop,Function.iterate_add_apply]
    rw [heq]
    exact Finset.le_sup (f:=fun j => collatzStep^[j] n)
      (Finset.mem_range.mpr (by dsimp [p] at hr; omega))

/-- Once independent-clock affine lifts are excluded, any smaller
merger would have to lie in an orbit that eventually exceeds every
fixed height. -/
private theorem collatz_merger_without_independent_lift_escapes (n : ℕ)
    (hno : ¬collatzIndependentLift n)
    (hmerge : ∃ k i j : ℕ, 0<k ∧ k<n ∧ collatzStep^[i] n=collatzStep^[j] k) :
    ∀ H : ℕ, ∃ T : ℕ, ∀ t : ℕ, T≤t → H<collatzStep^[t] n := by
  have hinj : Function.Injective (fun t : ℕ => collatzStep^[t] n) := by
    intro a b he
    by_contra! hne
    have hbound : ∃ M : ℕ, ∀ t : ℕ, collatzStep^[t] n≤M := by
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact ordinary_repeat_gives_bounded_orbit n a b hab he
      · exact ordinary_repeat_gives_bounded_orbit n b a hba he.symm
    obtain ⟨M,hM⟩ := hbound
    exact hno ((collatz_bounded_ordinary_merger_iff_independent_lift n M hM).mp hmerge)
  intro H
  let bad : Set ℕ := {t | collatzStep^[t] n≤H}
  let value := fun t : ℕ => collatzStep^[t] n
  have hsmall : (value '' bad).Finite := by
    apply (Set.finite_range (fun x : Fin (H+1) => x.val)).subset
    rintro _ ⟨t,ht,rfl⟩
    have hv : value t≤H := ht
    exact ⟨⟨value t,by omega⟩,rfl⟩
  obtain ⟨M,hM⟩ := (hsmall.of_finite_image hinj.injOn).bddAbove
  refine ⟨M+1,?_⟩
  intro t ht
  by_contra! h
  have hs : t≤M := hM (show t∈bad from h)
  omega

theorem solution (n : ℕ) :
    let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let lift := ∃ a b u v s : ℕ, 0<u ∧ 0<v ∧ a≠b ∧
      let P := 2^a*u
      let Q := 2^b*v
      let r := n%P
      0<s ∧ s<r ∧ Q≤P ∧ S^[a] r=S^[b] s ∧ S^[a] (P+r)=S^[b] (Q+s)
    let merger := ∃ k i j : ℕ, 0<k ∧ k<n ∧ collatzStep^[i] n=collatzStep^[j] k
    (∀ H : ℕ, (∀ t : ℕ, collatzStep^[t] n≤H) → (merger ↔ lift)) ∧
    (merger → lift ∨ (∀ H : ℕ, ∃ T : ℕ, ∀ t : ℕ, T≤t → H<collatzStep^[t] n)) := by
  dsimp only
  constructor
  · intro H hbound
    exact collatz_bounded_ordinary_merger_iff_independent_lift n H hbound
  · intro hmerge
    by_cases h : collatzIndependentLift n
    · exact Or.inl h
    · exact Or.inr (collatz_merger_without_independent_lift_escapes n h hmerge)
