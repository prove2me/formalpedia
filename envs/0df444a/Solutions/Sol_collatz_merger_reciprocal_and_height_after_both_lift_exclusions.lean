-- Prove2me | solution 1 for collatz_merger_reciprocal_and_height_after_both_lift_exclusions
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:10:09.731482+00:00
-- url     : https://prove2.me/submissions/75783f74-8cff-4e9e-8945-e64c7751374d

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
private theorem stepEven (n : ℕ) (h : n % 2 = 0) : collatzStep n = n / 2 := by
  rw [collatzStep, if_pos (Nat.even_iff.mpr h)]

private theorem stepOdd (n : ℕ) (h : n % 2 = 1) : collatzStep n = 3*n+1 := by
  rw [collatzStep, if_neg (by rw [Nat.even_iff, h]; decide)]


private def runShortcut (x : ℕ) : ℕ :=
  if x%2=0 then x/2 else (3*x+1)/2


/-- At an ordinary clock the visitor is either at a shortcut endpoint
or one step before the next endpoint. -/
private theorem ordinary_iterate_shortcut_cases (t x : ℕ) :
    ∃ d : ℕ, d≤t ∧ (collatzStep^[t] x=runShortcut^[d] x ∨
      ((runShortcut^[d] x)%2=1 ∧
        collatzStep^[t] x=collatzStep (runShortcut^[d] x))) := by
  induction t with
  | zero => exact ⟨0,Nat.le_refl _,Or.inl rfl⟩
  | succ t ih =>
    rcases ih with ⟨d,hdt,hd | ⟨ho,hd⟩⟩
    · by_cases he : (runShortcut^[d] x)%2=0
      · refine ⟨d+1,by omega,Or.inl ?_⟩
        rw [Function.iterate_succ_apply',hd,stepEven _ he,Function.iterate_succ_apply',
          runShortcut,if_pos he]
      · exact ⟨d,by omega,Or.inr ⟨by omega,by rw [Function.iterate_succ_apply',hd]⟩⟩
    · have he : (collatzStep (runShortcut^[d] x))%2=0 := by
        rw [stepOdd _ ho]
        omega
      refine ⟨d+1,by omega,Or.inl ?_⟩
      rw [Function.iterate_succ_apply',hd,stepEven _ he,stepOdd _ ho,
        Function.iterate_succ_apply',runShortcut,if_neg (by omega)]


private theorem shortcut_preimage_cases {a b : ℕ} (h : runShortcut a=b) :
    a=2*b ∨ (b%3=2 ∧ 3*a+1=2*b) := by
  by_cases he : a%2=0
  · rw [runShortcut,if_pos he] at h
    exact Or.inl (by omega)
  · rw [runShortcut,if_neg he] at h
    have hmul : 3*a+1=2*b := by omega
    exact Or.inr ⟨by omega,hmul⟩


private theorem shortcut_multiple_three_min (t a b : ℕ) (hm : b%3=0)
    (h : runShortcut^[t] a=b) : b≤a := by
  induction t generalizing b with
  | zero => exact le_of_eq h.symm
  | succ t ih =>
    rw [Function.iterate_succ_apply'] at h
    rcases shortcut_preimage_cases h with hdouble | ⟨hnot,_⟩
    · have hx : (runShortcut^[t] a)%3=0 := by omega
      exact (by omega : b≤runShortcut^[t] a).trans (ih _ hx rfl)
    · omega


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


private def shortcutOddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t+1, x => (if x%2=0 then 0 else 1)+shortcutOddCount t (runShortcut x)

private theorem shortcutMultiplier_eq_pow_three (t x : ℕ) :
    shortcutMultiplier t x=3^shortcutOddCount t x := by
  induction t generalizing x with
  | zero => simp [shortcutMultiplier,collatzShortcutAffinePair,shortcutOddCount]
  | succ t ih =>
    have he := ih (runShortcut x)
    simp only [shortcutMultiplier,collatzShortcutAffinePair,shortcutOddCount]
    change (if x%2=0 then shortcutMultiplier t (runShortcut x)
      else 3*shortcutMultiplier t (runShortcut x)) =
      3^((if x%2=0 then 0 else 1)+shortcutOddCount t (runShortcut x))
    rw [he]
    by_cases h : x%2=0 <;> simp [h,pow_add]


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


/-- The two lifts may use different binary widths and different positive
multipliers. Equal images at parameters zero and one fix both affine
image functions. -/
theorem collatz_shortcut_affine_merger_independent_clocks
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
theorem collatz_affine_merger_independent_clocks (n a b u v r s : ℕ)
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
theorem collatz_bounded_ordinary_merger_iff_independent_lift (n H : ℕ)
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


private theorem repeat_gives_bounded_orbit (f : ℕ → ℕ) (n a b : ℕ) (hab : a<b)
    (he : f^[a] n=f^[b] n) : ∃ H : ℕ, ∀ t : ℕ, f^[t] n≤H := by
  let p := b-a
  let x := f^[a] n
  have hp : 0<p := by dsimp [p]; omega
  have hret : f^[p] x=x := by
    change f^[p] (f^[a] n)=f^[a] n
    rw [←Function.iterate_add_apply,show p+a=b by dsimp [p]; omega]
    exact he.symm
  have hloop (q : ℕ) : f^[p*q] x=x := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ,Function.iterate_add_apply,hret,ih]
  refine ⟨(Finset.range b).sup (fun j => f^[j] n),?_⟩
  intro t
  by_cases ht : t<a
  · exact Finset.le_sup (f:=fun j => f^[j] n) (Finset.mem_range.mpr (by omega))
  · let r := (t-a)%p
    let q := (t-a)/p
    have hdiv : r+p*q=t-a := Nat.mod_add_div _ _
    have hr : r<p := Nat.mod_lt _ hp
    have heq : f^[t] n=f^[r+a] n := by
      calc
        _ = f^[r] (f^[p*q] x) := by
          rw [←Function.iterate_add_apply]
          change f^[t] n=f^[r+p*q] (f^[a] n)
          rw [←Function.iterate_add_apply,show r+p*q+a=t by omega]
        _ = f^[r+a] n := by rw [hloop,Function.iterate_add_apply]
    rw [heq]
    exact Finset.le_sup (f:=fun j => f^[j] n)
      (Finset.mem_range.mpr (by dsimp [p] at hr; omega))

/-- Once independent-clock affine lifts are excluded, any smaller
merger would have to lie in an orbit that eventually exceeds every
fixed height. -/
theorem collatz_merger_without_independent_lift_escapes (n : ℕ)
    (hno : ¬collatzIndependentLift n)
    (hmerge : ∃ k i j : ℕ, 0<k ∧ k<n ∧ collatzStep^[i] n=collatzStep^[j] k) :
    ∀ H : ℕ, ∃ T : ℕ, ∀ t : ℕ, T≤t → H<collatzStep^[t] n := by
  have hinj : Function.Injective (fun t : ℕ => collatzStep^[t] n) := by
    intro a b he
    by_contra! hne
    have hbound : ∃ M : ℕ, ∀ t : ℕ, collatzStep^[t] n≤M := by
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact repeat_gives_bounded_orbit collatzStep n a b hab he
      · exact repeat_gives_bounded_orbit collatzStep n b a hba he.symm
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



private def collatzEqualClockLift (n : ℕ) : Prop :=
  ∃ d m : ℕ, 0<d ∧ d<n ∧
    let r := n%2^m
    d≤r ∧ runShortcut^[m] r=runShortcut^[m] (r-d) ∧
      runShortcut^[m] (2^m+r)=runShortcut^[m] (2^m+r-d)

private theorem equal_clock_lift_of_equal_multiplier (n k a : ℕ)
    (hk : 0<k) (hkn : k<n) (hmeet : runShortcut^[a] n=runShortcut^[a] k)
    (hA : shortcutMultiplier a n=shortcutMultiplier a k) : collatzEqualClockLift n := by
  let m := n+a
  have hpow : n<2^m := (show n<2^n from Nat.lt_two_pow_self).trans_le
    (Nat.pow_le_pow_right (by decide) (by dsimp [m]; omega))
  have hm : runShortcut^[m] n=runShortcut^[m] k := by
    dsimp [m]
    rw [Function.iterate_add_apply,Function.iterate_add_apply,hmeet]
  have hcoeff : shortcutMultiplier m n=shortcutMultiplier m k := by
    dsimp [m]
    rw [Nat.add_comm n a,shortcutMultiplier_add,shortcutMultiplier_add,hA,hmeet]
  have ho : runShortcut^[m] (2^m+n)=runShortcut^[m] (2^m+k) := by
    have hzeroN : runShortcut^[m] n=(collatzShortcutAffinePair m n).2 := by
      simpa using collatzShortcutAffinePair_sound m 0 n
    have hzeroK : runShortcut^[m] k=(collatzShortcutAffinePair m k).2 := by
      simpa using collatzShortcutAffinePair_sound m 0 k
    have hconst := hzeroN.symm.trans (hm.trans hzeroK)
    have hp (x : ℕ) : runShortcut^[m] (2^m+x)=shortcutMultiplier m x+(collatzShortcutAffinePair m x).2 := by
      simpa using collatzShortcutAffinePair_sound m 1 x
    rw [hp,hp,hcoeff,hconst]
  refine ⟨n-k,m,by omega,by omega,?_⟩
  dsimp only
  rw [Nat.mod_eq_of_lt hpow,show n-(n-k)=k by omega,show 2^m+n-(n-k)=2^m+k by omega]
  exact ⟨by omega,hm,ho⟩

private theorem shortcut_path_upper_at_floor (N t x : ℕ)
    (hfloor : ∀ i : ℕ, i≤t → N≤runShortcut^[i] x) :
    2^t*(N^shortcutOddCount t x*runShortcut^[t] x)≤(3*N+1)^shortcutOddCount t x*x := by
  induction t generalizing x with
  | zero => simp [shortcutOddCount]
  | succ t ih =>
    let y := runShortcut x
    let z := runShortcut^[t] y
    let o := shortcutOddCount t y
    have htail : ∀ i : ℕ, i≤t → N≤runShortcut^[i] y := by
      intro i hi
      rw [←Function.iterate_succ_apply]
      exact hfloor (i+1) (by omega)
    have hp := ih y htail
    change 2^t*(N^o*z)≤(3*N+1)^o*y at hp
    simp only [shortcutOddCount,Function.iterate_succ_apply]
    by_cases hx : x%2=0
    · rw [if_pos hx,zero_add]
      change 2^(t+1)*(N^o*z)≤(3*N+1)^o*x
      have he : x=2*y := by dsimp [y]; rw [runShortcut,if_pos hx]; omega
      calc
        _ = 2*(2^t*(N^o*z)) := by rw [pow_succ]; ring
        _ ≤ 2*((3*N+1)^o*y) := Nat.mul_le_mul_left _ hp
        _ = _ := by rw [he]; ring
    · rw [if_neg hx]
      change 2^(t+1)*(N^(1+o)*z)≤(3*N+1)^(1+o)*x
      have he : 2*y=3*x+1 := by dsimp [y]; rw [runShortcut,if_neg hx]; omega
      have hNx : N≤x := hfloor 0 (Nat.zero_le _)
      have hstep : N*(2*y)≤(3*N+1)*x := by
        rw [he]
        calc
          N*(3*x+1) = 3*N*x+N := by ring
          _ ≤ 3*N*x+x := Nat.add_le_add_left hNx _
          _ = (3*N+1)*x := by ring
      calc
        _ = (2*N)*(2^t*(N^o*z)) := by rw [pow_succ,pow_add,pow_one]; ring
        _ ≤ (2*N)*((3*N+1)^o*y) := Nat.mul_le_mul_left _ hp
        _ = (3*N+1)^o*(N*(2*y)) := by ring
        _ ≤ (3*N+1)^o*((3*N+1)*x) := Nat.mul_le_mul_left _ hstep
        _ = _ := by rw [pow_add,pow_one]; ring

private theorem reciprocal_bernoulli_nat (c o : ℕ) (ho : o≤c) :
    (c-o)*(c+1)^o≤c^(o+1) := by
  induction o with
  | zero => simp
  | succ o ih =>
    let d := c-o.succ
    have hd : d≤c := Nat.sub_le _ _
    have he : c-o=d+1 := by dsimp [d]; omega
    have hstep : (c-o.succ)*(c+1)≤(c-o)*c := calc
      _ = d*c+d := by dsimp [d]; ring
      _ ≤ d*c+c := Nat.add_le_add_left hd _
      _ = _ := by rw [he]; ring
    calc
      _ = ((c-o.succ)*(c+1))*(c+1)^o := by simp only [pow_succ]; ring
      _ ≤ ((c-o)*c)*(c+1)^o := Nat.mul_le_mul_right _ hstep
      _ = c*((c-o)*(c+1)^o) := by ring
      _ ≤ c*c^(o+1) := Nat.mul_le_mul_left _ (ih (by omega))
      _ = c^(o.succ+1) := by simp only [Nat.succ_eq_add_one]; rw [pow_succ c (o+1)]; ring

private theorem shortcut_small_odd_count_growth_bound (n t : ℕ) (hn : 0<n)
    (hfloor : ∀ i : ℕ, n≤runShortcut^[i] n) (ho : shortcutOddCount t n≤n) :
    2*(2^t*runShortcut^[t] n)≤3*shortcutMultiplier t n*n := by
  let o := shortcutOddCount t n
  have ha : shortcutMultiplier t n=3^o := shortcutMultiplier_eq_pow_three t n
  have hb := reciprocal_bernoulli_nat (3*n) o (by omega)
  have hcorrection_scaled : (2*(3*n+1)^o)*n≤(3*(3*n)^o)*n := calc
    _ = (2*n)*(3*n+1)^o := by ring
    _ ≤ (3*n-o)*(3*n+1)^o := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (3*n)^(o+1) := hb
    _ = _ := by rw [pow_succ]; ring
  have hcorrect := Nat.le_of_mul_le_mul_right hcorrection_scaled hn
  have hup : 2^t*(n^o*runShortcut^[t] n)≤(3*n+1)^o*n :=
    shortcut_path_upper_at_floor n t n (fun i _ => hfloor i)
  apply Nat.le_of_mul_le_mul_right _ (Nat.pow_pos (n:=o) hn)
  calc
    _ = 2*(2^t*(n^o*runShortcut^[t] n)) := by ring
    _ ≤ 2*((3*n+1)^o*n) := Nat.mul_le_mul_left _ hup
    _ = (2*(3*n+1)^o)*n := by ring
    _ ≤ (3*(3*n)^o)*n := Nat.mul_le_mul_right _ hcorrect
    _ = _ := by rw [mul_pow,ha]; ring

/-- On the branch excluding both known affine lift tests, an unfavorable
comparison of normalized multipliers forces an equal-clock, long merger
from an odd visitor very close to the original start. -/
theorem collatz_no_lifts_merger_gain_constraint (n k a b : ℕ)
    (hn : 3≤n) (hstay : ∀ t : ℕ, n≤collatzStep^[t] n)
    (hnoEqual : ¬collatzEqualClockLift n) (hnoIndependent : ¬collatzIndependentLift n)
    (hk : 0<k) (hkn : k<n) (hmeet : runShortcut^[a] n=runShortcut^[b] k) :
    2^a*shortcutMultiplier b k<2^b*shortcutMultiplier a n ∨
      (a=b ∧ k%2=1 ∧ 2*n≤3*k+1 ∧ n<shortcutOddCount a n) := by
  by_cases h : 2^a*shortcutMultiplier b k<2^b*shortcutMultiplier a n
  · exact Or.inl h
  have hord : 2^b*shortcutMultiplier a n≤2^a*shortcutMultiplier b k := by omega
  have hab : a=b := by
    by_contra hne
    exact hnoIndependent (independent_lift_of_shortcut_multiplier_order n k a b hk hkn hne hmeet hord)
  subst b
  let A := shortcutMultiplier a n
  let B := shortcutMultiplier a k
  have hA : 0<A := shortcutMultiplier_pos a n
  have hAB : A≤B := Nat.le_of_mul_le_mul_left hord (Nat.two_pow_pos _)
  have hneq : A≠B := by
    intro heq
    exact hnoEqual (equal_clock_lift_of_equal_multiplier n k a hk hkn hmeet heq)
  have hpower : shortcutOddCount a n<shortcutOddCount a k := by
    by_contra! he
    have hback := Nat.pow_le_pow_right (by decide : 0<(3:ℕ)) he
    rw [←shortcutMultiplier_eq_pow_three a n,←shortcutMultiplier_eq_pow_three a k] at hback
    change B≤A at hback
    omega
  have htriple : 3*A≤B := by
    have hle := Nat.pow_le_pow_right (by decide : 0<(3:ℕ))
      (show shortcutOddCount a n+1≤shortcutOddCount a k by omega)
    rw [pow_succ,←shortcutMultiplier_eq_pow_three a n,←shortcutMultiplier_eq_pow_three a k] at hle
    omega
  have hfront : n≤runShortcut k := by
    by_contra! hsmall
    have ha0 : a≠0 := by
      intro he
      rw [he] at hmeet
      change n=k at hmeet
      omega
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero ha0
    have hshift : runShortcut^[a] n=runShortcut^[t] (runShortcut k) := by
      rw [hmeet,ht,Function.iterate_succ_apply]
    have hnext : 0<runShortcut k := by unfold runShortcut; split <;> omega
    have hsplit : B=if k%2=0 then shortcutMultiplier t (runShortcut k)
        else 3*shortcutMultiplier t (runShortcut k) := by
      dsimp [B]
      rw [ht]
      rfl
    have hgain : A≤shortcutMultiplier t (runShortcut k) := by
      split at hsplit <;> omega
    have horder : 2^t*A≤2^a*shortcutMultiplier t (runShortcut k) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by omega)) hgain
    exact hnoIndependent (independent_lift_of_shortcut_multiplier_order n (runShortcut k) a t
      hnext hsmall (by omega) hshift horder)
  have ho : k%2=1 := by
    by_contra! h
    rw [runShortcut,if_pos (by omega : k%2=0)] at hfront
    omega
  have hclose : 2*n≤3*k+1 := by
    rw [runShortcut,if_neg (by omega : k%2≠0)] at hfront
    omega
  refine Or.inr ⟨rfl,ho,hclose,?_⟩
  by_contra! hodd
  have hstayS : ∀ t : ℕ, n≤runShortcut^[t] n := by
    intro t
    obtain ⟨i,hi⟩ := shortcutIterate_ordinary n t
    exact hi ▸ hstay i
  have hupper := shortcut_small_odd_count_growth_bound n a (by omega) hstayS hodd
  have hlower : (3*A)*k≤2^a*runShortcut^[a] n := calc
    _ ≤ B*k := Nat.mul_le_mul_right _ htriple
    _ ≤ _ := by rw [hmeet]; exact (shortcutMultiplier_lower a k).1
  have hmul : (2*k)*(3*A)≤n*(3*A) := calc
    _ = 2*((3*A)*k) := by ring
    _ ≤ 2*(2^a*runShortcut^[a] n) := Nat.mul_le_mul_left _ hlower
    _ ≤ 3*A*n := hupper
    _ = _ := by ring
  have hhalf : 2*k≤n := Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos (by decide) hA)
  omega



/-- The reciprocal correction at each odd shortcut departure. -/
private def shortcutReciprocalSum : ℕ → ℕ → ℚ
  | 0, _ => 0
  | t+1, x => (if x%2=0 then 0 else (3*(x:ℚ)+1)⁻¹) +
      shortcutReciprocalSum t (runShortcut x)

private theorem shortcut_reciprocal_sum_nonnegative (t x : ℕ) :
    0≤shortcutReciprocalSum t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    rw [shortcutReciprocalSum]
    apply add_nonneg _ (ih (runShortcut x))
    split
    · exact le_refl _
    · exact inv_nonneg.mpr (by positivity)

/-- The accumulated reciprocal correction bounds the departure from the
multiplicative approximation, even at variable clocks. -/
private theorem shortcut_reciprocal_correction (t x : ℕ) :
    (1-shortcutReciprocalSum t x)*((2:ℚ)^t*(runShortcut^[t] x:ℕ))≤
      (shortcutMultiplier t x:ℚ)*x := by
  induction t generalizing x with
  | zero => simp [shortcutReciprocalSum,shortcutMultiplier,collatzShortcutAffinePair]
  | succ t ih =>
    let y := runShortcut x
    let z := runShortcut^[t] y
    let R := shortcutReciprocalSum t y
    let A := shortcutMultiplier t y
    let W : ℚ := 2^t*(z:ℚ)
    have htail : (1-R)*W≤(A:ℚ)*y := ih y
    have hR : 0≤R := shortcut_reciprocal_sum_nonnegative t y
    have hW : 0≤W := by dsimp [W]; positivity
    rw [Function.iterate_succ_apply,shortcutReciprocalSum]
    change (1-((if x%2=0 then 0 else (3*(x:ℚ)+1)⁻¹)+R))*((2:ℚ)^(t+1)*(z:ℚ))≤
      ((if x%2=0 then A else 3*A : ℕ):ℚ)*x
    have hp : (2:ℚ)^(t+1)*(z:ℚ)=2*W := by dsimp [W]; rw [pow_succ]; ring
    rw [hp]
    by_cases hx : x%2=0
    · rw [if_pos hx,if_pos hx,zero_add]
      have he : x=2*y := by dsimp [y]; rw [runShortcut,if_pos hx]; omega
      have hcast : (x:ℚ)=2*(y:ℚ) := by exact_mod_cast he
      rw [hcast]
      linarith [mul_le_mul_of_nonneg_left htail (show (0:ℚ)≤2 by decide)]
    · rw [if_neg hx,if_neg hx,Nat.cast_mul,Nat.cast_ofNat]
      let C : ℚ := 3*(x:ℚ)+1
      have hC : 0<C := by dsimp [C]; positivity
      have he : 2*y=3*x+1 := by dsimp [y]; rw [runShortcut,if_neg hx]; omega
      have hcast : 2*(y:ℚ)=C := by dsimp [C]; exact_mod_cast he
      have hc : 0≤1-C⁻¹ := by
        have : 1≤C := by dsimp [C]; linarith [show (0:ℚ)≤3*(x:ℚ) by positivity]
        have hi : C⁻¹≤1 := inv_le_one_of_one_le₀ this
        linarith
      change (1-(C⁻¹+R))*(2*W)≤3*(A:ℚ)*x
      calc
        _ ≤ ((1-C⁻¹)*(1-R))*(2*W) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hprod := mul_nonneg (inv_nonneg.mpr hC.le) hR
          linarith only [show (1-C⁻¹)*(1-R)-(1-(C⁻¹+R))=C⁻¹*R by ring,hprod]
        _ = (1-C⁻¹)*(2*((1-R)*W)) := by ring
        _ ≤ (1-C⁻¹)*(2*((A:ℚ)*y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail (by positivity)) hc
        _ = (A:ℚ)*((1-C⁻¹)*C) := by rw [←hcast]; ring
        _ = _ := by
          have hh : (1-C⁻¹)*C=C-1 := by field_simp
          rw [hh]
          dsimp [C]
          ring

/-- A merger surviving both lifting exclusions has a positive cumulative
reciprocal threshold on one of its two paths. -/
theorem collatz_no_lifts_merger_reciprocal_constraint (n k a b : ℕ)
    (hn : 3≤n) (hstay : ∀ t : ℕ, n≤collatzStep^[t] n)
    (hnoEqual : ¬collatzEqualClockLift n) (hnoIndependent : ¬collatzIndependentLift n)
    (hk : 0<k) (hkn : k<n) (hmeet : runShortcut^[a] n=runShortcut^[b] k) :
    (2^a*shortcutMultiplier b k<2^b*shortcutMultiplier a n ∧
      1-(k:ℚ)/n<shortcutReciprocalSum b k) ∨
    (a=b ∧ k%2=1 ∧ 2*n≤3*k+1 ∧
      1-(n:ℚ)/(3*k)≤shortcutReciprocalSum a n) := by
  have hA : 0<(shortcutMultiplier a n:ℚ) := by
    exact_mod_cast shortcutMultiplier_pos a n
  let y := runShortcut^[a] n
  have hny : n≤y := by
    obtain ⟨t,ht⟩ := shortcutIterate_ordinary n a
    change n≤runShortcut^[a] n
    rw [←ht]
    exact hstay t
  have hy : 0<(y:ℚ) := by exact_mod_cast (show 0<y by omega)
  have hnq : 0<(n:ℚ) := by exact_mod_cast (show 0<n by omega)
  have hkq : 0<(k:ℚ) := by exact_mod_cast hk
  have hlN : (shortcutMultiplier a n:ℚ)*n≤2^a*(y:ℚ) := by
    exact_mod_cast (shortcutMultiplier_lower a n).1
  have hRN : (1-shortcutReciprocalSum a n)*(2^a*(y:ℚ))≤(shortcutMultiplier a n:ℚ)*n :=
    shortcut_reciprocal_correction a n
  have hRK : (1-shortcutReciprocalSum b k)*(2^b*(y:ℚ))≤(shortcutMultiplier b k:ℚ)*k := by
    dsimp [y]
    rw [hmeet]
    exact shortcut_reciprocal_correction b k
  by_cases horder : 2^a*shortcutMultiplier b k<2^b*shortcutMultiplier a n
  · refine Or.inl ⟨horder,?_⟩
    have horderQ : (2:ℚ)^a*(shortcutMultiplier b k:ℚ)<
        (2:ℚ)^b*(shortcutMultiplier a n:ℚ) := by exact_mod_cast horder
    have hratio : ((1-shortcutReciprocalSum b k)*(n:ℚ))*((2:ℚ)^a*(2^b*(y:ℚ)))<
        (k:ℚ)*((2:ℚ)^a*(2^b*(y:ℚ))) := calc
      _ = ((1-shortcutReciprocalSum b k)*(2^b*(y:ℚ)))*(2^a*(n:ℚ)) := by ring
      _ ≤ ((shortcutMultiplier b k:ℚ)*k)*(2^a*(n:ℚ)) :=
        mul_le_mul_of_nonneg_right hRK (by positivity)
      _ = ((2:ℚ)^a*(shortcutMultiplier b k:ℚ))*((n:ℚ)*k) := by ring
      _ < ((2:ℚ)^b*(shortcutMultiplier a n:ℚ))*((n:ℚ)*k) :=
        mul_lt_mul_of_pos_right horderQ (by positivity)
      _ = ((shortcutMultiplier a n:ℚ)*n)*(2^b*(k:ℚ)) := by ring
      _ ≤ (2^a*(y:ℚ))*(2^b*(k:ℚ)) := mul_le_mul_of_nonneg_right hlN (by positivity)
      _ = _ := by ring
    have hshort := lt_of_mul_lt_mul_right hratio (by positivity)
    have hd := (lt_div_iff₀ hnq).mpr hshort
    linarith
  · obtain ⟨heq,hodd,hclose,_⟩ :=
      (collatz_no_lifts_merger_gain_constraint n k a b hn hstay
        hnoEqual hnoIndependent hk hkn hmeet).resolve_left horder
    refine Or.inr ⟨heq,hodd,hclose,?_⟩
    have hord : 3*shortcutMultiplier a n≤shortcutMultiplier b k := by
      by_contra! hlt
      have hne : shortcutMultiplier a n≠shortcutMultiplier b k := by
        intro he
        subst b
        exact hnoEqual (equal_clock_lift_of_equal_multiplier n k a hk hkn hmeet he)
      have hstrict : shortcutMultiplier a n<shortcutMultiplier b k := by
        by_contra! hle
        have hreverse : shortcutMultiplier b k<shortcutMultiplier a n := by omega
        have hab : 2^a*shortcutMultiplier b k<2^b*shortcutMultiplier a n := calc
          _ < 2^a*shortcutMultiplier a n :=
            Nat.mul_lt_mul_of_pos_left hreverse (Nat.two_pow_pos _)
          _ = _ := congrArg (fun t => 2^t*shortcutMultiplier a n) heq
        exact horder hab
      have ho : shortcutOddCount a n<shortcutOddCount b k := by
        by_contra! h
        have h' := Nat.pow_le_pow_right (by decide : 0<(3:ℕ)) h
        rw [←shortcutMultiplier_eq_pow_three,←shortcutMultiplier_eq_pow_three] at h'
        omega
      have hle := Nat.pow_le_pow_right (by decide : 0<(3:ℕ))
        (show shortcutOddCount a n+1≤shortcutOddCount b k by omega)
      rw [pow_succ,←shortcutMultiplier_eq_pow_three,←shortcutMultiplier_eq_pow_three] at hle
      omega
    have hordQ : 3*(shortcutMultiplier a n:ℚ)≤(shortcutMultiplier b k:ℚ) := by exact_mod_cast hord
    have hlK : (shortcutMultiplier b k:ℚ)*k≤2^b*(y:ℚ) := by
      dsimp [y]
      rw [hmeet]
      exact_mod_cast (shortcutMultiplier_lower b k).1
    have hmul : ((1-shortcutReciprocalSum a n)*(3*(k:ℚ)))*(shortcutMultiplier a n:ℚ)≤
        (n:ℚ)*(shortcutMultiplier a n:ℚ) := by
      by_cases hsign : 0≤1-shortcutReciprocalSum a n
      · calc
          _ = (1-shortcutReciprocalSum a n)*((3*(shortcutMultiplier a n:ℚ))*k) := by ring
          _ ≤ (1-shortcutReciprocalSum a n)*((shortcutMultiplier b k:ℚ)*k) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hordQ hkq.le) hsign
          _ ≤ (1-shortcutReciprocalSum a n)*(2^b*(y:ℚ)) :=
            mul_le_mul_of_nonneg_left hlK hsign
          _ = (1-shortcutReciprocalSum a n)*(2^a*(y:ℚ)) := by rw [heq]
          _ ≤ _ := by simpa [mul_comm] using hRN
      · exact (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) hA.le).trans
          (by positivity)
    have hshort := le_of_mul_le_mul_right hmul hA
    have hd := (le_div_iff₀ (show 0<3*(k:ℚ) by positivity)).mpr hshort
    linarith

open scoped BigOperators in
private theorem shortcut_reciprocal_sum_eq_range (t x : ℕ) :
    shortcutReciprocalSum t x=∑ i ∈ Finset.range t,
      if (runShortcut^[i] x)%2=0 then 0 else (3*(runShortcut^[i] x:ℕ)+1 : ℚ)⁻¹ := by
  induction t generalizing x with
  | zero => simp [shortcutReciprocalSum]
  | succ t ih =>
    rw [shortcutReciprocalSum,ih,Finset.sum_range_succ',Function.iterate_zero_apply]
    simp only [Function.iterate_succ_apply]
    exact add_comm _ _

private theorem shortcut_no_multiple_three_after_odd (n i : ℕ) (hodd : n%2=1) (hi : 0<i) :
    (runShortcut^[i] n)%3≠0 := by
  cases i with
  | zero => omega
  | succ i =>
    induction i with
    | zero =>
      rw [Function.iterate_one,runShortcut,if_neg (by omega)]
      omega
    | succ i ih =>
      rw [Function.iterate_succ_apply',runShortcut]
      have hprev := ih (by omega)
      split <;> omega

open scoped BigOperators in
private theorem collatz_reciprocal_sum_one_bin (s : Finset ℕ) (N : ℕ) (hN : 1000≤N)
    (hs : ∀ x∈s, N≤x ∧ x<2*N ∧ (x%6=1 ∨ x%6=5)) :
    (∑ x ∈ s, (3*(x:ℚ)+1)⁻¹)≤3/25 := by
  let low := 2*(N/6)
  let width := 2*((2*N)/6)+2-low
  let code (x : ℕ) := 2*(x/6)+(if x%6=5 then 1 else 0)-low
  have hcard : s.card≤width := by
    rw [←Finset.card_range width]
    apply Finset.card_le_card_of_injOn code
    · intro x hx
      change x∈s at hx
      have h := hs x hx
      change code x∈Finset.range width
      rw [Finset.mem_range]
      dsimp [code,width,low]
      split <;> omega
    · intro x hx y hy he
      change x∈s at hx
      change y∈s at hy
      obtain ⟨hxN,_,hx6⟩ := hs x hx
      obtain ⟨hyN,_,hy6⟩ := hs y hy
      dsimp [code,low] at he
      rcases hx6 with hx6|hx6 <;> rcases hy6 with hy6|hy6 <;> simp [hx6,hy6] at he <;> omega
  have hbound : 3*s.card≤N+12 := by dsimp [width,low] at hcard; omega
  have hcast : (3:ℚ)*s.card≤(N:ℚ)+12 := by exact_mod_cast hbound
  have hNq : (1000:ℚ)≤N := by exact_mod_cast hN
  calc
    _ ≤ (s.card:ℚ)*(3*(N:ℚ)+1)⁻¹ := by
      rw [←nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ ?_
      intro x hx
      apply inv_anti₀ (by positivity)
      have hX : (N:ℚ)≤x := by exact_mod_cast (hs x hx).1
      linarith
    _ = (s.card:ℚ)/(3*(N:ℚ)+1) := by rw [div_eq_mul_inv]
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr (by linarith)

open scoped BigOperators in
private theorem collatz_reciprocal_sum_dyadic_bins (d n : ℕ) (s : Finset ℕ) (hn : 1000≤n)
    (hs : ∀ x∈s, n≤x ∧ x<2^d*n ∧ (x%6=1 ∨ x%6=5)) :
    (∑ x ∈ s, (3*(x:ℚ)+1)⁻¹)≤(d:ℚ)*(3/25) := by
  induction d generalizing s with
  | zero =>
    have he : s=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := hs x hx
      simp only [pow_zero,one_mul] at h
      omega
    simp [he]
  | succ d ih =>
    let N := 2^d*n
    have hN : 1000≤N := hn.trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
    have hupper : 2^(d+1)*n=2*N := by dsimp [N]; rw [pow_succ]; ring
    have hfirst := ih (s.filter fun x => x<N) (by
      intro x hx
      obtain ⟨hm,hlt⟩ := Finset.mem_filter.mp hx
      exact ⟨(hs x hm).1,hlt,(hs x hm).2.2⟩)
    have hsecond := collatz_reciprocal_sum_one_bin (s.filter fun x => ¬ x<N) N hN (by
      intro x hx
      obtain ⟨hm,hge⟩ := Finset.mem_filter.mp hx
      have hh := hs x hm
      rw [hupper] at hh
      exact ⟨by omega,hh.2.1,hh.2.2⟩)
    have hsplit := Finset.sum_filter_add_sum_filter_not (s:=s)
      (p:=fun x => x<N) (f:=fun x => (3*(x:ℚ)+1)⁻¹)
    rw [Nat.cast_succ]
    linarith

private theorem shortcut_merger_no_repeat_without_independent_lift (n k a b : ℕ)
    (hno : ¬collatzIndependentLift n) (hk : 0<k) (hkn : k<n)
    (hmeet : runShortcut^[a] n=runShortcut^[b] k) :
    Function.Injective (fun i : ℕ => runShortcut^[i] n) := by
  intro i j he
  by_contra! hne
  have hb : ∃ H : ℕ, ∀ t : ℕ, runShortcut^[t] n≤H := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact repeat_gives_bounded_orbit runShortcut n i j hlt he
    · exact repeat_gives_bounded_orbit runShortcut n j i hgt he.symm
  obtain ⟨H,hH⟩ := hb
  have hC (t : ℕ) : collatzStep^[t] n≤3*H+1 := by
    rcases ordinary_iterate_shortcut_cases t n with ⟨d,_,hd | ⟨ho,hd⟩⟩
    · have := hH d
      rw [hd]
      omega
    · have := hH d
      rw [hd,stepOdd _ ho]
      omega
  obtain ⟨a',ha⟩ := shortcutIterate_ordinary n a
  obtain ⟨b',hb⟩ := shortcutIterate_ordinary k b
  exact hno ((collatz_bounded_ordinary_merger_iff_independent_lift n (3*H+1) hC).mp
    ⟨k,a',b',hk,hkn,ha.trans (hmeet.trans hb.symm)⟩)

open scoped BigOperators in
private theorem shortcut_reciprocal_sum_below_sixteen (n a : ℕ)
    (hn : 1000≤n) (hodd : n%2=1)
    (hfloor : ∀ i : ℕ, i<a → n≤runShortcut^[i] n)
    (hcap : ∀ i : ℕ, i<a → runShortcut^[i] n<16*n)
    (hinj : Function.Injective (fun i : ℕ => runShortcut^[i] n)) :
    shortcutReciprocalSum a n<49/100 := by
  cases a with
  | zero => change (0:ℚ)<49/100; norm_num
  | succ t =>
    let f (i : ℕ) := runShortcut^[i] (runShortcut n)
    let I := (Finset.range t).filter (fun i => (f i)%2≠0)
    let states := I.image f
    have hclock (i : ℕ) : f i=runShortcut^[i+1] n :=
      (Function.iterate_succ_apply runShortcut i n).symm
    have hs : ∀ x∈states, n≤x ∧ x<2^4*n ∧ (x%6=1 ∨ x%6=5) := by
      intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hm,hod⟩ := Finset.mem_filter.mp hi
      have hit := Finset.mem_range.mp hm
      rw [hclock] at hod ⊢
      have hlo := hfloor (i+1) (by omega)
      have hhi := hcap (i+1) (by omega)
      have hthree := shortcut_no_multiple_three_after_odd n (i+1) hodd (by omega)
      exact ⟨hlo,hhi,by omega⟩
    have hsum := collatz_reciprocal_sum_dyadic_bins 4 n states hn hs
    have himage : (∑ x ∈ states, (3*(x:ℚ)+1)⁻¹)=shortcutReciprocalSum t (runShortcut n) := by
      dsimp [states]
      rw [Finset.sum_image]
      · dsimp [I]
        rw [Finset.sum_filter,shortcut_reciprocal_sum_eq_range]
        apply Finset.sum_congr rfl
        intro i _
        by_cases he : (f i)%2=0 <;> simp [he,f]
      · intro i _ j _ he
        rw [hclock,hclock] at he
        have hf := hinj he
        omega
    rw [himage] at hsum
    have hinit : (3*(n:ℚ)+1)⁻¹≤(3001:ℚ)⁻¹ := by
      apply inv_anti₀ (by norm_num)
      have hN : (1000:ℚ)≤n := by exact_mod_cast hn
      linarith
    rw [shortcutReciprocalSum,if_neg (by omega)]
    norm_num at hsum hinit ⊢
    linarith

/-- For the exceptional equal-clock branch, a merger surviving both
lifting exclusions must attain at least sixteen times its original start. -/
theorem collatz_no_lifts_merger_reciprocal_or_sixteenfold (n k a b : ℕ)
    (hn : 1000≤n) (hodd : n%2=1) (hstay : ∀ t : ℕ, n≤collatzStep^[t] n)
    (hnoEqual : ¬collatzEqualClockLift n) (hnoIndependent : ¬collatzIndependentLift n)
    (hk : 0<k) (hkn : k<n) (hmeet : runShortcut^[a] n=runShortcut^[b] k) :
    (2^a*shortcutMultiplier b k<2^b*shortcutMultiplier a n ∧
      1-(k:ℚ)/n<shortcutReciprocalSum b k) ∨
    (a=b ∧ k%2=1 ∧ 2*n≤3*k+1 ∧ ∃ i<a, 16*n≤runShortcut^[i] n) := by
  rcases collatz_no_lifts_merger_reciprocal_constraint n k a b (by omega) hstay
      hnoEqual hnoIndependent hk hkn hmeet with h | ⟨heq,hko,hclose,hR⟩
  · exact Or.inl h
  · refine Or.inr ⟨heq,hko,hclose,?_⟩
    by_contra! hcap
    have hfloor (i : ℕ) (_ : i<a) : n≤runShortcut^[i] n := by
      obtain ⟨t,ht⟩ := shortcutIterate_ordinary n i
      exact ht ▸ hstay t
    have hinj := shortcut_merger_no_repeat_without_independent_lift n k a b
      hnoIndependent hk hkn hmeet
    have hu := shortcut_reciprocal_sum_below_sixteen n a hn hodd hfloor hcap hinj
    have hc : 2*(n:ℚ)≤3*(k:ℚ)+1 := by exact_mod_cast hclose
    have hN : (1000:ℚ)≤n := by exact_mod_cast hn
    have hq : (n:ℚ)/(3*(k:ℚ))≤51/100 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith



private theorem shortcutOddCount_eq_range (t x : ℕ) :
    shortcutOddCount t x=((List.range t).map (fun i => (runShortcut^[i] x)%2)).sum := by
  induction t generalizing x with
  | zero => simp [shortcutOddCount]
  | succ t ih =>
    have hp : (if x%2=0 then 0 else 1)=x%2 := by split <;> omega
    rw [shortcutOddCount,hp,ih,List.range_succ_eq_map]
    simp only [List.map_cons,List.sum_cons,List.map_map,Function.iterate_zero_apply]
    have he : (fun i : ℕ => (runShortcut^[i] (runShortcut x))%2)=
        (fun i => (runShortcut^[i] x)%2) ∘ Nat.succ := by
      funext i
      change (runShortcut^[i] (runShortcut x))%2=(runShortcut^[i.succ] x)%2
      rw [Function.iterate_succ_apply]
    rw [he]

theorem solution (n k a b : ℕ) (hn : 1000 ≤ n) (hodd : n % 2 = 1)
    (hstay : ∀ t : ℕ, n ≤ collatzStep^[t] n) (hk : 0 < k) (hkn : k < n) :
    let S : ℕ → ℕ := fun x => if x % 2 = 0 then x / 2 else (3*x+1) / 2
    let odd : ℕ → ℕ → ℕ := fun t x => ((List.range t).map (fun i => (S^[i] x) % 2)).sum
    let R : ℕ → ℕ → ℚ := fun t x => (Finset.range t).sum fun i =>
      if (S^[i] x) % 2 = 0 then 0 else (3*(S^[i] x : ℕ)+1 : ℚ)⁻¹
    let equalLift := ∃ d m : ℕ, 0 < d ∧ d < n ∧
      let r := n % 2^m
      d ≤ r ∧ S^[m] r = S^[m] (r-d) ∧ S^[m] (2^m+r) = S^[m] (2^m+r-d)
    let independentLift := ∃ c d u v s : ℕ, 0 < u ∧ 0 < v ∧ c ≠ d ∧
      let P := 2^c*u
      let Q := 2^d*v
      let r := n % P
      0 < s ∧ s < r ∧ Q ≤ P ∧ S^[c] r = S^[d] s ∧ S^[c] (P+r) = S^[d] (Q+s)
    ¬equalLift → ¬independentLift → S^[a] n = S^[b] k →
      (2^a*3^odd b k < 2^b*3^odd a n ∧ 1-(k:ℚ)/n < R b k) ∨
      (a = b ∧ k % 2 = 1 ∧ 2*n ≤ 3*k+1 ∧ ∃ i < a, 16*n ≤ S^[i] n) := by
  dsimp only
  intro hEqual hIndependent hmeet
  have h := collatz_no_lifts_merger_reciprocal_or_sixteenfold n k a b
    hn hodd hstay hEqual hIndependent hk hkn hmeet
  simp only [shortcutMultiplier_eq_pow_three,shortcutOddCount_eq_range,
    shortcut_reciprocal_sum_eq_range] at h
  delta runShortcut at h
  exact h
