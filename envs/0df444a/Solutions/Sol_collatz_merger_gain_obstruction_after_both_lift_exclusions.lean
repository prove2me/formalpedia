-- Prove2me | solution 1 for collatz_merger_gain_obstruction_after_both_lift_exclusions
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:01:00.992215+00:00
-- url     : https://prove2.me/submissions/143748b2-69b5-4fbb-b0aa-5bc47e602c9c

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Range

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
private theorem collatz_no_lifts_merger_gain_constraint (n k a b : ℕ)
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


/-- When the original normalized multiplier is strictly larger, the
visitor must accumulate enough odd steps to compensate for its smaller
start. The visitor-floor hypothesis holds for a least coalescing start. -/
private theorem collatz_larger_original_gain_forces_visitor_odd_steps (n k a b : ℕ)
    (hk : 0<k) (hkn : k<n) (hmeet : runShortcut^[a] n=runShortcut^[b] k)
    (horder : 2^a*shortcutMultiplier b k<2^b*shortcutMultiplier a n)
    (hfloor : ∀ i : ℕ, i≤b → k≤runShortcut^[i] k) :
    3*k*(n-k)<shortcutOddCount b k*n := by
  let o := shortcutOddCount b k
  let A := shortcutMultiplier a n
  let B := shortcutMultiplier b k
  let y := runShortcut^[b] k
  have hB : 0<B := shortcutMultiplier_pos b k
  have hBpow : B=3^o := shortcutMultiplier_eq_pow_three b k
  have hstrong : B*n<2^b*y := by
    apply Nat.lt_of_mul_lt_mul_right (a:=2^a)
    calc
      _ = (2^a*B)*n := by ring
      _ < (2^b*A)*n := Nat.mul_lt_mul_of_pos_right horder (by omega)
      _ = 2^b*(A*n) := by ring
      _ ≤ 2^b*(2^a*y) := by
        apply Nat.mul_le_mul_left
        rw [←show runShortcut^[a] n=y from hmeet]
        exact (shortcutMultiplier_lower a n).1
      _ = _ := by ring
  by_cases hc : o<3*k
  · have hup : 2^b*(k^o*y)≤(3*k+1)^o*k := shortcut_path_upper_at_floor k b k hfloor
    have hstep : ((3*k-o)*n)*(B*k^o)<(3*k*k)*(B*k^o) := calc
      _ = (B*n)*((3*k-o)*k^o) := by ring
      _ < (2^b*y)*((3*k-o)*k^o) := Nat.mul_lt_mul_of_pos_right hstrong
        (Nat.mul_pos (by omega) (Nat.pow_pos hk))
      _ = (3*k-o)*(2^b*(k^o*y)) := by ring
      _ ≤ (3*k-o)*((3*k+1)^o*k) := Nat.mul_le_mul_left _ hup
      _ = ((3*k-o)*(3*k+1)^o)*k := by ring
      _ ≤ (3*k)^(o+1)*k := Nat.mul_le_mul_right k (reciprocal_bernoulli_nat (3*k) o hc.le)
      _ = _ := by rw [pow_succ,mul_pow,hBpow]; ring
    have hsmall : (3*k-o)*n<3*k*k := Nat.lt_of_mul_lt_mul_right hstep
    have hsum : (3*k-o)*n+o*n=3*k*n := by rw [←Nat.add_mul,Nat.sub_add_cancel hc.le]
    have hgap : 3*k*(n-k)+3*k*k=3*k*n := by rw [←Nat.mul_add,Nat.sub_add_cancel hkn.le]
    change 3*k*(n-k)<o*n
    omega
  · exact (Nat.mul_lt_mul_of_pos_left (show n-k<n by omega) (by omega : 0<3*k)).trans_le
      (Nat.mul_le_mul_right n (by omega : 3*k≤o))


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

theorem solution (n k a b : ℕ)
    (hn : 3≤n) (hstay : ∀ t : ℕ, n≤collatzStep^[t] n) (hk : 0<k) (hkn : k<n) :
    let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let odd : ℕ → ℕ → ℕ := fun t x => ((List.range t).map (fun i => (S^[i] x)%2)).sum
    let equalLift := ∃ d m : ℕ, 0<d ∧ d<n ∧
      let r := n%2^m
      d≤r ∧ S^[m] r=S^[m] (r-d) ∧ S^[m] (2^m+r)=S^[m] (2^m+r-d)
    let independentLift := ∃ c d u v s : ℕ, 0<u ∧ 0<v ∧ c≠d ∧
      let P := 2^c*u
      let Q := 2^d*v
      let r := n%P
      0<s ∧ s<r ∧ Q≤P ∧ S^[c] r=S^[d] s ∧ S^[c] (P+r)=S^[d] (Q+s)
    ¬equalLift → ¬independentLift → S^[a] n=S^[b] k →
      (2^a*3^odd b k<2^b*3^odd a n ∧
        ((∀ i : ℕ, i≤b → k≤S^[i] k) → 3*k*(n-k)<odd b k*n)) ∨
      (a=b ∧ k%2=1 ∧ 2*n≤3*k+1 ∧ n<odd a n) := by
  dsimp only
  intro hEqual hIndependent hmeet
  have hcases := collatz_no_lifts_merger_gain_constraint n k a b hn hstay hEqual hIndependent hk hkn hmeet
  have hresult : (2^a*shortcutMultiplier b k<2^b*shortcutMultiplier a n ∧
        ((∀ i : ℕ, i≤b → k≤runShortcut^[i] k) → 3*k*(n-k)<shortcutOddCount b k*n)) ∨
      (a=b ∧ k%2=1 ∧ 2*n≤3*k+1 ∧ n<shortcutOddCount a n) := by
    rcases hcases with h | h
    · exact Or.inl ⟨h,collatz_larger_original_gain_forces_visitor_odd_steps n k a b hk hkn hmeet h⟩
    · exact Or.inr h
  simp only [shortcutMultiplier_eq_pow_three,shortcutOddCount_eq_range] at hresult
  delta runShortcut at hresult
  exact hresult
