-- Prove2me | solution 1 for collatz_root_assumptions_no_uniform_meeting_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T11:14:59.26267+00:00
-- url     : https://prove2.me/submissions/a3c4c403-4445-41b3-87c1-137f7c2d004d

import Definitions.Def_collatzStepMap
import Definitions.Def_collatzMinPreimage
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp

private theorem stepEven (n : ℕ) (h : n % 2 = 0) : collatzStep n = n / 2 := by
  rw [collatzStep, if_pos (Nat.even_iff.mpr h)]

private theorem stepOdd (n : ℕ) (h : n % 2 = 1) : collatzStep n = 3*n+1 := by
  rw [collatzStep, if_neg (by rw [Nat.even_iff, h]; decide)]

private def runShortcut (x : ℕ) : ℕ :=
  if x%2=0 then x/2 else (3*x+1)/2

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

private def collatzShortcutAffinePair : ℕ → ℕ → ℕ × ℕ
  | 0, x => (1,x)
  | t+1, x =>
    let p := collatzShortcutAffinePair t (runShortcut x)
    (if x%2=0 then p.1 else 3*p.1,p.2)

private abbrev shortcutMultiplier (t x : ℕ) : ℕ := (collatzShortcutAffinePair t x).1

private theorem shortcutMultiplier_pos (t x : ℕ) : 0<shortcutMultiplier t x := by
  induction t generalizing x with
  | zero => simp [shortcutMultiplier,collatzShortcutAffinePair]
  | succ t ih =>
    simp only [shortcutMultiplier,collatzShortcutAffinePair]
    split
    · exact ih _
    · exact Nat.mul_pos (by decide) (ih _)

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

private def shortcutNumeratorOffset : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t+1, x => 2*shortcutNumeratorOffset t (runShortcut x) +
      if x%2=0 then 0 else shortcutMultiplier t (runShortcut x)

private theorem shortcut_numerator_identity (t x : ℕ) :
    2^t*runShortcut^[t] x=shortcutMultiplier t x*x+shortcutNumeratorOffset t x := by
  induction t generalizing x with
  | zero => simp [shortcutMultiplier,collatzShortcutAffinePair,shortcutNumeratorOffset]
  | succ t ih =>
    let y := runShortcut x
    let A := shortcutMultiplier t y
    let B := shortcutNumeratorOffset t y
    have he : 2^t*runShortcut^[t] y=A*y+B := ih y
    rw [Function.iterate_succ_apply,pow_succ]
    change (2^t*2)*runShortcut^[t] y=(if x%2=0 then A else 3*A)*x+
      (2*B+(if x%2=0 then 0 else A))
    have hc : (2^t*2)*runShortcut^[t] y=2*(A*y+B) := by
      rw [←he]
      ring
    rw [hc]
    by_cases hx : x%2=0
    · have hy : x=2*y := by dsimp [y]; rw [runShortcut,if_pos hx]; omega
      rw [if_pos hx,if_pos hx,hy]
      ring
    · have hy : 2*y=3*x+1 := by dsimp [y]; rw [runShortcut,if_neg hx]; omega
      rw [if_neg hx,if_neg hx]
      calc
        _ = A*(2*y)+2*B := by ring
        _ = _ := by rw [hy]; ring

private theorem shortcut_numerator_offset_bound (t x : ℕ) :
    shortcutMultiplier t x≤3^t ∧
      shortcutNumeratorOffset t x+2^t≤3^t ∧
      (shortcutMultiplier t x≠3^t → shortcutNumeratorOffset t x+2^t<3^t) ∧
      (shortcutMultiplier t x=3^t → shortcutNumeratorOffset t x+2^t=3^t) := by
  induction t generalizing x with
  | zero => simp [shortcutMultiplier,collatzShortcutAffinePair,shortcutNumeratorOffset]
  | succ t ih =>
    let y := runShortcut x
    let A := shortcutMultiplier t y
    let B := shortcutNumeratorOffset t y
    have h : A≤3^t ∧ B+2^t≤3^t ∧ (A≠3^t → B+2^t<3^t) ∧
        (A=3^t → B+2^t=3^t) := ih y
    change (if x%2=0 then A else 3*A)≤3^(t+1) ∧
      (2*B+(if x%2=0 then 0 else A))+2^(t+1)≤3^(t+1) ∧
      ((if x%2=0 then A else 3*A)≠3^(t+1) →
        (2*B+(if x%2=0 then 0 else A))+2^(t+1)<3^(t+1)) ∧
      ((if x%2=0 then A else 3*A)=3^(t+1) →
        (2*B+(if x%2=0 then 0 else A))+2^(t+1)=3^(t+1))
    have hp : 0<(3:ℕ)^t := Nat.pow_pos (by decide)
    rw [pow_succ (3:ℕ) t,pow_succ (2:ℕ) t]
    by_cases hx : x%2=0
    · simp only [if_pos hx,add_zero]
      exact ⟨by omega,by omega,fun _ => by omega,fun _ => by omega⟩
    · simp only [if_neg hx]
      refine ⟨by omega,by omega,?_,?_⟩
      · intro hne
        have hA : A≠3^t := by omega
        have := h.2.2.1 hA
        omega
      · intro he
        have hA : A=3^t := by omega
        have := h.2.2.2 hA
        omega

private theorem shortcut_all_odd_run (t q : ℕ) (hq : 0<q) :
    runShortcut^[t] (2^t*q-1)=3^t*q-1 := by
  induction t generalizing q with
  | zero => simp
  | succ t ih =>
    have htwo : 2^(t+1)*q=2*(2^t*q) := by rw [pow_succ]; ring
    have hp : 0<2^t*q := Nat.mul_pos (Nat.two_pow_pos t) hq
    have hf : 2^t*(3*q)=3*(2^t*q) := by ring
    have hstep : runShortcut (2^(t+1)*q-1)=2^t*(3*q)-1 := by
      rw [htwo,hf,runShortcut,if_neg (by omega)]
      omega
    rw [Function.iterate_succ_apply,hstep,ih (3*q) (by omega),pow_succ]
    congr 1
    ring

private theorem shortcut_odd_prefix_value (n t : ℕ) (hd : 2^t ∣ n+1) :
    2^t*(runShortcut^[t] n+1)=3^t*(n+1) := by
  obtain ⟨q,hq⟩ := hd
  have hpos : 0<q := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h,mul_zero] at hq
    omega
  have hn : n=2^t*q-1 := by omega
  have he : runShortcut^[t] n=3^t*q-1 := by
    rw [hn,shortcut_all_odd_run t q hpos]
  have hp : 0<3^t*q := Nat.mul_pos (Nat.pow_pos (by decide)) hpos
  rw [he,Nat.sub_add_cancel hp,hq]
  ring

private theorem shortcut_odd_count_add (a b k : ℕ) :
    shortcutOddCount (a+b) k=shortcutOddCount a k+shortcutOddCount b (runShortcut^[a] k) := by
  induction a generalizing k with
  | zero => simp [shortcutOddCount]
  | succ a ih =>
    rw [Nat.succ_add,shortcutOddCount,ih,Function.iterate_succ_apply,shortcutOddCount,
      Nat.add_assoc]

private theorem shortcut_odd_count_le (t k : ℕ) : shortcutOddCount t k≤t := by
  induction t generalizing k with
  | zero => simp [shortcutOddCount]
  | succ t ih =>
    have hi := ih (runShortcut k)
    rw [shortcutOddCount]
    split <;> omega

private theorem shortcut_reverse_shadow_lower_bound (n l k c u : ℕ)
    (hnu : n≤u) (hgap : c*n<u) (hdiv : 3^shortcutOddCount l k ∣ u)
    (h : runShortcut^[l] k=c+u) : n≤k := by
  induction l generalizing c u with
  | zero =>
    change k=c+u at h
    omega
  | succ l ih =>
    let y := runShortcut^[l] k
    have hy : runShortcut y=c+u := by
      rw [Function.iterate_succ_apply'] at h
      exact h
    have hcount : shortcutOddCount (l+1) k=shortcutOddCount l k+
        (if y%2=0 then 0 else 1) := by
      rw [shortcut_odd_count_add,shortcutOddCount,shortcutOddCount,add_zero]
    rw [hcount] at hdiv
    rcases shortcut_preimage_cases hy with he | ⟨_,ho⟩
    · rw [if_pos (by omega : y%2=0),add_zero] at hdiv
      have hd := dvd_mul_of_dvd_right hdiv 2
      have horder : (2*c)*n<2*u := by
        rw [Nat.mul_assoc]
        exact Nat.mul_lt_mul_of_pos_left hgap (by decide)
      apply ih (2*c) (2*u) (by omega) horder hd
      change y=2*c+2*u
      omega
    · rw [if_neg (by omega : y%2≠0),pow_succ] at hdiv
      obtain ⟨w,hw⟩ := hdiv
      let p := 3^shortcutOddCount l k
      have hu : u=3*(p*w) := by rw [hw]; dsimp [p]; ring
      let c' := (2*c-1)/3
      let u' := 2*(p*w)
      have h2c : 2*c=3*c'+1 := by dsimp [c']; omega
      have hc' : 0<c' := by omega
      have hy' : y=c'+u' := by dsimp [u']; omega
      have horder : c'*n<u' := by
        apply Nat.lt_of_mul_lt_mul_left (a:=3)
        calc
          3*(c'*n) ≤ (3*c'+1)*n := by
            rw [←Nat.mul_assoc]
            exact Nat.mul_le_mul_right _ (by omega)
          _ < 2*u := by rw [←h2c,Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_left hgap (by decide)
          _ = 3*u' := by dsimp [u']; rw [hu]; ring
      have hn' := (Nat.le_mul_of_pos_left n hc').trans horder.le
      have hdiv' : p ∣ u' := ⟨2*w,by dsimp [u']; ring⟩
      exact ih c' u' hn' horder hdiv' hy'

private theorem shortcut_shifted_numerator (t x : ℕ) :
    2^t*(runShortcut^[t] x+1)=
      shortcutMultiplier t x*x+(shortcutNumeratorOffset t x+2^t) := by
  rw [Nat.mul_add,mul_one,shortcut_numerator_identity,Nat.add_assoc]

private theorem shortcut_odd_prefix_mono (n a b : ℕ) (hba : b≤a)
    (hd : 2^a ∣ n+1) : runShortcut^[b] n≤runShortcut^[a] n := by
  obtain ⟨q,hq⟩ := hd
  have hpos : 0<q := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h,mul_zero] at hq
    omega
  have hn : n=2^a*q-1 := by omega
  have hp (p : ℕ) : p^b*p^(a-b)=p^a := by rw [←pow_add,Nat.add_sub_of_le hba]
  have hn' : n=2^b*(2^(a-b)*q)-1 := by rw [←Nat.mul_assoc,hp 2,←hn]
  rw [show runShortcut^[b] n=3^b*(2^(a-b)*q)-1 by
    rw [hn',shortcut_all_odd_run b _ (Nat.mul_pos (Nat.two_pow_pos _) hpos)]]
  rw [hn,shortcut_all_odd_run a q hpos]
  apply Nat.sub_le_sub_right
  calc
    3^b*(2^(a-b)*q) ≤ 3^b*(3^(a-b)*q) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right q (Nat.pow_le_pow_left (by decide) _))
    _ = 3^a*q := by rw [←Nat.mul_assoc,hp 3]

theorem collatz_prescribed_odd_prefix_no_few_odd_visitor (n J B a b k : ℕ)
    (h2 : 2^J ∣ n+1) (h3 : 3^B ∣ n) (ha : a≤J) (hb : shortcutOddCount (b-a) k≤B)
    (hkn : k<n) : runShortcut^[a] n≠runShortcut^[b] k := by
  intro hmeet
  have h2a := (pow_dvd_pow 2 ha).trans h2
  by_cases hba : b≤a
  · have h2b := (pow_dvd_pow 2 hba).trans h2a
    have hmono := shortcut_odd_prefix_mono n a b hba h2a
    have hbound := shortcut_numerator_offset_bound b k
    have hprod := Nat.mul_le_mul_right k hbound.1
    have hless : 2^b*(runShortcut^[b] k+1)<2^b*(runShortcut^[b] n+1) := by
      rw [shortcut_shifted_numerator,shortcut_odd_prefix_value n b h2b]
      calc
        _ ≤ 3^b*(k+1) := by rw [Nat.mul_add,mul_one]; omega
        _ < _ := Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos (by decide))
    have hlt := Nat.lt_of_mul_lt_mul_left hless
    omega
  · let l := b-a
    let v := runShortcut^[l] k
    let A := shortcutMultiplier a v
    let C := shortcutNumeratorOffset a v+2^a
    have hd : 3^shortcutOddCount l k ∣ n := (pow_dvd_pow 3 hb).trans h3
    have hfwd : runShortcut^[a] v=runShortcut^[a] n := by
      dsimp [v]
      rw [←Function.iterate_add_apply,show a+l=b by dsimp [l]; omega]
      exact hmeet.symm
    have hsum : A*v+C=3^a*(n+1) :=
      (shortcut_shifted_numerator a v).symm.trans
        (hfwd ▸ shortcut_odd_prefix_value n a h2a)
    have hbound := shortcut_numerator_offset_bound a v
    have hApos : 0<A := shortcutMultiplier_pos a v
    by_cases hA : A=3^a
    · have hC : C=3^a := hbound.2.2.2 hA
      have hprod : 3^a*v=3^a*n := by
        rw [hA,hC,Nat.mul_add,mul_one] at hsum
        omega
      have hvn := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hprod
      have hmin := shortcut_reverse_shadow_lower_bound n l k 0 n (Nat.le_refl n)
        (by omega) hd (by simpa using hvn)
      omega
    · have hClt : C<3^a := hbound.2.2.1 hA
      have hCpos : 0<C := by dsimp [C]; have := Nat.two_pow_pos a; omega
      let f := shortcutOddCount a v
      let D := 3^(a-f)
      have hAf : A=3^f := shortcutMultiplier_eq_pow_three a v
      have hfa : f≤a := by
        by_contra! h
        have hp := Nat.pow_lt_pow_right (by decide : 1<(3:ℕ)) h
        have hm : A≤3^a := hbound.1
        omega
      have hAD : A*D=3^a := by rw [hAf,←pow_add,Nat.add_sub_of_le hfa]
      have hparts : A*v+C=A*(D*n)+A*D := by
        rw [hsum,Nat.mul_add,mul_one,←Nat.mul_assoc,hAD]
      have hvbig : D*n<v := by
        apply Nat.lt_of_mul_lt_mul_left (a:=A)
        omega
      let c := v-D*n
      have hcpos : 0<c := by dsimp [c]; omega
      have hv : v=c+D*n := by dsimp [c]; exact (Nat.sub_add_cancel hvbig.le).symm
      have hclt : c<D := by
        apply Nat.lt_of_mul_lt_mul_left (a:=A)
        rw [hv,Nat.mul_add] at hparts
        omega
      have hgap := Nat.mul_lt_mul_of_pos_right hclt (show 0<n by omega)
      have hmin := (Nat.le_mul_of_pos_left n hcpos).trans hgap.le
      have hshadow := shortcut_reverse_shadow_lower_bound n l k c (D*n) hmin
        hgap (dvd_mul_of_dvd_right hd D) hv
      omega

theorem collatz_prescribed_odd_prefix_no_shorter_visitor (n J B a b k : ℕ)
    (h2 : 2^J ∣ n+1) (h3 : 3^B ∣ n) (ha : a≤J) (hb : b≤a+B)
    (hkn : k<n) : runShortcut^[a] n≠runShortcut^[b] k :=
  collatz_prescribed_odd_prefix_no_few_odd_visitor n J B a b k h2 h3 ha
    ((shortcut_odd_count_le (b-a) k).trans (by omega)) hkn

theorem collatz_unbounded_ternary_divisibility_in_binary_prefix (J B N : ℕ) :
    ∃ n : ℕ, N≤n ∧ n%16=15 ∧ 2^J ∣ n+1 ∧ 3^B ∣ n := by
  let m := 2^(max 4 J)
  let p := 3^B
  have hcop : m.Coprime p := ((show Nat.Coprime 2 3 by decide).pow_left _).pow_right _
  obtain ⟨r,hr2,hr3⟩ := Nat.chineseRemainder hcop 0 1
  let shift := m*p*(N+2)
  let y := r+shift
  have hm : m ∣ shift := ⟨p*(N+2),by dsimp [shift]; ring⟩
  have hp : p ∣ shift := ⟨m*(N+2),by dsimp [shift]; ring⟩
  have hshift : N+2≤shift :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide)))
  have hy : 0<y := by dsimp [y]; omega
  let n := y-1
  have hn : n+1=y := Nat.sub_add_cancel hy
  have hN : N≤n := by dsimp [n,y]; omega
  have h2y : m ∣ y := Nat.modEq_zero_iff_dvd.mp
    (by simpa [y] using hr2.add (Nat.modEq_zero_iff_dvd.mpr hm))
  have h3y : y ≡ 1 [MOD p] := by
    simpa [y] using hr3.add (Nat.modEq_zero_iff_dvd.mpr hp)
  have h3n : p ∣ n := Nat.modEq_zero_iff_dvd.mp
    (Nat.ModEq.add_right_cancel' 1 (by simpa only [hn,zero_add] using h3y))
  have h16 : 16 ∣ n+1 := by
    rw [hn]
    exact (pow_dvd_pow 2 (le_max_left 4 J)).trans h2y
  exact ⟨n,hN,by omega,by rw [hn]; exact (pow_dvd_pow 2 (le_max_right 4 J)).trans h2y,h3n⟩

private theorem normalized_ordinary_iterate (t x : ℕ) :
    ∃ a≤t+1, runShortcut (collatzStep^[t] x)=runShortcut^[a] x := by
  rcases ordinary_iterate_shortcut_cases t x with ⟨d,hdt,hd | ⟨ho,hd⟩⟩
  · exact ⟨d+1,by omega,by rw [hd,Function.iterate_succ_apply']⟩
  · have he : (collatzStep (runShortcut^[d] x))%2=0 := by rw [stepOdd _ ho]; omega
    refine ⟨d+1,by omega,?_⟩
    rw [hd,Function.iterate_succ_apply',runShortcut,if_pos he,stepOdd _ ho,
      runShortcut,if_neg (by omega)]

private theorem min_preimage_lower_bound (depth y n : ℕ)
    (h : ∀ x t : ℕ, t≤depth → collatzStep^[t] x=y → n≤x) :
    n≤collatzMinPreimage depth y := by
  induction depth generalizing y with
  | zero => exact h y 0 (Nat.le_refl 0) rfl
  | succ depth ih =>
    have hy := h y 0 (Nat.zero_le _) rfl
    have hd (z : ℕ) (hz : collatzStep z=y) : n≤collatzMinPreimage depth z := by
      apply ih
      intro x t ht hx
      exact h x (t+1) (by omega) (by rw [Function.iterate_succ_apply',hx,hz])
    have he : collatzStep (2*y)=y := by rw [stepEven _ (by omega)]; omega
    simp only [collatzMinPreimage,le_min_iff]
    refine ⟨hy,hd _ he,?_⟩
    by_cases h6 : y%6=4
    · rw [if_pos h6]
      exact hd _ (by rw [stepOdd _ (by omega)]; omega)
    · simpa [h6] using hy

private theorem ordinary_prefix_no_shorter_visitor (n J B a b k : ℕ)
    (h2 : 2^J ∣ n+1) (h3 : 3^B ∣ n) (ha : a+1≤J) (hb : b+1≤B)
    (hkn : k<n) : collatzStep^[a] n≠collatzStep^[b] k := by
  intro he
  obtain ⟨i,hi,hI⟩ := normalized_ordinary_iterate a n
  obtain ⟨j,hj,hJ⟩ := normalized_ordinary_iterate b k
  exact collatz_prescribed_odd_prefix_no_shorter_visitor n J B i j k
    h2 h3 (hi.trans ha) (by omega) hkn (hI.symm.trans ((congrArg runShortcut he).trans hJ))

theorem collatz_min_preimage_16_through_128_of_divisibility (n : ℕ)
    (h2 : 2^129 ∣ n+1) (h3 : 3^17 ∣ n) :
    ∀ t : ℕ, t≤128 → n≤collatzMinPreimage 16 (collatzStep^[t] n) := by
  intro t ht
  apply min_preimage_lower_bound
  intro k j hj he
  by_contra! hk
  exact ordinary_prefix_no_shorter_visitor n 129 17 t j k h2 h3 (by omega) (by omega) hk he.symm

theorem solution (I T N : ℕ) :
    ∃ n : ℕ, N≤n ∧ 2310000≤n ∧ n%16=15 ∧
      (n%9=0 ∨ n%9=1 ∨ n%9=3 ∨ n%9=6 ∨ n%9=7) ∧
      (∀ t : ℕ, t≤128 → n≤collatzMinPreimage 16 (collatzStep^[t] n)) ∧
      n%81≠10 ∧ (n%2304≠1743 ∧ n%2304≠1599) ∧
      (n%4608≠2847 ∧ n%4608≠735 ∧ n%4608≠991 ∧
        n%4608≠2527 ∧ n%4608≠3039 ∧ n%4608≠4575) ∧
      n%2187 ∉ ([205,325,919,991,1000,1090,1171,2170] : List ℕ) ∧
      ∀ k a b : ℕ, k<n → a≤I → b≤T → collatzStep^[a] n≠collatzStep^[b] k := by
  let J := max 129 (I+1)
  let B := max 17 (T+1)
  obtain ⟨n,hN,hclass,h2,h3⟩ :=
    collatz_unbounded_ternary_divisibility_in_binary_prefix J B (max N 2310000)
  have h2p := (pow_dvd_pow 2 (show 129≤J by exact le_max_left _ _)).trans h2
  have h3p := (pow_dvd_pow 3 (show 17≤B by exact le_max_left _ _)).trans h3
  have h9 : n%9=0 :=
    Nat.mod_eq_zero_of_dvd ((show 9∣3^17 by decide).trans h3p)
  have h81 : n%81=0 :=
    Nat.mod_eq_zero_of_dvd ((show 81∣3^17 by decide).trans h3p)
  have h2187 : n%2187=0 :=
    Nat.mod_eq_zero_of_dvd ((show 2187∣3^17 by decide).trans h3p)
  have exclude (m r : ℕ) (hm : 9∣m) (hr : r%9≠0) : n%m≠r := by
    intro he
    apply hr
    rw [←he,Nat.mod_mod_of_dvd _ hm,h9]
  refine ⟨n,(le_max_left _ _).trans hN,(le_max_right _ _).trans hN,hclass,Or.inl h9,
    collatz_min_preimage_16_through_128_of_divisibility n h2p h3p,
    by rw [h81]; decide,?_,?_,by rw [h2187]; decide,?_⟩
  · exact ⟨exclude _ _ (by decide) (by decide),exclude _ _ (by decide) (by decide)⟩
  · repeat' apply And.intro
    all_goals exact exclude _ _ (by decide) (by decide)
  intro k a b hk ha hb
  exact ordinary_prefix_no_shorter_visitor n J B a b k h2 h3
    (by dsimp [J]; omega) (by dsimp [B]; omega) hk
