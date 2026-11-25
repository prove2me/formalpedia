-- Prove2me | solution 1 for collatz_mergers_from_sixfold_search_or_three_run_classes
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:55:20.281687+00:00
-- url     : https://prove2.me/submissions/3be1b9f7-cb97-471b-b970-6e6ab91db4c3

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Basic
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


private theorem mergerAtProgression
    (n m residue base stride offset t v w : ℕ)
    (h16 : n%16=15) (hres : n%m=residue) (hcoprime : Nat.Coprime 16 m)
    (hbase16 : base%16=15) (hbase : base%m=residue) (hbaseLt : base<16*m)
    (hpositive : 0<offset) (hoffset : offset<base) (hstride : stride≤16*m)
    (hnTrace : traceProgression 2 (16*m) base=some (v,w))
    (hkTrace : traceProgression t stride offset=some (v,w)) :
    ∃ k : ℕ, 0<k ∧ k<n ∧ collatzStep^[2] n=collatzStep^[t] k := by
  have hmod : n% (16*m)=base := by
    have heq : n ≡ base [MOD (16*m)] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcoprime).mp
        ⟨h16.trans hbase16.symm,hres.trans hbase.symm⟩
    change n%(16*m)=base%(16*m) at heq
    exact heq.trans (Nat.mod_eq_of_lt hbaseLt)
  let q := n/(16*m)
  have hn : n=(16*m)*q+base := by
    rw [Nat.add_comm,←hmod]
    exact (Nat.mod_add_div _ _).symm
  let k := stride*q+offset
  have hk : k<n := by
    rw [hn]
    exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right q hstride) hoffset
  refine ⟨k,by dsimp [k]; omega,hk,?_⟩
  calc
    collatzStep^[2] n = v*q+w := by rw [hn]; exact traceProgression_sound _ _ _ _ _ hnTrace q
    _ = collatzStep^[t] k := (traceProgression_sound _ _ _ _ _ hkTrace q).symm

/-- These three infinite congruence classes have smaller visitors built
from three blocks of odd pairs and halvings. -/
private theorem collatz_initial_anchor_three_run_merger_classes (n : ℕ)
    (h16 : n%16=15)
    (hres : n%2187=444 ∨ n%6561=4408 ∨ n%19683=3229) :
    ∃ k t : ℕ, 0<k ∧ k<n ∧ collatzStep^[2] n=collatzStep^[t] k := by
  rcases hres with h | h | h
  · obtain ⟨k,hk,hlt,hm⟩ :=
      mergerAtProgression n 2187 444 20127 32768 18847 20 52488 30191 h16 h
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨k,20,hk,hlt,hm⟩
  · obtain ⟨k,hk,hlt,hm⟩ :=
      mergerAtProgression n 6561 4408 50335 65536 31423 22 157464 75503 h16 h
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨k,22,hk,hlt,hm⟩
  · obtain ⟨k,hk,hlt,hm⟩ :=
      mergerAtProgression n 19683 3229 121327 262144 100991 25 472392 181991 h16 h
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨k,25,hk,hlt,hm⟩


/-- Connectivity by shortcut Collatz edges with both ends strictly below the cap. -/
private def collatzBelowCap (cap : ℕ) : ℕ → ℕ → Prop :=
  Relation.EqvGen (fun a b => a<cap ∧ b<cap ∧ runShortcut a=b)

private def ordinaryCoal (a b : ℕ) : Prop :=
  ∃ s t : ℕ, collatzStep^[s] a=collatzStep^[t] b

private theorem ordinaryCoal_equivalence : Equivalence ordinaryCoal := by
  constructor
  · exact fun _ => ⟨0,0,rfl⟩
  · rintro a b ⟨s,t,h⟩
    exact ⟨t,s,h.symm⟩
  · rintro a b c ⟨s,t,hab⟩ ⟨u,v,hbc⟩
    refine ⟨u+s,t+v,?_⟩
    rw [Function.iterate_add_apply,Function.iterate_add_apply,hab,←hbc,
      ←Function.iterate_add_apply,←Function.iterate_add_apply,Nat.add_comm u t]

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

private theorem belowCap_ordinaryCoal {cap a b : ℕ} (h : collatzBelowCap cap a b) :
    ordinaryCoal a b := by
  refine belowCap_lift ordinaryCoal_equivalence id h ?_
  intro x y _ _ hxy
  obtain ⟨t,ht⟩ := runShortcut_reachable x
  exact ⟨t,0,ht.trans hxy⟩

private theorem belowCap_mono {k l a b : ℕ} (hl : k≤l) :
    collatzBelowCap k a b → collatzBelowCap l a b :=
  Relation.EqvGen.mono (fun _ _ h => ⟨h.1.trans_le hl,h.2.1.trans_le hl,h.2.2⟩) a b


private theorem bridgeSteps {H : ℕ} (h : H%6=2) :
    runShortcut ((2*H-1)/3)=H ∧ runShortcut H=H/2 := by
  constructor
  · have hodd : ((2*H-1)/3)%2=1 := by omega
    rw [runShortcut,if_neg (by omega)]
    omega
  · rw [runShortcut,if_pos (by omega)]


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


private theorem sixfold_right_component (n : ℕ) (hodd : n%2=1) :
    collatzBelowCap (6*n+2) n (3*n+1) := by
  let p := (3*n+1)/2
  have h₁ : collatzBelowCap (6*n+2) n p := by
    apply Relation.EqvGen.rel
    exact ⟨by omega,by dsimp [p]; omega,by rw [runShortcut,if_neg (by omega)]⟩
  have h₂ : collatzBelowCap (6*n+2) (3*n+1) p := by
    apply Relation.EqvGen.rel
    exact ⟨by omega,by dsimp [p]; omega,by rw [runShortcut,if_pos (by omega)]⟩
  exact (belowCap_equivalence _).trans h₁ ((belowCap_equivalence _).symm h₂)

private theorem sixfold_left_relay (n : ℕ) (hn : 0<n) (hm : n%9=7) :
    collatzBelowCap (6*n+2) ((32*n+1)/9) (4*n+1) := by
  let w := (32*n+1)/9
  let r := (8*n+1)/3
  have hw : w%2=1 := by dsimp [w]; omega
  have hr : r%2=1 := by dsimp [r]; omega
  have h₁ : collatzBelowCap (6*n+2) w (2*r) := by
    apply Relation.EqvGen.rel
    have he : runShortcut w=2*r := by
      rw [runShortcut,if_neg (by omega)]
      dsimp [w,r]
      omega
    exact ⟨by dsimp [w]; omega,by dsimp [r]; omega,he⟩
  have h₂ : collatzBelowCap (6*n+2) (2*r) r := by
    apply Relation.EqvGen.rel
    have he : runShortcut (2*r)=r := by rw [runShortcut,if_pos (by omega)]; omega
    exact ⟨by dsimp [r]; omega,by dsimp [r]; omega,he⟩
  have h₃ : collatzBelowCap (6*n+2) r (4*n+1) := by
    apply Relation.EqvGen.rel
    have he : runShortcut r=4*n+1 := by
      rw [runShortcut,if_neg (by omega)]
      dsimp [r]
      omega
    exact ⟨by dsimp [r]; omega,by omega,he⟩
  exact (belowCap_equivalence _).trans h₁ ((belowCap_equivalence _).trans h₂ h₃)


private theorem collatz_sixfold_connects_of_ancestor (n k : ℕ) (hn : 0<n) (hodd : n%2=1)
    (hn7 : n%9=7) (hreach : collatzShortcutReachesBelow (6*n+2) k ((32*n+1)/9)) :
    collatzBelowCap (6*n+3) n k := by
  let H := 6*n+2
  let q := 4*n+1
  let v := 3*n+1
  have hmod : H%6=2 := by dsimp [H]; omega
  have hq : (2*H-1)/3=q := by dsimp [H,q]; omega
  have hv : H/2=v := by dsimp [H,v]; omega
  have hnv : collatzBelowCap H n v := sixfold_right_component n hodd
  have R := belowCap_equivalence (H+1)
  have qv : collatzBelowCap (H+1) q v := by
    obtain ⟨h₁,h₂⟩ := bridgeSteps hmod
    rw [hq] at h₁
    rw [hv] at h₂
    exact R.trans (.rel _ _ ⟨by dsimp [q,H]; omega,by omega,h₁⟩)
      (.rel _ _ ⟨by omega,by dsimp [v,H]; omega,h₂⟩)
  have hkq : collatzBelowCap H k q :=
    (belowCap_equivalence H).trans (shortcutReach_belowCap hreach)
      (sixfold_left_relay n hn hn7)
  have hnq : collatzBelowCap (H+1) n k :=
    R.trans (belowCap_mono (Nat.le_succ _) hnv)
      (R.symm (R.trans (belowCap_mono (Nat.le_succ _) hkq) qv))
  exact hnq


/-- In the cap below 6n+2, search backwards until a positive state
below n is found. Only the indicated inverse continuation is needed. -/
private def collatzSixfoldVisitorCheck (n : ℕ) : ℕ → ℕ → Bool
  | fuel,v =>
    if 0<v ∧ v<6*n+2 then
      if v<n then true
      else match fuel with
        | 0 => false
        | fuel+1 =>
          if v%3=2 then collatzSixfoldVisitorCheck n fuel ((2*v-1)/3)
          else if v%3=1 ∧ 2*v<6*n+2 then
            collatzSixfoldVisitorCheck n fuel ((4*v-1)/3)
          else false
    else false

private theorem shortcutReach_append {cap k x y : ℕ}
    (h : collatzShortcutReachesBelow cap k x) (he : runShortcut x=y) (hy : y<cap) :
    collatzShortcutReachesBelow cap k y := by
  obtain ⟨t,ht,hcap⟩ := h
  refine ⟨t+1,by rw [Function.iterate_succ_apply',ht,he],?_⟩
  intro i hi
  by_cases hle : i≤t
  · exact hcap i hle
  · rw [show i=t+1 by omega,Function.iterate_succ_apply',ht,he]
    exact hy

private theorem sixfold_direct_reverse {v : ℕ} (hm : v%3=2) :
    runShortcut ((2*v-1)/3)=v := by
  have hodd : ((2*v-1)/3)%2=1 := by omega
  rw [runShortcut,if_neg (by omega)]
  omega

private theorem sixfold_doubled_reverse {v : ℕ} (hm : v%3=1) :
    runShortcut ((4*v-1)/3)=2*v ∧ runShortcut (2*v)=v := by
  constructor
  · have hodd : ((4*v-1)/3)%2=1 := by omega
    rw [runShortcut,if_neg (by omega)]
    omega
  · rw [runShortcut,if_pos (by omega)]
    omega

private theorem collatz_sixfold_visitor_check_sound (n fuel v : ℕ)
    (h : collatzSixfoldVisitorCheck n fuel v=true) :
    ∃ k : ℕ, 0<k ∧ k<n ∧ collatzShortcutReachesBelow (6*n+2) k v := by
  induction fuel generalizing v with
  | zero =>
    by_cases hcap : 0<v ∧ v<6*n+2
    · by_cases hlt : v<n
      · exact ⟨v,hcap.1,hlt,0,rfl,fun i hi => by
          have he : i=0 := by omega
          simpa [he] using hcap.2⟩
      · simp [collatzSixfoldVisitorCheck,hcap,hlt] at h
    · simp [collatzSixfoldVisitorCheck,hcap] at h
  | succ fuel ih =>
    by_cases hcap : 0<v ∧ v<6*n+2
    · by_cases hlt : v<n
      · exact ⟨v,hcap.1,hlt,0,rfl,fun i hi => by
          have he : i=0 := by omega
          simpa [he] using hcap.2⟩
      · by_cases hmod : v%3=2
        · have hcheck : collatzSixfoldVisitorCheck n fuel ((2*v-1)/3)=true := by
            simpa [collatzSixfoldVisitorCheck,hcap,hlt,hmod] using h
          obtain ⟨k,hk,hkn,hreach⟩ := ih _ hcheck
          exact ⟨k,hk,hkn,shortcutReach_append hreach (sixfold_direct_reverse hmod) hcap.2⟩
        · by_cases hdouble : v%3=1 ∧ 2*v<6*n+2
          · have hcheck : collatzSixfoldVisitorCheck n fuel ((4*v-1)/3)=true := by
              simpa [collatzSixfoldVisitorCheck,hcap,hlt,hmod,hdouble] using h
            obtain ⟨k,hk,hkn,hreach⟩ := ih _ hcheck
            obtain ⟨h₁,h₂⟩ := sixfold_doubled_reverse hdouble.1
            exact ⟨k,hk,hkn,shortcutReach_append
              (shortcutReach_append hreach h₁ hdouble.2) h₂ hcap.2⟩
          · simp [collatzSixfoldVisitorCheck,hcap,hlt,hmod,hdouble] at h
    · simp [collatzSixfoldVisitorCheck,hcap] at h


private def collatzSixfoldBridgeCheck (n : ℕ) : Bool :=
  decide (n%9=7) && collatzSixfoldVisitorCheck n (6*n+1) ((32*n+1)/9)


private theorem collatz_coalescence_from_sixfold_bridge_check (n : ℕ) (hodd : n%2=1)
    (h : collatzSixfoldBridgeCheck n=true) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  obtain ⟨hmod,hcheck⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨k,hk,hlt,hreach⟩ := collatz_sixfold_visitor_check_sound n _ _ hcheck
  have hc := collatz_sixfold_connects_of_ancestor n k (by omega) hodd
    (of_decide_eq_true hmod) hreach
  obtain ⟨a,b,heq⟩ := belowCap_ordinaryCoal hc
  exact ⟨k,a,b,hk,hlt,heq⟩


/-- The occupied state of the deterministic search. Success and zero
are absorbing, so this map may be iterated a fixed number of times. -/
private def collatzSixfoldReverseStep (n v : ℕ) : ℕ :=
  if 0<v ∧ v<6*n+2 then
    if v<n then v
    else if v%3=2 then (2*v-1)/3
    else if v%3=1 ∧ 2*v<6*n+2 then (4*v-1)/3
    else 0
  else 0

private theorem collatz_sixfold_check_iff_reverse_iterate (n fuel v : ℕ) :
    collatzSixfoldVisitorCheck n fuel v=true ↔
      0<(collatzSixfoldReverseStep n)^[fuel] v ∧ (collatzSixfoldReverseStep n)^[fuel] v<n := by
  induction fuel generalizing v with
  | zero =>
    change collatzSixfoldVisitorCheck n 0 v=true ↔ 0<v ∧ v<n
    by_cases hcap : 0<v ∧ v<6*n+2
    · simp [collatzSixfoldVisitorCheck,hcap]
    · simp [collatzSixfoldVisitorCheck,hcap]
      omega
  | succ fuel ih =>
    rw [Function.iterate_succ_apply,←ih]
    by_cases hcap : 0<v ∧ v<6*n+2
    · by_cases hsmall : v<n
      · cases fuel <;> simp [collatzSixfoldVisitorCheck,collatzSixfoldReverseStep,hcap,hsmall]
      · by_cases hm : v%3=2
        · simp [collatzSixfoldVisitorCheck,collatzSixfoldReverseStep,hcap,hsmall,hm]
        · by_cases hd : v%3=1 ∧ 2*v<6*n+2
          · simp [collatzSixfoldVisitorCheck,collatzSixfoldReverseStep,hcap,hsmall,hd]
          · cases fuel <;> simp [collatzSixfoldVisitorCheck,collatzSixfoldReverseStep,
              hcap,hsmall,hm,hd]
    · cases fuel <;> simp [collatzSixfoldVisitorCheck,collatzSixfoldReverseStep,hcap]

private theorem collatz_coalescence_from_sixfold_iterate_or_three_run_classes (n : ℕ)
    (hclass : n%16=15)
    (h :
      (n%9=7 ∧
        let u := (collatzSixfoldReverseStep n)^[6*n+1] ((32*n+1)/9)
        0<u ∧ u<n) ∨
      n%2187=444 ∨ n%6561=4408 ∨ n%19683=3229) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  rcases h with ⟨hm,hiter⟩ | h
  · have hcheck := (collatz_sixfold_check_iff_reverse_iterate n (6*n+1) ((32*n+1)/9)).mpr hiter
    exact collatz_coalescence_from_sixfold_bridge_check n (by omega)
      (Bool.and_eq_true_iff.mpr ⟨by simp [hm],hcheck⟩)
  · obtain ⟨k,t,hk,hlt,hmeet⟩ := collatz_initial_anchor_three_run_merger_classes n hclass h
    exact ⟨k,2,t,hk,hlt,hmeet⟩

theorem solution (n : ℕ) (hclass : n%16=15)
    (h : (n%9=7 ∧
      let next : ℕ → ℕ := fun v =>
        if 0<v ∧ v<6*n+2 then
          if v<n then v
          else if v%3=2 then (2*v-1)/3
          else if v%3=1 ∧ 2*v<6*n+2 then (4*v-1)/3
          else 0
        else 0
      let u := next^[6*n+1] ((32*n+1)/9)
      0<u ∧ u<n) ∨ n%2187=444 ∨ n%6561=4408 ∨ n%19683=3229) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  exact collatz_coalescence_from_sixfold_iterate_or_three_run_classes n hclass h
