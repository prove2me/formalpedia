-- Prove2me | solution 1 for collatz_sixfold_progression_class_mergers
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:46:58.235587+00:00
-- url     : https://prove2.me/submissions/9eb33647-2945-4494-abfc-895de991b6a9

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Factorization.Basic
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


private theorem divTwoAffine {c d q : ℕ} (hc : c%2=0) :
    (c*q+d)/2=(c/2)*q+d/2 := by
  have h : c*q=2*((c/2)*q) := by
    rw [←Nat.mul_assoc,show 2*(c/2)=c by omega]
  calc
    (c*q+d)/2 = (2*((c/2)*q)+d)/2 := by rw [h]
    _ = (c/2)*q+d/2 := by omega

private theorem mulEvenCoeff {c d q : ℕ} (hc : c%2=0) :
    (c*q+d)%2=d%2 := by
  rw [Nat.add_mod,Nat.mul_mod,hc]
  simp


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


private def shortcutAffine (a b : ℕ) : Option (ℕ × ℕ) :=
  if a%2=0 then
    if b%2=0 then some (a/2,b/2) else some (3*a/2,(3*b+1)/2)
  else none

private theorem shortcutAffine_sound {a b c d : ℕ}
    (h : shortcutAffine a b=some (c,d)) (q : ℕ) :
    runShortcut (a*q+b)=c*q+d := by
  by_cases ha : a%2=0
  · by_cases hb : b%2=0
    · simp [shortcutAffine,ha,hb] at h
      rcases h with ⟨rfl,rfl⟩
      rw [runShortcut,if_pos (by rwa [mulEvenCoeff ha]),divTwoAffine ha]
    · simp [shortcutAffine,ha,hb] at h
      rcases h with ⟨rfl,rfl⟩
      rw [runShortcut,if_neg (by rwa [mulEvenCoeff ha])]
      have hmul : (3*a)%2=0 := by simp [Nat.mul_mod,ha]
      rw [show 3*(a*q+b)+1=(3*a)*q+(3*b+1) by ring,divTwoAffine hmul]
  · simp [shortcutAffine,ha] at h

private def traceShortcutBelow : ℕ → ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | t, L, R, a, b =>
    if a≤L ∧ b<R then
      match t with
      | 0 => some (a,b)
      | t+1 => (shortcutAffine a b).bind fun (c,d) => traceShortcutBelow t L R c d
    else none

private theorem traceShortcutBelow_sound (t L R a b c d : ℕ)
    (h : traceShortcutBelow t L R a b=some (c,d)) (q : ℕ) :
    runShortcut^[t] (a*q+b)=c*q+d ∧
      ∀ i : ℕ, i≤t → runShortcut^[i] (a*q+b)<L*q+R := by
  induction t generalizing a b with
  | zero =>
    by_cases hsize : a≤L ∧ b<R
    · simp [traceShortcutBelow,hsize] at h
      rcases h with ⟨rfl,rfl⟩
      refine ⟨rfl,fun i hi => ?_⟩
      have he : i=0 := by omega
      subst i
      exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right q hsize.1) hsize.2
    · simp [traceShortcutBelow,hsize] at h
  | succ t ih =>
    by_cases hsize : a≤L ∧ b<R
    · cases hs : shortcutAffine a b with
      | none => simp [traceShortcutBelow,hsize,hs] at h
      | some pair =>
        obtain ⟨a',b'⟩ := pair
        have next : traceShortcutBelow t L R a' b'=some (c,d) := by
          simpa [traceShortcutBelow,hsize,hs] using h
        have he := shortcutAffine_sound hs q
        obtain ⟨hval,hbound⟩ := ih _ _ next
        refine ⟨by rwa [Function.iterate_succ_apply,he],?_⟩
        intro i hi
        cases i with
        | zero => exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right q hsize.1) hsize.2
        | succ i =>
          rw [Function.iterate_succ_apply,he]
          exact hbound i (by omega)
    · simp [traceShortcutBelow,hsize] at h

private structure SixfoldCertificate where
  period : ℕ
  base : ℕ
  stride : ℕ
  offset : ℕ
  steps : ℕ

private def sixfoldCertificateValid (c : SixfoldCertificate) : Bool :=
  decide (c.base<c.period ∧ c.period%18=0 ∧ c.base%18=7 ∧
    0<c.offset ∧ c.offset<c.base ∧ c.stride≤c.period) &&
    decide (traceShortcutBelow c.steps (6*c.period) (6*c.base+2) c.stride c.offset =
      some (32*c.period/9,(32*c.base+1)/9))

private theorem sixfoldCertificate_sound (c : SixfoldCertificate)
    (hvalid : sixfoldCertificateValid c=true) (n : ℕ) (hclass : n%c.period=c.base) :
    ∃ k : ℕ, 0<k ∧ k<n ∧ collatzBelowCap (6*n+3) n k := by
  unfold sixfoldCertificateValid at hvalid
  obtain ⟨hsize,htrace⟩ := Bool.and_eq_true_iff.mp hvalid
  obtain ⟨_,hperiod,hbase,hpos,hless,hstride⟩ := of_decide_eq_true hsize
  let q := n/c.period
  let k := c.stride*q+c.offset
  have hn : n=c.period*q+c.base := by
    rw [Nat.add_comm,←hclass]
    exact (Nat.mod_add_div _ _).symm
  have hn18 : n%18=7 := by rw [hn,Nat.add_mod,Nat.mul_mod,hperiod,hbase]; simp
  have hk : k<n := by
    rw [hn]
    exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right q hstride) hless
  have hcoef : 32*c.period=9*(32*c.period/9) := by omega
  have hw : (32*n+1)/9=(32*c.period/9)*q+(32*c.base+1)/9 := calc
    _ = ((32*c.period)*q+(32*c.base+1))/9 := by rw [hn]; ring_nf
    _ = _ := by
      have hprod : (32*c.period)*q=9*((32*c.period/9)*q) := by
        rw [←Nat.mul_assoc,←hcoef]
      rw [hprod]
      omega
  have cap : 6*n+2=(6*c.period)*q+(6*c.base+2) := by rw [hn]; ring
  obtain ⟨hval,hbound⟩ := traceShortcutBelow_sound _ _ _ _ _ _ _ (of_decide_eq_true htrace) q
  have hreach : collatzShortcutReachesBelow (6*n+2) k ((32*n+1)/9) := by
    rw [hw,cap]
    exact ⟨c.steps,hval,hbound⟩
  exact ⟨k,by dsimp [k]; omega,hk,
    collatz_sixfold_connects_of_ancestor n k (by omega) (by omega) (by omega) hreach⟩

private def sixfoldCertifiedClasses : List SixfoldCertificate :=
  [
    ⟨69984,14335,65536,13423,6⟩,
    ⟨629856,146527,524288,121967,9⟩,
    ⟨5668704,3995647,4194304,2956399,12⟩,
    ⟨51018336,37378015,33554432,24583279,15⟩,
    ⟨153055008,109181599,134217728,95744047,17⟩,
    ⟨1377495072,840444415,1073741824,655116911,20⟩,
    ⟨12397455648,3901544575,8589934592,2703297647,23⟩,
    ⟨37192366944,6197369695,34359738368,5725368367,25⟩,
    ⟨334731302496,208689145279,274877906944,171373382255,28⟩,
    ⟨3012581722464,2737770097471,2199023255552,1998425492591,31⟩,
    ⟨27113235502176,1064113584991,17592186044416,690440805487,34⟩,
    ⟨81339706506528,74370268831615,70368744177664,64339332493359,36⟩,
    ⟨732057358558752,472031056196863,562949953421312,362990492469871,39⟩,
    ⟨6588516227028768,2749542838379647,4503599627370496,1879458086718575,42⟩,
    ⟨19765548681086304,6653848750692991,18014398509481984,6064343821201455,44⟩,
    ⟨177889938129776736,169170582350735935,144115188075855872,137051316947405423,47⟩,
    ⟨1601009443167990624,307529423118340063,1152921504606846976,221458584598285423,50⟩
  ]

private def collatzSixfoldModuli : List (ℕ × ℕ) :=
  sixfoldCertifiedClasses.map fun c => (c.period,c.base)

set_option maxRecDepth 4096 in
private theorem sixfoldCertifiedClasses_valid :
    sixfoldCertifiedClasses.all sixfoldCertificateValid=true := by decide

/-- Each listed congruence class has a smaller merger in the shortcut
graph capped at 6n+2. The quotient of the start by the modulus is free. -/
private theorem collatz_sixfold_progression_classes (n : ℕ)
    (h : ∃ a : ℕ × ℕ, a∈collatzSixfoldModuli ∧ n%a.1=a.2) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k ∧
      collatzBelowCap (6*n+3) n k := by
  obtain ⟨a,hmem,hclass⟩ := h
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hmem
  have hvalid := (List.all_eq_true.mp sixfoldCertifiedClasses_valid) c hc
  obtain ⟨k,hk,hlt,hconn⟩ := sixfoldCertificate_sound c hvalid n hclass
  obtain ⟨a,b,hm⟩ := belowCap_ordinaryCoal hconn
  exact ⟨k,a,b,hk,hlt,hm,hconn⟩

theorem solution (n : ℕ)
    (h : ∃ a : ℕ × ℕ, a ∈
      ([(69984, 14335),
       (629856, 146527),
       (5668704, 3995647),
       (51018336, 37378015),
       (153055008, 109181599),
       (1377495072, 840444415),
       (12397455648, 3901544575),
       (37192366944, 6197369695),
       (334731302496, 208689145279),
       (3012581722464, 2737770097471),
       (27113235502176, 1064113584991),
       (81339706506528, 74370268831615),
       (732057358558752, 472031056196863),
       (6588516227028768, 2749542838379647),
       (19765548681086304, 6653848750692991),
       (177889938129776736, 169170582350735935),
       (1601009443167990624, 307529423118340063)] : List (ℕ × ℕ)) ∧ n%a.1=a.2) :
    let shortcut : ℕ → ℕ := fun x =>
      if x % 2 = 0 then x / 2 else (3*x+1)/2
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k ∧
      Relation.EqvGen (fun x y => x<6*n+3 ∧ y<6*n+3 ∧ shortcut x=y) n k := by
  exact collatz_sixfold_progression_classes n h
