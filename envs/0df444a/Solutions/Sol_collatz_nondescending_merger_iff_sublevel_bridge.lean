-- Prove2me | solution 1 for collatz_nondescending_merger_iff_sublevel_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T19:37:08.245192+00:00
-- url     : https://prove2.me/submissions/9abbe6fe-2230-408c-bd81-962d61229150

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

private theorem caps_ordinaryCoal_equivalence :
    Equivalence (fun a b : ℕ => ∃ cap : ℕ, collatzBelowCap cap a b) := by
  constructor
  · exact fun a => ⟨a+1,(belowCap_equivalence _).refl a⟩
  · rintro a b ⟨cap,h⟩
    exact ⟨cap,(belowCap_equivalence _).symm h⟩
  · rintro a b c ⟨j,hj⟩ ⟨k,hk⟩
    exact ⟨max j k,(belowCap_equivalence _).trans
      (belowCap_mono (le_max_left _ _) hj) (belowCap_mono (le_max_right _ _) hk)⟩

private theorem ordinaryStep_in_some_cap (x : ℕ) :
    ∃ cap : ℕ, collatzBelowCap cap x (collatzStep x) := by
  let y := collatzStep x
  let z := runShortcut x
  let cap := 1+max x (max y z)
  have hx : x<cap := by dsimp [cap]; omega
  have hy : y<cap := by dsimp [cap]; omega
  have hz : z<cap := by dsimp [cap]; omega
  have hfirst : collatzBelowCap cap x z := .rel _ _ ⟨hx,hz,rfl⟩
  by_cases he : x%2=0
  · have hz' : z=y := by dsimp [z,y]; rw [runShortcut,if_pos he,stepEven _ he]
    refine ⟨cap,?_⟩
    change collatzBelowCap cap x y
    rw [←hz']
    exact hfirst
  · have ho : x%2=1 := by omega
    have hz' : runShortcut y=z := by
      dsimp [z,y]
      rw [stepOdd _ ho,runShortcut,if_pos (by omega),runShortcut,if_neg he]
    have hlast : collatzBelowCap cap y z := .rel _ _ ⟨hy,hz,hz'⟩
    exact ⟨cap,(belowCap_equivalence _).trans hfirst ((belowCap_equivalence _).symm hlast)⟩

private theorem ordinaryIterate_in_some_cap (a t : ℕ) :
    ∃ cap : ℕ, collatzBelowCap cap a (collatzStep^[t] a) := by
  induction t with
  | zero => exact caps_ordinaryCoal_equivalence.refl a
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact caps_ordinaryCoal_equivalence.trans ih (ordinaryStep_in_some_cap _)

private theorem ordinaryCoal_in_some_cap {a b : ℕ} (h : ordinaryCoal a b) :
    ∃ cap : ℕ, collatzBelowCap cap a b := by
  obtain ⟨s,t,hm⟩ := h
  have ha := ordinaryIterate_in_some_cap a s
  rw [hm] at ha
  exact caps_ordinaryCoal_equivalence.trans ha
    (caps_ordinaryCoal_equivalence.symm (ordinaryIterate_in_some_cap b t))

private theorem topEdge_cases {H a b : ℕ} (ha : a≤H) (hb : b≤H) (h : runShortcut a=b) :
    (a<H ∧ b<H) ∨ (a=H ∧ b=H) ∨
      (a=H ∧ b<H ∧ H%2=0 ∧ b=H/2) ∨
      (a<H ∧ b=H ∧ H%3=2 ∧ a=(2*H-1)/3) := by
  rcases lt_or_eq_of_le ha with ha' | ha'
  · rcases lt_or_eq_of_le hb with hb' | hb'
    · exact Or.inl ⟨ha',hb'⟩
    · rw [hb'] at h
      by_cases he : a%2=0
      · rw [runShortcut,if_pos he] at h
        omega
      · rw [runShortcut,if_neg he] at h
        have heq : 2*H=3*a+1 := by omega
        exact Or.inr (Or.inr (Or.inr ⟨ha',hb',by omega,by omega⟩))
  · rw [ha'] at h
    rcases lt_or_eq_of_le hb with hb' | hb'
    · by_cases he : H%2=0
      · rw [runShortcut,if_pos he] at h
        exact Or.inr (Or.inr (Or.inl ⟨ha',hb',he,h.symm⟩))
      · rw [runShortcut,if_neg he] at h
        omega
    · exact Or.inr (Or.inl ⟨ha',hb'⟩)

private theorem topIsolated {H a b : ℕ} (hodd : H%2=1) (hmod : H%3≠2)
    (h : collatzBelowCap (H+1) a b) : a=H ↔ b=H := by
  have hR : Equivalence (fun x y : ℕ => x=H ↔ y=H) :=
    ⟨fun _ => Iff.rfl,fun h => h.symm,fun h₁ h₂ => h₁.trans h₂⟩
  refine belowCap_lift hR id h ?_
  intro x y hx hy he
  rcases topEdge_cases (H:=H) (by omega) (by omega) he with h | h | h | h
  · exact iff_of_false (Nat.ne_of_lt h.1) (Nat.ne_of_lt h.2)
  · exact iff_of_true h.1 h.2
  · omega
  · exact (hmod h.2.2.1).elim

private def linkedBelow (H u v a b : ℕ) : Prop :=
  collatzBelowCap H a b ∨
    (collatzBelowCap H a u ∧ collatzBelowCap H v b) ∨
    (collatzBelowCap H a v ∧ collatzBelowCap H u b)

private theorem linkedBelow_equivalence (H u v : ℕ) : Equivalence (linkedBelow H u v) := by
  have R := belowCap_equivalence H
  constructor
  · exact fun a => Or.inl (R.refl a)
  · rintro a b (h | ⟨hau,hvb⟩ | ⟨hav,hub⟩)
    · exact Or.inl (R.symm h)
    · exact Or.inr (Or.inr ⟨R.symm hvb,R.symm hau⟩)
    · exact Or.inr (Or.inl ⟨R.symm hub,R.symm hav⟩)
  · rintro a b c (hab | ⟨hau,hvb⟩ | ⟨hav,hub⟩) (hbc | ⟨hbu,hvc⟩ | ⟨hbv,huc⟩)
    · exact Or.inl (R.trans hab hbc)
    · exact Or.inr (Or.inl ⟨R.trans hab hbu,hvc⟩)
    · exact Or.inr (Or.inr ⟨R.trans hab hbv,huc⟩)
    · exact Or.inr (Or.inl ⟨hau,R.trans hvb hbc⟩)
    · exact Or.inr (Or.inl ⟨hau,hvc⟩)
    · exact Or.inl (R.trans hau huc)
    · exact Or.inr (Or.inr ⟨hav,R.trans hub hbc⟩)
    · exact Or.inl (R.trans hav hvc)
    · exact Or.inr (Or.inr ⟨hav,huc⟩)

private theorem topStep_decomposition {H a b : ℕ} (ha : a<H) (hb : b<H)
    (h : collatzBelowCap (H+1) a b) :
    collatzBelowCap H a b ∨
      (H%6=2 ∧
        ((collatzBelowCap H a ((2*H-1)/3) ∧ collatzBelowCap H (H/2) b) ∨
          (collatzBelowCap H a (H/2) ∧ collatzBelowCap H ((2*H-1)/3) b))) := by
  let u := (2*H-1)/3
  let v := H/2
  let f := fun z : ℕ => if z=H then (if H%2=0 then v else u) else z
  have hfa : f a=a := if_neg (by omega)
  have hfb : f b=b := if_neg (by omega)
  by_cases hbridge : H%6=2
  · have heven : H%2=0 := by omega
    have htop : f H=v := by simp [f,heven]
    have hh : linkedBelow H u v (f a) (f b) := by
      refine belowCap_lift (linkedBelow_equivalence H u v) f h ?_
      intro x y hx hy hxy
      rcases topEdge_cases (H:=H) (by omega) (by omega) hxy with h | h | h | h
      · have hfx : f x=x := if_neg (by omega)
        have hfy : f y=y := if_neg (by omega)
        rw [hfx,hfy]
        exact Or.inl (.rel _ _ ⟨h.1,h.2,hxy⟩)
      · rw [h.1,h.2]
        exact (linkedBelow_equivalence _ _ _).refl _
      · have hfy : f y=y := if_neg (by omega)
        rw [h.1,htop,hfy,h.2.2.2]
        exact (linkedBelow_equivalence _ _ _).refl _
      · have hfx : f x=x := if_neg (by omega)
        rw [hfx,h.2.1,htop,h.2.2.2]
        exact Or.inr (Or.inl ⟨(belowCap_equivalence _).refl _,(belowCap_equivalence _).refl _⟩)
    rw [hfa,hfb] at hh
    rcases hh with hlow | hnew
    · exact Or.inl hlow
    · exact Or.inr ⟨hbridge,hnew⟩
  · have hh : collatzBelowCap H (f a) (f b) := by
      refine belowCap_lift (belowCap_equivalence H) f h ?_
      intro x y hx hy hxy
      rcases topEdge_cases (H:=H) (by omega) (by omega) hxy with h | h | h | h
      · have hfx : f x=x := if_neg (by omega)
        have hfy : f y=y := if_neg (by omega)
        rw [hfx,hfy]
        exact .rel _ _ ⟨h.1,h.2,hxy⟩
      · rw [h.1,h.2]
        exact (belowCap_equivalence _).refl _
      · have hfy : f y=y := if_neg (by omega)
        have htop : f H=v := by simp [f,h.2.2.1]
        rw [h.1,htop,hfy,h.2.2.2]
        exact (belowCap_equivalence _).refl _
      · have hfx : f x=x := if_neg (by omega)
        have hodd : H%2≠0 := by omega
        have htop : f H=u := by simp [f,hodd]
        rw [hfx,h.2.1,htop,h.2.2.2]
        exact (belowCap_equivalence _).refl _
    rw [hfa,hfb] at hh
    exact Or.inl hh

private theorem bridgeSteps {H : ℕ} (h : H%6=2) :
    runShortcut ((2*H-1)/3)=H ∧ runShortcut H=H/2 := by
  constructor
  · have hodd : ((2*H-1)/3)%2=1 := by omega
    rw [runShortcut,if_neg (by omega)]
    omega
  · rw [runShortcut,if_pos (by omega)]

private theorem belowCap_terminal_reached {H a s : ℕ} (hnext : H≤runShortcut s)
    (h : collatzBelowCap H a s) :
    ∃ t : ℕ, runShortcut^[t] a=s := by
  let reaches := fun x : ℕ => ∃ t : ℕ, runShortcut^[t] x=s
  have hR : Equivalence (fun x y => reaches x ↔ reaches y) :=
    ⟨fun _ => Iff.rfl,fun h => h.symm,fun h₁ h₂ => h₁.trans h₂⟩
  have how : reaches (id a) ↔ reaches (id s) := by
    refine belowCap_lift hR id h ?_
    intro x y _ hy hedge
    change reaches x ↔ reaches y
    constructor
    · rintro ⟨t,ht⟩
      cases t with
      | zero =>
        change x=s at ht
        rw [←hedge,ht] at hy
        omega
      | succ t => exact ⟨t,by simpa only [Function.iterate_succ_apply,hedge] using ht⟩
    · rintro ⟨t,ht⟩
      exact ⟨t+1,by rwa [Function.iterate_succ_apply,hedge]⟩
  exact how.mpr ⟨0,rfl⟩

private theorem shortcutIterate_ordinary (x t : ℕ) :
    ∃ j : ℕ, collatzStep^[j] x=runShortcut^[t] x := by
  induction t with
  | zero => exact ⟨0,rfl⟩
  | succ t ih =>
    obtain ⟨j,hj⟩ := ih
    obtain ⟨s,hs⟩ := runShortcut_reachable (runShortcut^[t] x)
    exact ⟨s+j,by rw [Function.iterate_add_apply,hj,hs,Function.iterate_succ_apply']⟩

/-- For the residue classes in the remaining frontier, a smaller merger
exists exactly when a single height links the two indicated sublevel components. -/
private theorem collatz_coalescence_iff_sublevel_bridge (n : ℕ)
    (hodd : n%2=1) (hmod : n%3≠2) :
    (∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k) ↔
      ∃ H k : ℕ, n<H ∧ 0<k ∧ k<n ∧ H%6=2 ∧
        (∀ j : ℕ, 0<j → j<n → ¬collatzBelowCap H n j) ∧
        ((collatzBelowCap H n ((2*H-1)/3) ∧ collatzBelowCap H (H/2) k) ∨
          (collatzBelowCap H n (H/2) ∧ collatzBelowCap H ((2*H-1)/3) k)) := by
  classical
  constructor
  · rintro ⟨k,a,b,hpos,hlt,hmeet⟩
    obtain ⟨cap,hcap⟩ := ordinaryCoal_in_some_cap (a:=n) (b:=k) ⟨a,b,hmeet⟩
    let Good := fun c : ℕ => n<c ∧ ∃ k : ℕ, 0<k ∧ k<n ∧ collatzBelowCap c n k
    have hex : ∃ c, Good c :=
      ⟨max (n+1) cap,(Nat.lt_succ_self n).trans_le (le_max_left _ _),
      k,hpos,hlt,belowCap_mono (le_max_right _ _) hcap⟩
    let c := Nat.find hex
    obtain ⟨hn,k,hpos,hlt,hc⟩ := Nat.find_spec hex
    change n<c at hn
    change collatzBelowCap c n k at hc
    let H := c-1
    have heq : H+1=c := by dsimp [H]; omega
    have hnH : n<H := by
      by_contra! hN
      have hc' : c=n+1 := by omega
      have hnk := topIsolated hodd hmod (hc' ▸ hc)
      have : k=n := hnk.mp rfl
      omega
    have hminimal (j : ℕ) (hj : 0<j) (hjn : j<n) (hconn : collatzBelowCap H n j) :
        False := by
      have hgood : Good H := ⟨hnH,j,hj,hjn,hconn⟩
      have hh : c≤H := Nat.find_min' hex hgood
      omega
    rw [←heq] at hc
    rcases topStep_decomposition hnH (by omega : k<H) hc with hlow | ⟨hbridge,hjoin⟩
    · exact (hminimal k hpos hlt hlow).elim
    · exact ⟨H,k,hnH,hpos,hlt,hbridge,hminimal,hjoin⟩
  · rintro ⟨H,k,_,hpos,hlt,hbridge,_,hlow⟩
    let u := (2*H-1)/3
    let v := H/2
    have steps := bridgeSteps hbridge
    have e1 : ordinaryCoal u H := by
      obtain ⟨t,ht⟩ := runShortcut_reachable u
      exact ⟨t,0,ht.trans steps.1⟩
    have e2 : ordinaryCoal H v := by
      obtain ⟨t,ht⟩ := runShortcut_reachable H
      exact ⟨t,0,ht.trans steps.2⟩
    have R := ordinaryCoal_equivalence
    have ek : ordinaryCoal n k := by
      rcases hlow with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact R.trans (belowCap_ordinaryCoal ha)
          (R.trans (R.trans e1 e2) (belowCap_ordinaryCoal hb))
      · exact R.trans (belowCap_ordinaryCoal ha)
          (R.trans (R.symm (R.trans e1 e2)) (belowCap_ordinaryCoal hb))
    obtain ⟨a,b,h⟩ := ek
    exact ⟨k,a,b,hpos,hlt,h⟩



/-- If the original orbit stays at or above its start, a first sublevel
bridge reaching a smaller component has height at least twice the start. -/
private theorem collatz_nondescending_coalescence_iff_high_bridge (n : ℕ)
    (hodd : n%2=1) (hmod : n%3≠2) (hstay : ∀ t : ℕ, n≤collatzStep^[t] n) :
    (∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k) ↔
      ∃ H k : ℕ, n<H ∧ 2*n≤H ∧ 0<k ∧ k<n ∧ H%6=2 ∧
        (∀ j : ℕ, 0<j → j<n → ¬collatzBelowCap H n j) ∧
        ((collatzBelowCap H n ((2*H-1)/3) ∧ collatzBelowCap H (H/2) k) ∨
          (collatzBelowCap H n (H/2) ∧ collatzBelowCap H ((2*H-1)/3) k)) := by
  rw [collatz_coalescence_iff_sublevel_bridge n hodd hmod]
  constructor
  · rintro ⟨H,k,hnH,hk,hkn,hmod,hminimal,hconn⟩
    refine ⟨H,k,hnH,?_,hk,hkn,hmod,hminimal,hconn⟩
    obtain ⟨hup,hdown⟩ := bridgeSteps hmod
    rcases hconn with ⟨hu, _⟩ | ⟨hv, _⟩
    · obtain ⟨t,ht⟩ := belowCap_terminal_reached (le_of_eq hup.symm) hu
      have hs : runShortcut^[t+2] n=H/2 := by
        rw [show t+2=(t+1)+1 by omega,Function.iterate_succ_apply',
          Function.iterate_succ_apply',ht,hup,hdown]
      obtain ⟨j,hj⟩ := shortcutIterate_ordinary n (t+2)
      have hj' : collatzStep^[j] n=H/2 := hj.trans hs
      have hlow := hstay j
      rw [hj'] at hlow
      omega
    · by_contra! hsmall
      have hlt : H/2<n := by omega
      exact hminimal (H/2) (by omega) hlt hv
  · rintro ⟨H,k,hnH,_,hk,hkn,hmod,hminimal,hconn⟩
    exact ⟨H,k,hnH,hk,hkn,hmod,hminimal,hconn⟩


theorem solution (n : ℕ)
    (hodd : n % 2 = 1) (hmod : n % 3 ≠ 2)
    (hstay : ∀ t : ℕ, n ≤ collatzStep^[t] n) :
    let shortcut : ℕ → ℕ := fun x =>
      if x % 2 = 0 then x / 2 else (3*x+1)/2
    let below : ℕ → ℕ → ℕ → Prop := fun H =>
      Relation.EqvGen (fun a b => a < H ∧ b < H ∧ shortcut a = b)
    (∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k) ↔
      ∃ H k : ℕ, n < H ∧ 2*n ≤ H ∧ 0 < k ∧ k < n ∧ H % 6 = 2 ∧
        (∀ j : ℕ, 0 < j → j < n → ¬ below H n j) ∧
        ((below H n ((2*H-1)/3) ∧ below H (H/2) k) ∨
          (below H n (H/2) ∧ below H ((2*H-1)/3) k)) := by
  exact collatz_nondescending_coalescence_iff_high_bridge n hodd hmod hstay
