-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:31:22.713945+00:00
-- url     : https://prove2.me/submissions/542dadba-09bf-4613-ab5b-49c99b9ebc7b

import Definitions.Def_SteinerShortcuts_Main_TestFunctions
open SteinerShortcuts.Main
set_option maxRecDepth 4000

 theorem step_label (q : ℕ) (v : Point) (t : Fin q) :
    edgeLabel v (step q v t) = (t.val : ℤ) := by
  by_cases ho : v 0 % 2 = 1
  · simp [edgeLabel, step, update, position, direction, ho]
  · simp [edgeLabel, step, update, position, direction, ho]

 theorem step_label_injective (q : ℕ) (v : Point) (a b : Fin q)
    (he : step q v a = step q v b) : a = b := by
  have hh := congrArg (edgeLabel v) he
  rw [step_label, step_label] at hh
  apply Fin.ext
  exact_mod_cast hh

 theorem critical_layer (q : ℕ) (s : Point) (a b : Fin q) (i : ℕ) :
    criticalVertex q s a b i 0 = s 0 + (i : ℤ) := by
  induction i with
  | zero => simp [criticalVertex]
  | succ i ih => simp [criticalVertex, step, update, ih]; ring

private theorem chain_zip {V : Type} (r : V → V → Prop) (a : V) (l : List V) :
    (a::l).IsChain r ↔ ∀ e ∈ (a::l).zip l, r e.1 e.2 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [List.isChain_cons_cons, ih]

 theorem critical_arcs (L q : ℕ) (s : Point) (a b : Fin q)
    (e : Point × Point) (he : e ∈ (critical L q s a b).arcs) :
    ∃ i < L-1, e.1 = criticalVertex q s a b i ∧
      e.2 = criticalVertex q s a b (i+1) := by
  let f := criticalVertex q s a b
  have hc : ((List.range (L-1+1)).map f).IsChain
      (fun v w => ∃ i < L-1, v = f i ∧ w = f (i+1)) := by
    rw [List.isChain_map, List.isChain_range_succ]
    intro i hi
    exact ⟨i,hi,rfl,rfl⟩
  have heq : (critical L q s a b).vertices = (List.range (L-1+1)).map f := by
    simp [Route.vertices, critical, List.range_succ_eq_map, List.map_map, f,
      Function.comp_def, criticalVertex]
  rw [← heq] at hc
  exact (chain_zip _ _ _).mp hc e he

 theorem vanishes_critical (L q : ℕ) (s : Point) (a b : Fin q) (F : TestFunction q)
    (hf : ∀ i < L-1, F (position (criticalVertex q s a b i))
      (if i%2=0 then a else b) = 0) : Vanishes F (critical L q s a b) := by
  intro e he t ht
  obtain ⟨i,hi,hv,hw⟩ := critical_arcs L q s a b e he
  have he : step q e.1 t = step q e.1 (if i%2=0 then a else b) := by
    rw [← ht, hv, hw]
    rfl
  have hlabel := step_label_injective q e.1 t _ he
  rw [hlabel,hv]
  exact hf i hi


open SteinerShortcuts.Main
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

 theorem step_source_injective (q : ℕ) (t : Fin q) :
    Function.Injective (fun v : Point => step q v t) := by
  intro v w he
  have h0 : v 0 = w 0 := by
    have hh := congrFun he 0
    simpa [step,update] using hh
  have hp : position v = position w := by
    ext i
    have hh := congrFun he ⟨i.val,by omega⟩
    by_cases ho : w 0 % 2 = 1 <;>
      fin_cases i <;> simp [step, update, position, h0, ho] at hh ⊢ <;> omega
  change v + update q (position v) t = w + update q (position w) t at he
  rw [hp] at he
  exact add_right_cancel he


open SteinerShortcuts.Main

 def atV {V : Type} (R : Route V) (i : ℕ) : V := R.vertices[i]?.getD R.start

 theorem atV_some {V : Type} (R : Route V) (i : ℕ) (hi : i ≤ R.length) :
    R.vertices[i]? = some (atV R i) := by
  have hh : i < R.vertices.length := by simp [Route.vertices,Route.length] at *; omega
  simp [atV, List.getElem?_eq_getElem hh]

 theorem atV_start {V : Type} (R : Route V) : atV R 0 = R.start := by
  simp [atV,Route.vertices]

 theorem atV_finish {V : Type} (R : Route V) : atV R R.length = R.finish := by
  have hi : R.length = R.vertices.length-1 := by simp [Route.vertices,Route.length]
  unfold atV
  rw [hi, ← List.getLast?_eq_getElem?]
  change R.vertices.getLastD R.start = R.finish
  simp only [Route.vertices,Route.finish,List.getLastD_cons]

 theorem critical_vertices (L q : ℕ) (s : Point) (a b : Fin q) :
    (critical L q s a b).vertices = (List.range (L-1+1)).map (criticalVertex q s a b) := by
  simp [Route.vertices, critical, List.range_succ_eq_map, List.map_map,
    Function.comp_def, criticalVertex]

 theorem critical_atV (L q : ℕ) (s : Point) (a b : Fin q) (i : ℕ) (hi : i ≤ L-1) :
    atV (critical L q s a b) i = criticalVertex q s a b i := by
  simp [atV, critical_vertices, List.getElem?_range, show i < L-1+1 by omega]

 theorem critical_length (L q : ℕ) (s : Point) (a b : Fin q) :
    (critical L q s a b).length = L-1 := by simp [Route.length,critical]

private theorem route_edge (R : Route Point) (i : ℕ) (hi : i < R.length) :
    ∃ v w, R.vertices[i]? = some v ∧ R.vertices[i+1]? = some w ∧ (v,w) ∈ R.arcs := by
  have hiv : i < R.vertices.length := by simpa [Route.vertices, Route.length] using Nat.lt_succ_of_lt hi
  have hit : i < R.tail.length := hi
  have hia : i < R.arcs.length := by simpa [Route.arcs, Route.vertices, Route.length] using hi
  refine ⟨R.vertices[i], R.tail[i], List.getElem?_eq_getElem hiv, ?_, ?_⟩
  · simpa only [Route.vertices, List.getElem?_cons_succ] using List.getElem?_eq_getElem hit
  · have hm := List.getElem_mem hia
    simpa only [Route.arcs, List.getElem_zip] using hm

private theorem route_step (L q : ℕ) (R : Route Point) (hp : IsPath (construction L q) R)
    (i : ℕ) (hi : i < R.length) :
    ∃ t : Fin q, atV R (i+1) = step q (atV R i) t := by
  obtain ⟨v,w,hv,hw,he⟩ := route_edge R i hi
  have ha := (chain_zip _ _ _).mp hp (v,w) he
  obtain ⟨_,_,_,t,ht⟩ := ha
  refine ⟨t,?_⟩
  simpa [atV,hv,hw] using ht

private theorem route_layer (L q : ℕ) (R : Route Point) (hp : IsPath (construction L q) R)
    (i : ℕ) (hi : i ≤ R.length) : atV R i 0 = R.start 0 + (i:ℤ) := by
  induction i with
  | zero => simp [atV_start]
  | succ i ih =>
    have ih := ih (by omega)
    obtain ⟨t,ht⟩ := route_step L q R hp i (by omega)
    rw [ht]
    simp [step,update,ih]
    ring

private theorem source_layer (L q : ℕ) (s : Point) (hs : s ∈ sources L q) : s 0 = 1 := by
  have hh := Fintype.mem_piFinset.mp hs 0
  simpa [layerBox] using hh

private theorem critical_finish (L q : ℕ) (s : Point) (a b : Fin q) :
    (critical L q s a b).finish = criticalVertex q s a b (L-1) := by
  rw [← atV_finish,critical_length,critical_atV L q s a b (L-1) (by omega)]

private theorem cross_length (L q : ℕ) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R) :
    R.length = L-1 := by
  have hh := route_layer L q R hr.1 R.length (by omega)
  rw [atV_finish, hr.2.1,hr.2.2] at hh
  change (critical L q Q.source Q.a Q.b).finish 0 = P.source 0 + (R.length:ℤ) at hh
  rw [critical_finish, critical_layer, source_layer L q P.source hp,
    source_layer L q Q.source hq] at hh
  omega

private theorem uses_atV (R : Route Point) (i : ℕ) (t : ℤ) (hu : UsesLabel R i t) :
    edgeLabel (atV R i) (atV R (i+1)) = t := by
  obtain ⟨v,w,hv,hw,he⟩ := hu
  simpa [atV,hv,hw] using he

private theorem follows_step (L q : ℕ) (P : CriticalData q) (R : Route Point)
    (hr : IsPath (construction L q) R) (hs : R.start 0 = 1)
    (i : ℕ) (hi : i < R.length) (hf : Follows P R i) :
    atV R (i+1) = step q (atV R i) (if i%2=0 then P.a else P.b) := by
  obtain ⟨t,ht⟩ := route_step L q R hr i hi
  have h0 := route_layer L q R hr i (by omega)
  rw [hs] at h0
  have hl : edgeLabel (atV R i) (atV R (i+1)) = (t.val:ℤ) := by rw [ht,step_label]
  by_cases ho : i%2=0
  · have ho' : atV R i 0 % 2 = 1 := by omega
    have hu := uses_atV R i P.a.val (hf.1 ⟨atV R i, atV_some R i (by omega),ho'⟩)
    have hta : t = P.a := by apply Fin.ext; exact_mod_cast hl.symm.trans hu
    simpa [ho,hta] using ht
  · have ho' : atV R i 0 % 2 = 0 := by omega
    have hu := uses_atV R i P.b.val (hf.2 ⟨atV R i, atV_some R i (by omega),ho'⟩)
    have hta : t = P.b := by apply Fin.ext; exact_mod_cast hl.symm.trans hu
    simpa [ho,hta] using ht

 theorem solution (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T)
    (hq1 : Q1 P Q R) (hq2 : Q2 P Q R) (hq3 : Q3 P Q R) :
    Splices (P.route L) (Q.route L) R := by
  have hR := hs.2.2.2.1
  have hlen := cross_length L q P Q hs.1 hs.2.1 R hR
  have hs0 : R.start 0 = 1 := by
    rw [hR.2.1]
    exact source_layer L q P.source hs.1
  obtain ⟨j,hj,hbefore,hafter⟩ := hq3
  have hpref : ∀ i, i ≤ j → atV R i = criticalVertex q P.source P.a P.b i := by
    intro i hi
    induction i with
    | zero => simpa [atV_start,criticalVertex,CriticalData.route,critical] using hR.2.1
    | succ i ih =>
      have ih := ih (by omega)
      rw [follows_step L q P R hR.1 hs0 i (by omega) (hbefore i (by omega)),ih]
      rfl
  have hsuffix : ∀ d i, d+i=R.length → j ≤ i →
      atV R i = criticalVertex q Q.source Q.a Q.b i := by
    intro d
    induction d with
    | zero =>
      intro i hi hji
      have hi : i = R.length := by omega
      subst i
      rw [atV_finish,hR.2.2]
      change (critical L q Q.source Q.a Q.b).finish = _
      rw [critical_finish,hlen]
    | succ d ih =>
      intro i hi hji
      have hnext := ih (i+1) (by omega) (by omega)
      have hstep := follows_step L q Q R hR.1 hs0 i (by omega) (hafter i hji (by omega))
      apply step_source_injective q (if i%2=0 then Q.a else Q.b)
      exact hstep.symm.trans hnext
  have hsuf : ∀ i, j ≤ i → i ≤ R.length → atV R i = criticalVertex q Q.source Q.a Q.b i := by
    intro i hji hi
    exact hsuffix (R.length-i) i (by omega) hji
  have hlenP : (P.route L).length = R.length := by simp [CriticalData.route,critical_length,hlen]
  have hlenQ : (Q.route L).length = R.length := by simp [CriticalData.route,critical_length,hlen]
  have hvlen (S : Route Point) : S.vertices.length = S.length+1 := by simp [Route.vertices,Route.length]
  have hidxP : ∀ i, i ≤ R.length → atV (P.route L) i = criticalVertex q P.source P.a P.b i := by
    intro i hi; exact critical_atV L q P.source P.a P.b i (by omega)
  have hidxQ : ∀ i, i ≤ R.length → atV (Q.route L) i = criticalVertex q Q.source Q.a Q.b i := by
    intro i hi; exact critical_atV L q Q.source Q.a Q.b i (by omega)
  refine ⟨j,j,by rw [hvlen,hlenP]; omega,by rw [hvlen,hlenQ]; omega,?_,?_⟩
  · rw [atV_some _ j (by omega),atV_some _ j (by omega),hidxP j hj,hidxQ j hj]
    congr 1
    exact (hpref j (by omega)).symm.trans (hsuf j (by omega) hj)
  · apply List.ext_getElem?
    intro i
    have htake : ((P.route L).vertices.take (j+1)).length = j+1 := by
      rw [List.length_take,hvlen,hlenP,Nat.min_eq_left (by omega)]
    by_cases hij : i ≤ j
    · rw [List.getElem?_append_left (by omega : i < ((P.route L).vertices.take (j+1)).length)]
      rw [List.getElem?_take]
      simp only [show i < j+1 by omega,↓reduceIte]
      rw [atV_some R i (by omega),atV_some (P.route L) i (by omega),hidxP i (by omega)]
      exact congrArg some (hpref i hij)
    · rw [List.getElem?_append_right (by omega : ((P.route L).vertices.take (j+1)).length ≤ i)]
      rw [htake,List.getElem?_drop,show j+1+(i-(j+1)) = i by omega]
      by_cases hin : i ≤ R.length
      · rw [atV_some R i hin,atV_some (Q.route L) i (by omega),hidxQ i hin]
        exact congrArg some (hsuf i (by omega) hin)
      · have hRnone : R.vertices[i]? = none := List.getElem?_eq_none_iff.mpr (by rw [hvlen];omega)
        have hQnone : (Q.route L).vertices[i]? = none := List.getElem?_eq_none_iff.mpr (by rw [hvlen,hlenQ];omega)
        rw [hRnone,hQnone]
