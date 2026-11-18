-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_2_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:34:40.167362+00:00
-- url     : https://prove2.me/submissions/28f3bb91-17a1-4b6c-846f-390d5a5f4c1e

import Theorems.Thm_SteinerShortcuts_Main_claim_3_3
import Theorems.Thm_SteinerShortcuts_Main_equation_11
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

private theorem chain_reaches {V : Type} (G : Digraph V) (a : V) (l : List V)
    (hc : (a::l).IsChain G.Adj) : Reaches G a (l.getLastD a) := by
  induction l generalizing a with
  | nil => exact .refl
  | cons b l ih =>
    have hh := List.isChain_cons_cons.mp hc
    have hh' := Relation.ReflTransGen.head hh.1 (ih b hh.2)
    simpa only [List.getLastD_cons, Reaches] using hh'

private theorem route_ext {V : Type} (R S : Route V) (he : R.vertices = S.vertices) : R = S := by
  cases R with | mk a l =>
    cases S with | mk b m =>
      simp only [Route.vertices,List.cons.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      rfl

 theorem solution (L q : ℕ) (h : Admissible L q) :
    P1 (construction L q) (criticalPaths L q) := by
  obtain ⟨c,C,hc,hcC,hall⟩ := equation_11
  obtain ⟨_,_,_,_,_,_,hpaths,_⟩ := hall L q h
  intro C hC
  have hvalid := (hpaths C hC).1
  refine ⟨hvalid,?_⟩
  intro R hR hstart hend
  obtain ⟨sab,hsab,rfl⟩ := Finset.mem_image.mp hC
  let S : CriticalData q := ⟨sab.1,sab.2.1,sab.2.2⟩
  have hS : S.Valid L := (Finset.mem_product.mp hsab).1
  change R = S.route L
  change IsPath (construction L q) (S.route L) at hvalid
  have hreach := chain_reaches (construction L q) (S.route L).start (S.route L).tail hvalid
  have hcross : IsCrossPath (construction L q) (S.route L) (S.route L) R := ⟨hR,hstart,hend⟩
  have hs : PairSetup L q S S R (S.route L) :=
    ⟨hS,hS,⟨hreach,hreach⟩,hcross,⟨hvalid,rfl,rfl⟩⟩
  have hlabs := (claim_3_3 L q h S S R (S.route L) hs).1
  have hf : ∀ i < R.length, Follows S R i := by
    intro i hi
    exact ⟨fun ho => ((hlabs i hi).1 ho).elim id id,
      fun he => ((hlabs i hi).2 he).elim id id⟩
  have hlen := cross_length L q S S hS hS R hcross
  have hs0 : R.start 0 = 1 := by rw [hstart]; exact source_layer L q S.source hS
  have hpref : ∀ i, i ≤ R.length → atV R i = criticalVertex q S.source S.a S.b i := by
    intro i hi
    induction i with
    | zero => simpa [atV_start,criticalVertex,CriticalData.route,critical] using hstart
    | succ i ih =>
      have ih := ih (by omega)
      rw [follows_step L q S R hR hs0 i (by omega) (hf i (by omega)),ih]
      rfl
  apply route_ext
  apply List.ext_getElem?
  intro i
  have hvlen (P : Route Point) : P.vertices.length = P.length+1 := by simp [Route.vertices,Route.length]
  have hlenS : (S.route L).length = R.length := by simp [CriticalData.route,critical_length,hlen]
  by_cases hi : i ≤ R.length
  · rw [atV_some R i hi,atV_some (S.route L) i (by omega),hpref i hi]
    congr 1
    exact (critical_atV L q S.source S.a S.b i (by omega)).symm
  · have hRnone : R.vertices[i]? = none := List.getElem?_eq_none_iff.mpr (by rw [hvlen];omega)
    have hSnone : (S.route L).vertices[i]? = none := List.getElem?_eq_none_iff.mpr (by rw [hvlen,hlenS];omega)
    rw [hRnone,hSnone]
