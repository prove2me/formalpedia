-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:49:43.25319+00:00
-- url     : https://prove2.me/submissions/0e9a6f9b-5f17-423f-a8e4-a8f7e60af72d

import Theorems.Thm_SteinerShortcuts_Main_claim_3_1
import Theorems.Thm_SteinerShortcuts_Main_claim_3_3
import Theorems.Thm_SteinerShortcuts_Main_claim_3_5
import Definitions.Def_SteinerShortcuts_Main_TestFunctions
open SteinerShortcuts.Main
attribute [local instance] Classical.propDecidable
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

private def parLabel {q : ℕ} (odd : Bool) (P : CriticalData q) : Fin q :=
  if odd then P.a else P.b

private def parity (odd : Bool) (v : Point) : Prop :=
  if odd then v 0 % 2 = 1 else v 0 % 2 = 0

private noncomputable def psiV {q : ℕ} (odd : Bool) (P Q S : CriticalData q) (v : Point) : ℝ :=
  psi (v (if odd then 3 else 7)) (v (if odd then 1 else 2))
    (S.source (if odd then 3 else 7)) (parLabel odd S).val
    (parLabel odd P).val (parLabel odd Q).val

private theorem psi_step {q : ℕ} (odd : Bool) (P Q S : CriticalData q) (v : Point) (t : Fin q) :
    psiV odd P Q S (step q v t) = psiV odd P Q S v +
      if parity odd v then
        ((t.val:ℝ)-((parLabel odd S).val:ℝ)) /
          (((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ)) else 0 := by
  cases odd <;> by_cases ho : v 0 % 2 = 1
  all_goals have he : (v 0 % 2 = 0) ↔ ¬ (v 0 % 2 = 1) := by omega
  all_goals simp [psiV,parLabel,parity,psi,step,update,position,direction,ho,he]
  all_goals push_cast; ring

private theorem source_counters (L q : ℕ) (s : Point) (hs : s ∈ sources L q) :
    s 1 = 0 ∧ s 2 = 0 := by
  have hm := Fintype.mem_piFinset.mp hs
  have h1 := hm 1
  have h2 := hm 2
  norm_num [Fin.ext_iff] at h1 h2
  exact ⟨h1,h2⟩

private theorem critical_psi_zero (L q : ℕ) (odd : Bool) (P Q S : CriticalData q)
    (hs : S.Valid L) (i : ℕ) : psiV odd P Q S (criticalVertex q S.source S.a S.b i) = 0 := by
  have hs0 := source_layer L q S.source hs
  have hsc := source_counters L q S.source hs
  induction i with
  | zero => cases odd <;> simp [psiV,parLabel,psi,criticalVertex,hsc.1,hsc.2]
  | succ i ih =>
    rw [criticalVertex,psi_step,ih]
    have h0 := critical_layer q S.source S.a S.b i
    rw [hs0] at h0
    by_cases ho : i%2=0
    · have ho' : criticalVertex q S.source S.a S.b i 0 % 2 = 1 := by omega
      have he' : criticalVertex q S.source S.a S.b i 0 % 2 ≠ 0 := by omega
      cases odd <;> simp [parLabel,parity,ho,ho',he']
    · have ho' : criticalVertex q S.source S.a S.b i 0 % 2 ≠ 1 := by omega
      have he' : criticalVertex q S.source S.a S.b i 0 % 2 = 0 := by omega
      cases odd <;> simp [parLabel,parity,ho,ho',he']

private theorem seq_le (f : ℕ → ℝ) (N : ℕ) (hs : ∀ i < N, f i ≤ f (i+1))
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ N) : f i ≤ f j := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih => exact ih (by omega) |>.trans (hs j (by omega))

private theorem allowed_label (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (R : Route Point) (hl : Q1 P Q R) (i : ℕ) (hi : i < R.length)
    (t : Fin q) (ht : atV R (i+1) = step q (atV R i) t)
    (hp : parity odd (atV R i)) : t = parLabel odd P ∨ t = parLabel odd Q := by
  have hu : UsesLabel R i (parLabel odd P).val ∨ UsesLabel R i (parLabel odd Q).val := by
    cases odd
    · exact (hl i hi).2 ⟨atV R i,atV_some R i (by omega),hp⟩
    · exact (hl i hi).1 ⟨atV R i,atV_some R i (by omega),hp⟩
  rcases hu with hu | hu
  · left
    have hh := uses_atV R i _ hu
    rw [ht,step_label] at hh
    apply Fin.ext; exact_mod_cast hh
  · right
    have hh := uses_atV R i _ hu
    rw [ht,step_label] at hh
    apply Fin.ext; exact_mod_cast hh

private theorem par_denom_ne {q : ℕ} (odd : Bool) (P Q : CriticalData q)
    (hne : parLabel odd P ≠ parLabel odd Q) :
    ((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ) ≠ 0 := by
  intro he
  apply hne
  apply Fin.ext
  exact_mod_cast (sub_eq_zero.mp he).symm

private theorem psi_mono_step (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (R : Route Point) (hr : IsPath (construction L q) R) (hl : Q1 P Q R)
    (hne : parLabel odd P ≠ parLabel odd Q) (i : ℕ) (hi : i < R.length) :
    psiV odd P Q P (atV R i) ≤ psiV odd P Q P (atV R (i+1)) ∧
    psiV odd P Q Q (atV R (i+1)) ≤ psiV odd P Q Q (atV R i) := by
  obtain ⟨t,ht⟩ := route_step L q R hr i hi
  have hd := par_denom_ne odd P Q hne
  have hm : (((parLabel odd P).val:ℝ)-((parLabel odd Q).val:ℝ)) /
      (((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ)) = -1 := by
    field_simp; ring
  by_cases hp : parity odd (atV R i)
  · have ht' := allowed_label L q odd P Q R hl i hi t ht hp
    rw [ht,psi_step,psi_step]
    rcases ht' with rfl | rfl <;> simp [hp,hd,hm]
  · rw [ht,psi_step,psi_step]
    simp [hp]

private theorem cross_psi_nonneg (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hl : Q1 P Q R) (hne : parLabel odd P ≠ parLabel odd Q)
    (i : ℕ) (hi : i ≤ R.length) :
    0 ≤ psiV odd P Q P (atV R i) ∧ 0 ≤ psiV odd P Q Q (atV R i) := by
  have hzP : psiV odd P Q P (atV R 0) = 0 := by
    rw [atV_start,hr.2.1]
    exact critical_psi_zero L q odd P Q P hp 0
  have hzQ : psiV odd P Q Q (atV R R.length) = 0 := by
    rw [atV_finish,hr.2.2]
    change psiV odd P Q Q (critical L q Q.source Q.a Q.b).finish = 0
    rw [critical_finish]
    exact critical_psi_zero L q odd P Q Q hq (L-1)
  have hP := seq_le (fun i => psiV odd P Q P (atV R i)) R.length
    (fun i hi => (psi_mono_step L q odd P Q R hr.1 hl hne i hi).1) 0 i (by omega) hi
  have hQ := seq_le (fun i => -psiV odd P Q Q (atV R i)) R.length
    (fun i hi => neg_le_neg (psi_mono_step L q odd P Q R hr.1 hl hne i hi).2)
    i R.length hi (by omega)
  constructor <;> linarith

private noncomputable def Rtest {q : ℕ} (odd : Bool) (P Q : CriticalData q) : TestFunction q :=
  if odd then testROdd P Q else testREven P Q

private theorem Rtest_eq {q : ℕ} (odd : Bool) (P Q : CriticalData q) (v : Point) (t : Fin q) :
    Rtest odd P Q (position v) t =
      if parLabel odd P ≠ parLabel odd Q ∧ parity odd v then
        psiV odd P Q P v * psiV odd P Q Q v else 0 := by
  cases odd <;> simp [Rtest,testROdd,testREven,psiV,parLabel,parity,position]

private theorem Rtest_symm {q : ℕ} (odd : Bool) (P Q : CriticalData q) (v : Point) (t : Fin q) :
    Rtest odd Q P (position v) t = Rtest odd P Q (position v) t := by
  rw [Rtest_eq,Rtest_eq]
  by_cases hn : parLabel odd P = parLabel odd Q
  · simp [hn]
  · by_cases hp : parity odd v
    · simp only [ne_eq,hn,Ne.symm hn,hp,not_false_eq_true,and_self,ite_true]
      have hd : (((parLabel odd P).val:ℝ)-((parLabel odd Q).val:ℝ)) =
          -(((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ)) := by ring
      simp only [psiV,psi,hd,div_neg]
      ring
    · simp [hp]

private theorem critical_Rtest (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) :
    Vanishes (Rtest odd P Q) (P.route L) ∧ Vanishes (Rtest odd P Q) (Q.route L) := by
  constructor
  · apply vanishes_critical
    intro i hi
    rw [Rtest_eq]
    simp [critical_psi_zero L q odd P Q P hp i]
  · apply vanishes_critical
    intro i hi
    rw [Rtest_eq]
    simp [critical_psi_zero L q odd P Q Q hq i]

private theorem arc_atV (R : Route Point) (e : Point × Point) (he : e ∈ R.arcs) :
    ∃ i < R.length, e.1 = atV R i ∧ e.2 = atV R (i+1) := by
  obtain ⟨i,hi,hie⟩ := List.mem_iff_getElem.mp he
  have hir : i < R.length := by simpa [Route.arcs,Route.vertices,Route.length] using hi
  have hiv : i < R.vertices.length := by simp [Route.vertices,Route.length] at *;omega
  have hit : i < R.tail.length := hir
  have hf := congrArg Prod.fst hie
  have hs := congrArg Prod.snd hie
  simp only [Route.arcs,List.getElem_zip] at hf hs
  refine ⟨i,hir,?_,?_⟩
  · simpa [atV,List.getElem?_eq_getElem hiv] using hf.symm
  · simpa [atV,Route.vertices,List.getElem?_cons_succ,List.getElem?_eq_getElem hit] using hs.symm

private theorem cross_Rtest_nonneg (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hl : Q1 P Q R) (hne : parLabel odd P ≠ parLabel odd Q) :
    NonnegativeOn (Rtest odd P Q) R := by
  intro e he t ht
  obtain ⟨i,hi,hv,hw⟩ := arc_atV R e he
  have hn := cross_psi_nonneg L q odd P Q hp hq R hr hl hne i (by omega)
  rw [Rtest_eq,hv]
  split_ifs
  · exact mul_nonneg hn.1 hn.2
  · rfl

private theorem route_arc_atV (R : Route Point) (i : ℕ) (hi : i < R.length) :
    (atV R i,atV R (i+1)) ∈ R.arcs := by
  obtain ⟨v,w,hv,hw,he⟩ := route_edge R i hi
  simpa [atV,hv,hw] using he

private theorem route_step_of_label (L q : ℕ) (R : Route Point)
    (hr : IsPath (construction L q) R) (i : ℕ) (hi : i < R.length)
    (t : Fin q) (hu : UsesLabel R i t.val) :
    atV R (i+1) = step q (atV R i) t := by
  obtain ⟨s,hs⟩ := route_step L q R hr i hi
  have hl := uses_atV R i t.val hu
  rw [hs,step_label] at hl
  have hst : s = t := by apply Fin.ext; exact_mod_cast hl
  simpa [hst] using hs

private theorem ordered_of_vanish (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hl : Q1 P Q R) (hne : parLabel odd P ≠ parLabel odd Q)
    (hz : Vanishes (Rtest odd P Q) R) :
    LabelsOrdered R odd (parLabel odd P).val (parLabel odd Q).val := by
  intro i hi j hj hpar hui huj
  have hpi : parity odd (atV R i) := by
    cases odd <;> obtain ⟨v,hv,hp⟩ := hpar.1 <;> simpa [parity,atV,hv] using hp
  have hpj : parity odd (atV R j) := by
    cases odd <;> obtain ⟨v,hv,hp⟩ := hpar.2 <;> simpa [parity,atV,hv] using hp
  by_contra hnot
  have hji : j < i := by
    by_contra hnot'
    have he : j = i := by omega
    subst j
    have hli := uses_atV R i _ hui
    have hlj := uses_atV R i _ huj
    apply hne
    apply Fin.ext
    exact_mod_cast hli.symm.trans hlj
  have hd := par_denom_ne odd P Q hne
  have hm : (((parLabel odd P).val:ℝ)-((parLabel odd Q).val:ℝ)) /
      (((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ)) = -1 := by field_simp;ring
  have hfj : psiV odd P Q P (atV R (j+1)) = psiV odd P Q P (atV R j) + 1 := by
    rw [route_step_of_label L q R hr.1 j hj (parLabel odd Q) huj,psi_step]
    simp [hpj,hd]
  have hgi : psiV odd P Q Q (atV R (i+1)) = psiV odd P Q Q (atV R i) - 1 := by
    rw [route_step_of_label L q R hr.1 i hi (parLabel odd P) hui,psi_step]
    rw [if_pos hpi,hm]
    ring
  have hfj0 := (cross_psi_nonneg L q odd P Q hp hq R hr hl hne j (by omega)).1
  have hgi0 := (cross_psi_nonneg L q odd P Q hp hq R hr hl hne (i+1) (by omega)).2
  have hfm := seq_le (fun n => psiV odd P Q P (atV R n)) R.length
    (fun n hn => (psi_mono_step L q odd P Q R hr.1 hl hne n hn).1)
    (j+1) i (by omega) (by omega)
  have hfi : 0 < psiV odd P Q P (atV R i) := by linarith
  have hgi' : 0 < psiV odd P Q Q (atV R i) := by linarith
  obtain ⟨t,ht⟩ := route_step L q R hr.1 i hi
  have hh := hz (atV R i,atV R (i+1)) (route_arc_atV R i hi) t ht
  rw [Rtest_eq,if_pos ⟨hne,hpi⟩] at hh
  have hh' := mul_pos hfi hgi'
  linarith

 theorem solution (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    (P.a ≠ Q.a → LabelsOrdered R true P.a.val Q.a.val ∧
      LabelsOrdered T true Q.a.val P.a.val) ∧
    (P.b ≠ Q.b → LabelsOrdered R false P.b.val Q.b.val ∧
      LabelsOrdered T false Q.b.val P.b.val) := by
  have hlabs := claim_3_3 L q h P Q R T hs
  have f (odd : Bool) (hne : parLabel odd P ≠ parLabel odd Q) :
      LabelsOrdered R odd (parLabel odd P).val (parLabel odd Q).val ∧
      LabelsOrdered T odd (parLabel odd Q).val (parLabel odd P).val := by
    have hnR := cross_Rtest_nonneg L q odd P Q hs.1 hs.2.1 R hs.2.2.2.1 hlabs.1 hne
    have hnT' := cross_Rtest_nonneg L q odd Q P hs.2.1 hs.1 T hs.2.2.2.2 hlabs.2 (Ne.symm hne)
    have hnT : NonnegativeOn (Rtest odd P Q) T := by
      intro e he t ht
      rw [← Rtest_symm odd P Q e.1 t]
      exact hnT' e he t ht
    have hlin : T3prime L q (Rtest odd P Q) := by
      cases odd
      · exact (claim_3_5 L q h P Q R T hs).2 hne
      · exact (claim_3_5 L q h P Q R T hs).1 hne
    have hz := claim_3_1 L q h P Q R T hs (Rtest odd P Q) ⟨hnR,hnT⟩
      (critical_Rtest L q odd P Q hs.1 hs.2.1) hlin
    have hzT : Vanishes (Rtest odd Q P) T := by
      intro e he t ht
      rw [Rtest_symm odd P Q e.1 t]
      exact hz.2 e he t ht
    exact ⟨ordered_of_vanish L q odd P Q hs.1 hs.2.1 R hs.2.2.2.1 hlabs.1 hne hz.1,
      ordered_of_vanish L q odd Q P hs.2.1 hs.1 T hs.2.2.2.2 hlabs.2 (Ne.symm hne) hzT⟩
  exact ⟨fun ha => f true ha,fun hb => f false hb⟩
