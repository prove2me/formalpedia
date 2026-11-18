-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:03:09.565836+00:00
-- url     : https://prove2.me/submissions/306f8974-4bbb-4666-a5da-515952d750f4

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

private def counterV (odd : Bool) (v : Point) : ℤ := if odd then v 1 else v 2

private noncomputable def tauPar {q : ℕ} (odd : Bool) (P Q : CriticalData q) : ℝ :=
  ((P.source (if odd then 3 else 7):ℝ)-(Q.source (if odd then 3 else 7):ℝ)) /
    (((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ))

private theorem psi_difference {q : ℕ} (odd : Bool) (P Q : CriticalData q)
    (hne : parLabel odd P ≠ parLabel odd Q) (v : Point) :
    psiV odd P Q P v - psiV odd P Q Q v = (counterV odd v:ℝ)-tauPar odd P Q := by
  have hd := par_denom_ne odd P Q hne
  unfold psiV psi counterV tauPar
  field_simp
  cases odd <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

private theorem psi_source_Q (L q : ℕ) (odd : Bool) (P Q : CriticalData q) (hp : P.Valid L) :
    psiV odd P Q Q P.source = tauPar odd P Q := by
  have hc := source_counters L q P.source hp
  cases odd <;> simp [psiV,psi,parLabel,tauPar,hc.1,hc.2]

private theorem psi_step_choices (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (R : Route Point) (hr : IsPath (construction L q) R) (hl : Q1 P Q R)
    (hne : parLabel odd P ≠ parLabel odd Q) (i : ℕ) (hi : i < R.length) :
    (psiV odd P Q P (atV R (i+1)) = psiV odd P Q P (atV R i) ∨
      psiV odd P Q P (atV R (i+1)) = psiV odd P Q P (atV R i)+1) ∧
    (psiV odd P Q Q (atV R i) = psiV odd P Q Q (atV R (i+1)) ∨
      psiV odd P Q Q (atV R i) = psiV odd P Q Q (atV R (i+1))+1) := by
  obtain ⟨t,ht⟩ := route_step L q R hr i hi
  have hd := par_denom_ne odd P Q hne
  have hm : (((parLabel odd P).val:ℝ)-((parLabel odd Q).val:ℝ)) /
      (((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ)) = -1 := by field_simp;ring
  by_cases hp : parity odd (atV R i)
  · have ht' := allowed_label L q odd P Q R hl i hi t ht hp
    rw [ht,psi_step,psi_step]
    rcases ht' with rfl | rfl <;> simp [hp,hd,hm]
  · rw [ht,psi_step,psi_step]
    simp [hp]

private theorem psiQ_finish_zero (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R) :
    psiV odd P Q Q (atV R R.length) = 0 := by
  rw [atV_finish,hr.2.2]
  change psiV odd P Q Q (critical L q Q.source Q.a Q.b).finish = 0
  rw [critical_finish]
  exact critical_psi_zero L q odd P Q Q hq (L-1)

private theorem tau_nat (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hl : Q1 P Q R) (hne : parLabel odd P ≠ parLabel odd Q) :
    ∃ n : ℕ, tauPar odd P Q = (n:ℝ) := by
  have f : ∀ d i, d+i=R.length → ∃ n : ℕ, psiV odd P Q Q (atV R i) = (n:ℝ) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hi : i=R.length := by omega
      subst i
      exact ⟨0,by simpa using psiQ_finish_zero L q odd P Q hq R hr⟩
    | succ d ih =>
      intro i hi
      obtain ⟨n,hn⟩ := ih (i+1) (by omega)
      have hh := (psi_step_choices L q odd P Q R hr.1 hl hne i (by omega)).2
      rcases hh with hh | hh
      · exact ⟨n,hh.trans hn⟩
      · refine ⟨n+1,?_⟩
        rw [hh,hn,Nat.cast_add,Nat.cast_one]
  obtain ⟨n,hn⟩ := f R.length 0 (by omega)
  rw [atV_start,hr.2.1] at hn
  refine ⟨n,?_⟩
  change psiV odd P Q Q P.source = (n:ℝ) at hn
  rw [psi_source_Q L q odd P Q hp] at hn
  exact hn

private theorem psi_product_zero (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hne : parLabel odd P ≠ parLabel odd Q) (hz : Vanishes (Rtest odd P Q) R)
    (i : ℕ) (hi : i ≤ R.length) :
    psiV odd P Q P (atV R i) * psiV odd P Q Q (atV R i) = 0 := by
  have f : ∀ d i, d+i=R.length →
      psiV odd P Q P (atV R i) * psiV odd P Q Q (atV R i) = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hi : i=R.length := by omega
      subst i
      rw [psiQ_finish_zero L q odd P Q hq R hr,mul_zero]
    | succ d ih =>
      intro i hi
      obtain ⟨t,ht⟩ := route_step L q R hr.1 i (by omega)
      by_cases hpar : parity odd (atV R i)
      · have hh := hz (atV R i,atV R (i+1)) (route_arc_atV R i (by omega)) t ht
        rw [Rtest_eq,if_pos ⟨hne,hpar⟩] at hh
        exact hh
      · have hh := ih (i+1) (by omega)
        rw [ht,psi_step,psi_step] at hh
        simpa [hpar] using hh
  exact f (R.length-i) i (by omega)

private theorem psi_values (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hl : Q1 P Q R) (hne : parLabel odd P ≠ parLabel odd Q)
    (hz : Vanishes (Rtest odd P Q) R) (i : ℕ) (hi : i ≤ R.length) :
    psiV odd P Q P (atV R i) = max ((counterV odd (atV R i):ℝ)-tauPar odd P Q) 0 ∧
    psiV odd P Q Q (atV R i) = max (tauPar odd P Q-(counterV odd (atV R i):ℝ)) 0 := by
  have hn := cross_psi_nonneg L q odd P Q hp hq R hr hl hne i hi
  have hd := psi_difference odd P Q hne (atV R i)
  have hh := psi_product_zero L q odd P Q hq R hr hne hz i hi
  rcases mul_eq_zero.mp hh with hh | hh
  · rw [hh] at hd
    rw [max_eq_right (by linarith),max_eq_left (by linarith)]
    constructor <;> linarith
  · rw [hh] at hd
    rw [max_eq_left (by linarith),max_eq_right (by linarith)]
    constructor <;> linarith

private def counterAt (odd : Bool) (i : ℕ) : ℕ := if odd then (i+1)/2 else i/2

private theorem cross_counter (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (i : ℕ) (hi : i ≤ R.length) : counterV odd (atV R i) = (counterAt odd i : ℤ) := by
  have hs0 : R.start 0 = 1 := by rw [hr.2.1];exact source_layer L q P.source hp
  have hs1 : R.start 1 = 0 := by rw [hr.2.1];exact (source_counters L q P.source hp).1
  have hs2 : R.start 2 = 0 := by rw [hr.2.1];exact (source_counters L q P.source hp).2
  have f : ∀ i, i ≤ R.length → atV R i 1 = ((i:ℤ)+1)/2 ∧ atV R i 2 = (i:ℤ)/2 := by
    intro i hi
    induction i with
    | zero => simp [atV_start,hs1,hs2]
    | succ i ih =>
      have ih := ih (by omega)
      obtain ⟨t,ht⟩ := route_step L q R hr.1 i (by omega)
      have h0 := route_layer L q R hr.1 i (by omega)
      rw [hs0] at h0
      rw [ht]
      by_cases ho : (1+(i:ℤ))%2=1 <;>
        simp [step,update,position,h0,ho,ih] <;> omega
  have hh := f i hi
  cases odd <;> simp [counterV,counterAt,Int.natCast_ediv,Nat.cast_add,hh]

private theorem cross_parity (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (i : ℕ) (hi : i ≤ R.length) :
    parity odd (atV R i) ↔ (if odd then i%2=0 else i%2=1) := by
  have hh := route_layer L q R hr.1 i hi
  have hs0 : R.start 0 = 1 := by rw [hr.2.1];exact source_layer L q P.source hp
  rw [hs0] at hh
  cases odd <;> simp only [parity,Bool.false_eq_true,↓reduceIte] <;> omega

private theorem tau_nat_bounds (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hl : Q1 P Q R) (hne : parLabel odd P ≠ parLabel odd Q) :
    ∃ n : ℕ, n ≤ counterAt odd R.length ∧ tauPar odd P Q = (n:ℝ) := by
  obtain ⟨n,hn⟩ := tau_nat L q odd P Q hp hq R hr hl hne
  have hd := psi_difference odd P Q hne (atV R R.length)
  rw [cross_counter L q odd P Q hp R hr R.length (by omega),hn,
    psiQ_finish_zero L q odd P Q hq R hr] at hd
  have hh := (cross_psi_nonneg L q odd P Q hp hq R hr hl hne R.length (by omega)).1
  refine ⟨n,?_,hn⟩
  exact_mod_cast (show (n:ℝ) ≤ (counterAt odd R.length:ℝ) by push_cast at hd;linarith)

private theorem phase_direction (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hl : Q1 P Q R) (hne : parLabel odd P ≠ parLabel odd Q)
    (hz : Vanishes (Rtest odd P Q) R) (n : ℕ) (hn : tauPar odd P Q = (n:ℝ))
    (i : ℕ) (hi : i < R.length) (hpar : parity odd (atV R i))
    (t : Fin q) (ht : atV R (i+1) = step q (atV R i) t) :
    t = if counterAt odd i < n then parLabel odd P else parLabel odd Q := by
  have hd := par_denom_ne odd P Q hne
  have hm : (((parLabel odd P).val:ℝ)-((parLabel odd Q).val:ℝ)) /
      (((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ)) = -1 := by field_simp;ring
  have hcur := cross_psi_nonneg L q odd P Q hp hq R hr hl hne i (by omega)
  have hnxt := cross_psi_nonneg L q odd P Q hp hq R hr hl hne (i+1) (by omega)
  have hdiff := psi_difference odd P Q hne (atV R i)
  rw [cross_counter L q odd P Q hp R hr i (by omega),hn] at hdiff
  push_cast at hdiff
  have hpz := psi_product_zero L q odd P Q hq R hr hne hz i (by omega)
  have hnz := psi_product_zero L q odd P Q hq R hr hne hz (i+1) (by omega)
  have hchoice := allowed_label L q odd P Q R hl i hi t ht hpar
  rcases hchoice with rfl | rfl
  · have hstep : psiV odd P Q Q (atV R (i+1)) = psiV odd P Q Q (atV R i)-1 := by
      rw [ht,psi_step,if_pos hpar,hm];ring
    have hgpos : 0 < psiV odd P Q Q (atV R i) := by linarith
    have hfp : psiV odd P Q P (atV R i) = 0 := (mul_eq_zero.mp hpz).resolve_right (ne_of_gt hgpos)
    have hlt : counterAt odd i < n := by
      exact_mod_cast (show (counterAt odd i:ℝ) < (n:ℝ) by linarith)
    simp [hlt]
  · have hstepP : psiV odd P Q P (atV R (i+1)) = psiV odd P Q P (atV R i)+1 := by
      rw [ht,psi_step,if_pos hpar];simp [hd]
    have hstepQ : psiV odd P Q Q (atV R (i+1)) = psiV odd P Q Q (atV R i) := by
      rw [ht,psi_step,if_pos hpar];simp
    have hfpos : 0 < psiV odd P Q P (atV R (i+1)) := by linarith
    have hgq : psiV odd P Q Q (atV R (i+1)) = 0 := (mul_eq_zero.mp hnz).resolve_left (ne_of_gt hfpos)
    have hge : n ≤ counterAt odd i := by
      exact_mod_cast (show (n:ℝ) ≤ (counterAt odd i:ℝ) by linarith)
    simp [show ¬ counterAt odd i < n by omega]

private theorem psiV_swap {q : ℕ} (odd : Bool) (P Q S : CriticalData q) (v : Point) :
    psiV odd Q P S v = -psiV odd P Q S v := by
  have hd : (((parLabel odd P).val:ℝ)-((parLabel odd Q).val:ℝ)) =
      -(((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ)) := by ring
  unfold psiV psi
  rw [hd]
  simp only [div_neg]

private theorem tauPar_swap {q : ℕ} (odd : Bool) (P Q : CriticalData q) :
    tauPar odd Q P = tauPar odd P Q := by
  have hd : (((parLabel odd P).val:ℝ)-((parLabel odd Q).val:ℝ)) =
      -(((parLabel odd Q).val:ℝ)-((parLabel odd P).val:ℝ)) := by ring
  have hx : ((Q.source (if odd then 3 else 7):ℝ)-(P.source (if odd then 3 else 7):ℝ)) =
      -((P.source (if odd then 3 else 7):ℝ)-(Q.source (if odd then 3 else 7):ℝ)) := by ring
  unfold tauPar
  rw [hd,hx]
  simp only [neg_div_neg_eq]

private theorem S_eq {q : ℕ} (P Q : CriticalData q) (v : Point) (t : Fin q) :
    testS P Q (position v) t =
      if P.a ≠ Q.a ∧ P.b ≠ Q.b ∧ parity true v then
        (tauPar false P Q-tauPar true P Q) *
          (((t.val:ℝ)-(P.a.val:ℝ))/((Q.a.val:ℝ)-(P.a.val:ℝ))) * psiV false P Q Q v else 0 := by
  simp [testS,position,parity,psiV,parLabel,tauPar,tauEven,tauOdd] <;> rfl

private theorem S_critical (L q : ℕ) (P Q : CriticalData q) (hp : P.Valid L) (hq : Q.Valid L) :
    Vanishes (testS P Q) (P.route L) ∧ Vanishes (testS P Q) (Q.route L) := by
  constructor
  · apply vanishes_critical
    intro i hi
    rw [S_eq]
    have h0 := critical_layer q P.source P.a P.b i
    rw [source_layer L q P.source hp] at h0
    by_cases ho : i%2=0
    · simp [ho]
    · have ho' : ¬ parity true (criticalVertex q P.source P.a P.b i) := by
        change criticalVertex q P.source P.a P.b i 0 % 2 ≠ 1
        omega
      simp [ho']
  · apply vanishes_critical
    intro i hi
    rw [S_eq]
    simp [critical_psi_zero L q false P Q Q hq i]

private theorem phase_uses (L q : ℕ) (odd : Bool) (P Q : CriticalData q)
    (hp : P.Valid L) (hq : Q.Valid L) (R : Route Point)
    (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (hl : Q1 P Q R) (hne : parLabel odd P ≠ parLabel odd Q)
    (hz : Vanishes (Rtest odd P Q) R) (n : ℕ) (hn : tauPar odd P Q = (n:ℝ))
    (i : ℕ) (hi : i < R.length) (hpar : parity odd (atV R i)) :
    UsesLabel R i (if counterAt odd i < n then ((parLabel odd P).val:ℤ) else ((parLabel odd Q).val:ℤ)) := by
  obtain ⟨t,ht⟩ := route_step L q R hr.1 i hi
  have hh := phase_direction L q odd P Q hp hq R hr hl hne hz n hn i hi hpar t ht
  refine ⟨atV R i,atV R (i+1),atV_some R i (by omega),atV_some R (i+1) (by omega),?_⟩
  rw [ht,step_label,hh]
  split_ifs <;> rfl

private theorem parity_of_step (R : Route Point) (odd : Bool) (i : ℕ)
    (hp : if odd then OddStep R i else EvenStep R i) : parity odd (atV R i) := by
  cases odd <;> obtain ⟨v,hv,hp⟩ := hp <;> simpa [parity,atV,hv] using hp

private theorem threshold_Q3 (L q : ℕ) (P Q : CriticalData q) (hp : P.Valid L)
    (R : Route Point) (hr : IsCrossPath (construction L q) (P.route L) (Q.route L) R)
    (no ne : ℕ) (hrel : no = ne ∨ no = ne+1)
    (ho : ∀ i < R.length, OddStep R i →
      UsesLabel R i (if counterAt true i < no then (P.a.val:ℤ) else (Q.a.val:ℤ)))
    (he : ∀ i < R.length, EvenStep R i →
      UsesLabel R i (if counterAt false i < ne then (P.b.val:ℤ) else (Q.b.val:ℤ))) : Q3 P Q R := by
  let cut := if no=ne then 2*no else 2*no-1
  let j := min cut R.length
  have hj : j ≤ R.length := Nat.min_le_right _ _
  have hjcut : j ≤ cut := Nat.min_le_left _ _
  refine ⟨j,hj,?_,?_⟩
  · intro i hij
    constructor
    · intro hodd
      have hm := (cross_parity L q true P Q hp R hr i (by omega)).mp (parity_of_step R true i hodd)
      have hh : counterAt true i < no := by dsimp [counterAt,cut] at *; split_ifs at hjcut <;> omega
      simpa [hh] using ho i (by omega) hodd
    · intro heven
      have hm := (cross_parity L q false P Q hp R hr i (by omega)).mp (parity_of_step R false i heven)
      have hh : counterAt false i < ne := by dsimp [counterAt,cut] at *; split_ifs at hjcut <;> omega
      simpa [hh] using he i (by omega) heven
  · intro i hji hi
    have hcut : cut ≤ i := by dsimp [j] at hji;omega
    constructor
    · intro hodd
      have hm := (cross_parity L q true P Q hp R hr i (by omega)).mp (parity_of_step R true i hodd)
      have hh : ¬ counterAt true i < no := by dsimp [counterAt,cut] at *; split_ifs at hcut <;> omega
      simpa [hh] using ho i hi hodd
    · intro heven
      have hm := (cross_parity L q false P Q hp R hr i (by omega)).mp (parity_of_step R false i heven)
      have hh : ¬ counterAt false i < ne := by dsimp [counterAt,cut] at *; split_ifs at hcut <;> omega
      simpa [hh] using he i hi heven

private structure SyncData (L q : ℕ) (P Q : CriticalData q) (R T : Route Point) where
  setup : PairSetup L q P Q R T
  ha : P.a ≠ Q.a
  hb : P.b ≠ Q.b
  no : ℕ
  ne : ℕ
  no_bound : no ≤ counterAt true R.length
  ne_bound : ne ≤ counterAt false R.length
  tauo : tauPar true P Q = (no:ℝ)
  taue : tauPar false P Q = (ne:ℝ)
  labsR : Q1 P Q R
  labsT : Q1 Q P T
  oddR : Vanishes (Rtest true P Q) R
  evenR : Vanishes (Rtest false P Q) R
  oddT : Vanishes (Rtest true Q P) T
  evenT : Vanishes (Rtest false Q P) T

private theorem S_value_R {L q : ℕ} {P Q : CriticalData q} {R T : Route Point}
    (D : SyncData L q P Q R T) (i : ℕ) (hi : i < R.length)
    (hp : parity true (atV R i)) (t : Fin q)
    (ht : atV R (i+1) = step q (atV R i) t) :
    testS P Q (position (atV R i)) t =
      ((D.ne:ℝ)-(D.no:ℝ)) * (if counterAt true i < D.no then 0 else 1) *
        max ((D.ne:ℝ)-(counterAt true i:ℝ)) 0 := by
  have hr := D.setup.2.2.2.1
  have hv := (psi_values L q false P Q D.setup.1 D.setup.2.1 R hr D.labsR D.hb D.evenR i (by omega)).2
  have hc : counterAt false i = counterAt true i := by
    have hh := (cross_parity L q true P Q D.setup.1 R hr i (by omega)).mp hp
    change i%2=0 at hh
    simp only [counterAt,Bool.false_eq_true,↓reduceIte]
    omega
  rw [cross_counter L q false P Q D.setup.1 R hr i (by omega),D.taue] at hv
  push_cast at hv
  rw [hc] at hv
  have hd := par_denom_ne true P Q D.ha
  have hdir := phase_direction L q true P Q D.setup.1 D.setup.2.1 R hr D.labsR
    D.ha D.oddR D.no D.tauo i hi hp t ht
  rw [S_eq,if_pos ⟨D.ha,D.hb,hp⟩,D.taue,D.tauo,hv]
  by_cases hh : counterAt true i < D.no
  · rw [if_pos hh] at hdir
    rw [hdir]
    simp [hh,parLabel]
  · rw [if_neg hh] at hdir
    rw [hdir]
    simpa [hh,parLabel] using congrArg
      (fun x : ℝ => ((D.ne:ℝ)-(D.no:ℝ))*x*max ((D.ne:ℝ)-(counterAt true i:ℝ)) 0)
      (div_self hd)

private theorem S_value_T {L q : ℕ} {P Q : CriticalData q} {R T : Route Point}
    (D : SyncData L q P Q R T) (i : ℕ) (hi : i < T.length)
    (hp : parity true (atV T i)) (t : Fin q)
    (ht : atV T (i+1) = step q (atV T i) t) :
    testS P Q (position (atV T i)) t =
      ((D.ne:ℝ)-(D.no:ℝ)) * (if counterAt true i < D.no then 1 else 0) *
        (-max ((counterAt true i:ℝ)-(D.ne:ℝ)) 0) := by
  have hr := D.setup.2.2.2.2
  have hv := (psi_values L q false Q P D.setup.2.1 D.setup.1 T hr D.labsT
    (Ne.symm D.hb) D.evenT i (by omega)).1
  have hc : counterAt false i = counterAt true i := by
    have hh := (cross_parity L q true Q P D.setup.2.1 T hr i (by omega)).mp hp
    change i%2=0 at hh
    simp only [counterAt,Bool.false_eq_true,↓reduceIte]
    omega
  rw [psiV_swap,cross_counter L q false Q P D.setup.2.1 T hr i (by omega),
    tauPar_swap,D.taue] at hv
  push_cast at hv
  rw [hc] at hv
  have hpsi : psiV false P Q Q (atV T i) = -max ((counterAt true i:ℝ)-(D.ne:ℝ)) 0 := by linarith
  have hn : tauPar true Q P = (D.no:ℝ) := by rw [tauPar_swap,D.tauo]
  have hdir := phase_direction L q true Q P D.setup.2.1 D.setup.1 T hr D.labsT
    (Ne.symm D.ha) D.oddT D.no hn i hi hp t ht
  have hd := par_denom_ne true P Q D.ha
  rw [S_eq,if_pos ⟨D.ha,D.hb,hp⟩,D.taue,D.tauo,hpsi]
  by_cases hh : counterAt true i < D.no
  · rw [if_pos hh] at hdir
    rw [hdir]
    simpa [hh,parLabel] using congrArg
      (fun x : ℝ => ((D.ne:ℝ)-(D.no:ℝ))*x*(-max ((counterAt true i:ℝ)-(D.ne:ℝ)) 0))
      (div_self hd)
  · rw [if_neg hh] at hdir
    rw [hdir]
    simp [hh,parLabel]

private theorem S_numeric_R (no ne j : ℕ) :
    0 ≤ ((ne:ℝ)-(no:ℝ)) * (if j<no then 0 else 1) * max ((ne:ℝ)-(j:ℝ)) 0 := by
  by_cases h : j < no
  · simp [h]
  · by_cases he : ne ≤ j
    · have he' : (ne:ℝ) ≤ (j:ℝ) := by exact_mod_cast he
      simp [h,max_eq_right (sub_nonpos.mpr he')]
    · have hne : (no:ℝ) ≤ (ne:ℝ) := by exact_mod_cast (show no ≤ ne by omega)
      simp only [if_neg h,mul_one]
      exact mul_nonneg (sub_nonneg.mpr hne) (le_max_right _ _)

private theorem S_numeric_T (no ne j : ℕ) :
    0 ≤ ((ne:ℝ)-(no:ℝ)) * (if j<no then 1 else 0) * (-max ((j:ℝ)-(ne:ℝ)) 0) := by
  by_cases h : j < no
  · by_cases he : j ≤ ne
    · have he' : (j:ℝ) ≤ (ne:ℝ) := by exact_mod_cast he
      simp [h,max_eq_right (sub_nonpos.mpr he')]
    · have hne : (ne:ℝ) ≤ (no:ℝ) := by exact_mod_cast (show ne ≤ no by omega)
      simp only [if_pos h,mul_one]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hne)
        (neg_nonpos.mpr (le_max_right _ _))
  · simp [h]

private theorem S_nonnegative {L q : ℕ} {P Q : CriticalData q} {R T : Route Point}
    (D : SyncData L q P Q R T) : T1prime (testS P Q) R T := by
  constructor
  · intro e he t ht
    obtain ⟨i,hi,hv,hw⟩ := arc_atV R e he
    have ht' : atV R (i+1) = step q (atV R i) t := by simpa [hv,hw] using ht
    rw [hv]
    by_cases hp : parity true (atV R i)
    · rw [S_value_R D i hi hp t ht']
      exact S_numeric_R D.no D.ne (counterAt true i)
    · rw [S_eq]
      simp [hp]
  · intro e he t ht
    obtain ⟨i,hi,hv,hw⟩ := arc_atV T e he
    have ht' : atV T (i+1) = step q (atV T i) t := by simpa [hv,hw] using ht
    rw [hv]
    by_cases hp : parity true (atV T i)
    · rw [S_value_T D i hi hp t ht']
      exact S_numeric_T D.no D.ne (counterAt true i)
    · rw [S_eq]
      simp [hp]

private theorem sync_thresholds {L q : ℕ} {P Q : CriticalData q} {R T : Route Point}
    (D : SyncData L q P Q R T) (hz : Vanishes (testS P Q) R ∧ Vanishes (testS P Q) T) :
    D.no = D.ne ∨ D.no = D.ne+1 := by
  have hbad1 : ¬ D.no < D.ne := by
    intro hlt
    have hb := D.ne_bound
    simp only [counterAt,Bool.false_eq_true,↓reduceIte] at hb
    have hi : 2*D.no < R.length := by omega
    have hp : parity true (atV R (2*D.no)) := by
      apply (cross_parity L q true P Q D.setup.1 R D.setup.2.2.2.1 (2*D.no) (by omega)).mpr
      change (2*D.no)%2=0
      omega
    obtain ⟨t,ht⟩ := route_step L q R D.setup.2.2.2.1.1 (2*D.no) hi
    have hh := hz.1 (atV R (2*D.no),atV R (2*D.no+1)) (route_arc_atV R (2*D.no) hi) t ht
    rw [S_value_R D (2*D.no) hi hp t ht] at hh
    have hc : counterAt true (2*D.no) = D.no := by simp only [counterAt,↓reduceIte];omega
    rw [hc,if_neg (by omega : ¬D.no<D.no),mul_one] at hh
    have hd : 0 < (D.ne:ℝ)-(D.no:ℝ) := sub_pos.mpr (by exact_mod_cast hlt)
    rw [max_eq_left hd.le] at hh
    nlinarith
  have hbad2 : ¬ D.ne+1 < D.no := by
    intro hlt
    have hb := D.no_bound
    simp only [counterAt,↓reduceIte] at hb
    have hlen : T.length = R.length :=
      (cross_length L q Q P D.setup.2.1 D.setup.1 T D.setup.2.2.2.2).trans
        (cross_length L q P Q D.setup.1 D.setup.2.1 R D.setup.2.2.2.1).symm
    have hi : 2*(D.ne+1) < T.length := by omega
    have hp : parity true (atV T (2*(D.ne+1))) := by
      apply (cross_parity L q true Q P D.setup.2.1 T D.setup.2.2.2.2 (2*(D.ne+1)) (by omega)).mpr
      change (2*(D.ne+1))%2=0
      omega
    obtain ⟨t,ht⟩ := route_step L q T D.setup.2.2.2.2.1 (2*(D.ne+1)) hi
    have hh := hz.2 (atV T (2*(D.ne+1)),atV T (2*(D.ne+1)+1))
      (route_arc_atV T (2*(D.ne+1)) hi) t ht
    rw [S_value_T D (2*(D.ne+1)) hi hp t ht] at hh
    have hc : counterAt true (2*(D.ne+1)) = D.ne+1 := by simp only [counterAt,↓reduceIte];omega
    have hj : ((D.ne+1:ℕ):ℝ)-(D.ne:ℝ) = 1 := by push_cast;ring
    rw [hc,if_pos hlt,mul_one,hj] at hh
    norm_num at hh
    have hd : (D.ne:ℝ) < (D.no:ℝ) := by exact_mod_cast (show D.ne<D.no by omega)
    linarith
  omega

open SteinerShortcuts.Main

private theorem layer_counters (L q ell : ℕ) (scale : ℤ) (v : Point)
    (hv : v ∈ layerBox L q ell scale) :
    v 0 = (ell:ℤ) ∧ v 1 = ((ell / 2 : ℕ):ℤ) ∧
      v 2 = (((ell-1)/2:ℕ):ℤ) := by
  have hm := Fintype.mem_piFinset.mp hv
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  norm_num [Fin.ext_iff] at h0 h1 h2
  exact ⟨h0,h1,h2⟩

 theorem vertex_counters (L q : ℕ) (v : Point) (hv : v ∈ vertices L q) :
    v 1 = v 0 / 2 ∧ v 2 = (v 0 - 1) / 2 := by
  rcases Finset.mem_union.mp hv with hv | hv
  · rcases layer_counters L q 1 1 v hv with ⟨h0,h1,h2⟩
    norm_num [h0, h1, h2]
  · rcases Finset.mem_biUnion.mp hv with ⟨ell, hell, hv⟩
    rcases layer_counters L q ell 2 v hv with ⟨h0,h1,h2⟩
    have he : 1 ≤ ell := by have := (Finset.mem_Icc.mp hell).1; omega
    simp [h0, h1, h2, Int.natCast_ediv, Nat.cast_sub he]

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

 theorem testS_linear (L q : ℕ) (P Q : CriticalData q) (ha : P.a ≠ Q.a) (hb : P.b ≠ Q.b) :
    T3prime L q (testS P Q) := by
  let da : ℝ := (Q.a.val:ℝ)-(P.a.val:ℝ)
  let db : ℝ := (Q.b.val:ℝ)-(P.b.val:ℝ)
  let k : ℝ := (tauEven P Q-tauOdd P Q)/da/db
  let x : ℝ := Q.source 7
  let a : ℝ := P.a.val
  let b : ℝ := Q.b.val
  refine ⟨![0,0,0,-k*x,0,0,0,0,0,0,0,0,0,0,0,0,0,0,k,-k*a,-k*b],
    fun ell => if ell%2=1 then k*(a*x+a*b*((ell/2:ℤ):ℝ)) else 0,?_⟩
  intro v hv t
  have hc := vertex_counters L q v hv
  by_cases ho : v 0 % 2 = 1
  · have he : v 2 = v 1 := by omega
    simp [testS,ha,hb,position,update,direction,ho,psi,Fin.sum_univ_succ]
    rw [he,hc.1]
    push_cast
    dsimp [k,da,db,x,a,b]
    ring
  · simp [testS,ha,hb,position,update,ho,Fin.sum_univ_succ]
private theorem pair_Rvanishes (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) (odd : Bool)
    (hne : parLabel odd P ≠ parLabel odd Q) :
    Vanishes (Rtest odd P Q) R ∧ Vanishes (Rtest odd Q P) T := by
  have hlabs := claim_3_3 L q h P Q R T hs
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
  refine ⟨hz.1,?_⟩
  intro e he t ht
  rw [Rtest_symm odd P Q e.1 t]
  exact hz.2 e he t ht

 theorem solution (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    Q3 P Q R := by
  have hlabs := claim_3_3 L q h P Q R T hs
  have hr := hs.2.2.2.1
  have odd_equal (ha : P.a = Q.a) (no : ℕ) :
      ∀ i < R.length, OddStep R i →
        UsesLabel R i (if counterAt true i < no then (P.a.val:ℤ) else (Q.a.val:ℤ)) := by
    intro i hi ho
    rcases (hlabs.1 i hi).1 ho with hu | hu <;> simpa [ha] using hu
  have even_equal (hb : P.b = Q.b) (ne : ℕ) :
      ∀ i < R.length, EvenStep R i →
        UsesLabel R i (if counterAt false i < ne then (P.b.val:ℤ) else (Q.b.val:ℤ)) := by
    intro i hi he
    rcases (hlabs.1 i hi).2 he with hu | hu <;> simpa [hb] using hu
  by_cases ha : P.a = Q.a
  · by_cases hb : P.b = Q.b
    · exact threshold_Q3 L q P Q hs.1 R hr 0 0 (Or.inl rfl) (odd_equal ha 0) (even_equal hb 0)
    · obtain ⟨ne,hne,hτe⟩ := tau_nat_bounds L q false P Q hs.1 hs.2.1 R hr hlabs.1 hb
      have hz := (pair_Rvanishes L q h P Q R T hs false hb).1
      apply threshold_Q3 L q P Q hs.1 R hr ne ne (Or.inl rfl) (odd_equal ha ne)
      intro i hi he
      exact phase_uses L q false P Q hs.1 hs.2.1 R hr hlabs.1 hb hz ne hτe i hi
        (parity_of_step R false i he)
  · by_cases hb : P.b = Q.b
    · obtain ⟨no,hno,hτo⟩ := tau_nat_bounds L q true P Q hs.1 hs.2.1 R hr hlabs.1 ha
      have hz := (pair_Rvanishes L q h P Q R T hs true ha).1
      apply threshold_Q3 L q P Q hs.1 R hr no no (Or.inl rfl) ?_ (even_equal hb no)
      intro i hi ho
      exact phase_uses L q true P Q hs.1 hs.2.1 R hr hlabs.1 ha hz no hτo i hi
        (parity_of_step R true i ho)
    · obtain ⟨no,hno,hτo⟩ := tau_nat_bounds L q true P Q hs.1 hs.2.1 R hr hlabs.1 ha
      obtain ⟨ne,hne,hτe⟩ := tau_nat_bounds L q false P Q hs.1 hs.2.1 R hr hlabs.1 hb
      have hzo := pair_Rvanishes L q h P Q R T hs true ha
      have hze := pair_Rvanishes L q h P Q R T hs false hb
      let D : SyncData L q P Q R T :=
        ⟨hs,ha,hb,no,ne,hno,hne,hτo,hτe,hlabs.1,hlabs.2,hzo.1,hze.1,hzo.2,hze.2⟩
      have hzS := claim_3_1 L q h P Q R T hs (testS P Q) (S_nonnegative D)
        (S_critical L q P Q hs.1 hs.2.1) (testS_linear L q P Q ha hb)
      have hrel : no = ne ∨ no = ne+1 := sync_thresholds D hzS
      apply threshold_Q3 L q P Q hs.1 R hr no ne hrel
      · intro i hi ho
        exact phase_uses L q true P Q hs.1 hs.2.1 R hr hlabs.1 ha hzo.1 no hτo i hi
          (parity_of_step R true i ho)
      · intro i hi he
        exact phase_uses L q false P Q hs.1 hs.2.1 R hr hlabs.1 hb hze.1 ne hτe i hi
          (parity_of_step R false i he)
