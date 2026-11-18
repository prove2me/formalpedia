-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_2_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:07:01.325825+00:00
-- url     : https://prove2.me/submissions/16692717-fca7-4483-855e-92207f1e35da

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
private theorem source_coordinates (L q : ℕ) (s : Point) (hs : s ∈ sources L q) :
    s 0 = 1 ∧ s 1 = 0 ∧ s 2 = 0 ∧
    ∀ j : Fin 21, 3 ≤ j.val → 0 ≤ s j ∧ s j ≤ boxBounds L q j := by
  have hm := Fintype.mem_piFinset.mp hs
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  norm_num [Fin.ext_iff] at h0 h1 h2
  refine ⟨h0,h1,h2,?_⟩
  intro j hj
  have hj0 : j ≠ 0 := by intro hh; subst j; norm_num at hj
  have hj1 : j ≠ 1 := by intro hh; subst j; norm_num at hj
  have hj2 : j ≠ 2 := by intro hh; subst j; norm_num at hj
  have hh := hm j
  simpa [hj0,hj1,hj2] using hh

private theorem critical_counters (L q : ℕ) (s : Point) (hs : s ∈ sources L q)
    (a b : Fin q) (i : ℕ) :
    criticalVertex q s a b i 1 = ((i:ℤ)+1)/2 ∧
    criticalVertex q s a b i 2 = (i:ℤ)/2 := by
  obtain ⟨hs0,hs1,hs2,_⟩ := source_coordinates L q s hs
  induction i with
  | zero => simp [criticalVertex,hs1,hs2]
  | succ i ih =>
    have h0 := critical_layer q s a b i
    rw [hs0] at h0
    by_cases ho : (1+(i:ℤ))%2 = 1 <;>
      simp [criticalVertex,step,update,position,h0,ho,ih] <;> omega


private theorem critical_position (L q : ℕ) (s : Point) (hs : s ∈ sources L q)
    (a b : Fin q) (i : ℕ) :
    criticalVertex q s a b i 3 = s 3 + (a.val:ℤ)*criticalVertex q s a b i 1 ∧
    criticalVertex q s a b i 7 = s 7 + (b.val:ℤ)*criticalVertex q s a b i 2 := by
  obtain ⟨hs0,hs1,hs2,_⟩ := source_coordinates L q s hs
  induction i with
  | zero => simp [criticalVertex,hs1,hs2]
  | succ i ih =>
    have h0 := critical_layer q s a b i
    rw [hs0] at h0
    by_cases ho : i%2=0
    · have hp : criticalVertex q s a b i 0 % 2 = 1 := by omega
      simp [criticalVertex,step,update,position,direction,ih,ho,hp] <;> ring
    · have hp : criticalVertex q s a b i 0 % 2 ≠ 1 := by omega
      simp [criticalVertex,step,update,position,direction,ih,ho,hp] <;> ring

private theorem critical_source_injective (q : ℕ) (a b : Fin q) (i : ℕ) :
    Function.Injective (fun s : Point => criticalVertex q s a b i) := by
  induction i with
  | zero => intro s t he; exact he
  | succ i ih =>
    intro s t he
    exact ih (step_source_injective q (if i%2=0 then a else b) he)

private theorem critical_eq_of_two_vertices (L q : ℕ) (s t : Point)
    (hs : s ∈ sources L q) (ht : t ∈ sources L q) (a b c d : Fin q)
    (i j : ℕ) (hgap : i+2 ≤ j)
    (hi : criticalVertex q s a b i = criticalVertex q t c d i)
    (hj : criticalVertex q s a b j = criticalVertex q t c d j) :
    critical L q s a b = critical L q t c d := by
  have hxi := congrFun hi 3
  have hxj := congrFun hj 3
  have hyi := congrFun hi 7
  have hyj := congrFun hj 7
  have hPi := critical_position L q s hs a b i
  have hQi := critical_position L q t ht c d i
  have hPj := critical_position L q s hs a b j
  have hQj := critical_position L q t ht c d j
  have hci := critical_counters L q s hs a b i
  have hcj := critical_counters L q s hs a b j
  have hdi := critical_counters L q t ht c d i
  have hdj := critical_counters L q t ht c d j
  rw [hci.1,hci.2] at hPi
  rw [hdi.1,hdi.2] at hQi
  rw [hcj.1,hcj.2] at hPj
  rw [hdj.1,hdj.2] at hQj
  have hr : ((i:ℤ)+1)/2 < ((j:ℤ)+1)/2 := by omega
  have he : (i:ℤ)/2 < (j:ℤ)/2 := by omega
  have ham : ((a.val:ℤ)-(c.val:ℤ))*(((j:ℤ)+1)/2-((i:ℤ)+1)/2) = 0 := by
    nlinarith [hPi.1,hQi.1,hPj.1,hQj.1]
  have hbm : ((b.val:ℤ)-(d.val:ℤ))*((j:ℤ)/2-(i:ℤ)/2) = 0 := by
    nlinarith [hPi.2,hQi.2,hPj.2,hQj.2]
  have ha : a=c := by
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp ((mul_eq_zero.mp ham).resolve_right (ne_of_gt (sub_pos.mpr hr)))
  have hb : b=d := by
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp ((mul_eq_zero.mp hbm).resolve_right (ne_of_gt (sub_pos.mpr he)))
  subst c
  subst d
  have hst := critical_source_injective q a b i hi
  subst t
  rfl

private theorem common_arc (L q : ℕ) (s t : Point) (hs : s ∈ sources L q)
    (ht : t ∈ sources L q) (a b c d : Fin q) (e : Point × Point)
    (hp : e ∈ (critical L q s a b).arcs) (hq : e ∈ (critical L q t c d).arcs) :
    ∃ i < L-1, e.1 = criticalVertex q s a b i ∧
      e.2 = criticalVertex q s a b (i+1) ∧
      e.1 = criticalVertex q t c d i ∧ e.2 = criticalVertex q t c d (i+1) := by
  obtain ⟨i,hi,he1,he2⟩ := critical_arcs L q s a b e hp
  obtain ⟨j,hj,hf1,hf2⟩ := critical_arcs L q t c d e hq
  have hh := congrArg (fun v : Point => v 0) (he1.symm.trans hf1)
  rw [critical_layer,critical_layer,(source_coordinates L q s hs).1,
    (source_coordinates L q t ht).1] at hh
  have hij : i=j := by omega
  subst j
  exact ⟨i,hi,he1,he2,hf1,hf2⟩

 theorem solution (L q : ℕ) (h : Admissible L q) : P3 (criticalPaths L q) 1 := by
  intro P hP Q hQ hneq
  obtain ⟨sab,hsab,rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨tab,htab,rfl⟩ := Finset.mem_image.mp hQ
  have hs := (Finset.mem_product.mp hsab).1
  have ht := (Finset.mem_product.mp htab).1
  apply Finset.card_le_one.mpr
  intro e he f hf
  simp only [Finset.mem_inter,List.mem_toFinset] at he hf
  obtain ⟨i,hi,hei1,hei2,heq1,heq2⟩ := common_arc L q sab.1 tab.1 hs ht
    sab.2.1 sab.2.2 tab.2.1 tab.2.2 e he.1 he.2
  obtain ⟨j,hj,hfi1,hfi2,hfq1,hfq2⟩ := common_arc L q sab.1 tab.1 hs ht
    sab.2.1 sab.2.2 tab.2.1 tab.2.2 f hf.1 hf.2
  by_cases hij : i=j
  · subst j
    exact Prod.ext (hei1.trans hfi1.symm) (hei2.trans hfi2.symm)
  · rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact False.elim (hneq (critical_eq_of_two_vertices L q sab.1 tab.1 hs ht
        sab.2.1 sab.2.2 tab.2.1 tab.2.2 i (j+1) (by omega)
        (hei1.symm.trans heq1) (hfi2.symm.trans hfq2)))
    · exact False.elim (hneq (critical_eq_of_two_vertices L q sab.1 tab.1 hs ht
        sab.2.1 sab.2.2 tab.2.1 tab.2.2 j (i+1) (by omega)
        (hfi1.symm.trans hfq1) (hei2.symm.trans heq2)))
