-- Prove2me | solution 1 for SteinerShortcuts.Main.equation_11
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T16:21:14.137524+00:00
-- url     : https://prove2.me/submissions/f472c88e-d86c-4157-897b-ba3d14e6303b

import Theorems.Thm_SteinerShortcuts_Main_critical_paths_valid
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

open SteinerShortcuts.Main

 theorem critical_injective (L q : ℕ) (hL : 3 ≤ L) :
    Function.Injective (fun sab : Point × (Fin q × Fin q) => critical L q sab.1 sab.2.1 sab.2.2) := by
  intro sab tab he
  rcases sab with ⟨s,a,b⟩
  rcases tab with ⟨t,c,d⟩
  have hs : s = t := congrArg Route.start he
  subst t
  have h1 := congrArg (fun R : Route Point => atV R 1) he
  rw [critical_atV L q s a b 1 (by omega),critical_atV L q s c d 1 (by omega)] at h1
  change step q s a = step q s c at h1
  have ha := step_label_injective q s a c h1
  subst c
  have h2 := congrArg (fun R : Route Point => atV R 2) he
  rw [critical_atV L q s a b 2 (by omega),critical_atV L q s a d 2 (by omega)] at h2
  change step q (step q s a) b = step q (step q s a) d at h2
  have hb := step_label_injective q (step q s a) b d h2
  subst d
  rfl

open SteinerShortcuts.Main
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private def boxProd (L q : ℕ) (r : ℤ) : ℤ :=
  ∏ i : Fin 18, (r*boxBounds L q i.succ.succ.succ+1)

private theorem box_nonneg (L q : ℕ) (i : Fin 21) : 0 ≤ boxBounds L q i := by
  fin_cases i <;> simp [boxBounds] <;> positivity

private theorem layer_product (L q ell : ℕ) (r : ℤ) (hr : 0 ≤ r) :
    ((layerBox L q ell r).card : ℤ) = boxProd L q r := by
  simp only [layerBox,Fintype.card_piFinset,Nat.cast_prod]
  trans ∏ i : Fin 21, if i.val<3 then (1:ℤ) else r*boxBounds L q i+1
  · apply Finset.prod_congr rfl
    intro i hi
    by_cases h0 : i=0
    · subst i;norm_num
    by_cases h1 : i=1
    · subst i;norm_num [Fin.ext_iff]
    by_cases h2 : i=2
    · subst i;norm_num [Fin.ext_iff]
    have hv : ¬ i.val<3 := by
      have hi0 : i.val≠0 := by intro he;exact h0 (Fin.ext he)
      have hi1 : i.val≠1 := by intro he;exact h1 (Fin.ext he)
      have hi2 : i.val≠2 := by intro he;exact h2 (Fin.ext he)
      omega
    simp only [h0,h1,h2,hv,↓reduceIte]
    have hh : (0:ℤ) ≤ r*boxBounds L q i+1 := by
      have hb := box_nonneg L q i
      positivity
    simpa using (Int.card_Icc_of_le (a:=(0:ℤ)) (b:=r*boxBounds L q i) hh)
  · rw [Fin.prod_univ_succ]
    norm_num only [Fin.val_zero,ite_true,one_mul]
    rw [Fin.prod_univ_succ]
    norm_num only [Fin.val_succ,Fin.val_zero,ite_true,one_mul]
    rw [Fin.prod_univ_succ]
    norm_num only [Fin.val_succ,Fin.val_zero,ite_true,one_mul]
    unfold boxProd
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (by omega)]

private theorem layer_card_eq (L q i j : ℕ) (r : ℤ) (hr : 0 ≤ r) :
    (layerBox L q i r).card = (layerBox L q j r).card := by
  exact_mod_cast (layer_product L q i r hr).trans (layer_product L q j r hr).symm

private theorem boxProd_scale (L q : ℕ) : boxProd L q 1 ≤ boxProd L q 2 ∧
    boxProd L q 2 ≤ 2^18 * boxProd L q 1 := by
  constructor
  · apply Finset.prod_le_prod
    · intro i hi;have := box_nonneg L q i.succ.succ.succ;positivity
    · intro i hi;have := box_nonneg L q i.succ.succ.succ;linarith
  · calc boxProd L q 2 ≤ ∏ i : Fin 18, 2*(boxBounds L q i.succ.succ.succ+1) := by
          apply Finset.prod_le_prod
          · intro i hi;have := box_nonneg L q i.succ.succ.succ;positivity
          · intro i hi;linarith
        _ = 2^18 * boxProd L q 1 := by
          simp [Finset.prod_mul_distrib,boxProd]

private def leExp : Fin 18 → ℕ := ![1,1,1,1,1,1,1,1,1,2,3,3,2,3,3,2,2,2]
private def qeExp : Fin 18 → ℕ := ![1,1,1,2,1,1,1,2,2,1,1,2,1,1,2,2,1,1]
private def boxCoeff : Fin 18 → ℤ := ![1,1,1,1,1,1,1,1,1,2,2,4,2,2,4,2,2,1]
private def degree (i : Fin 18) : ℕ := leExp i+qeExp i

private theorem box_monomial (L q : ℕ) (i : Fin 18) :
    boxBounds L q i.succ.succ.succ = boxCoeff i*(L:ℤ)^(leExp i)*(q:ℤ)^(qeExp i) := by
  fin_cases i <;> norm_num [boxBounds,boxCoeff,leExp,qeExp,Fin.succ] <;> ring

private theorem coeff_bounds (i : Fin 18) : 1 ≤ boxCoeff i ∧ boxCoeff i*2^(qeExp i) ≤ 16 := by
  fin_cases i <;> norm_num [boxCoeff,qeExp]

private theorem degree_sum : ∑ i : Fin 18, degree i = 55 := by
  norm_num [Fin.sum_univ_succ,degree,leExp,qeExp]

private theorem entry_bounds (L q : ℕ) (hL : 1 ≤ L) (hlq : L ≤ q) (hql : q ≤ 2*L) (i : Fin 18) :
    (L:ℤ)^(degree i) ≤ boxBounds L q i.succ.succ.succ+1 ∧
    boxBounds L q i.succ.succ.succ+1 ≤ 32*(L:ℤ)^(degree i) := by
  have hL0 : (0:ℤ) ≤ L := by positivity
  have hq0 : (0:ℤ) ≤ q := by positivity
  have hL1 : (1:ℤ) ≤ L := by exact_mod_cast hL
  have hlq' : (L:ℤ) ≤ q := by exact_mod_cast hlq
  have hql' : (q:ℤ) ≤ 2*(L:ℤ) := by exact_mod_cast hql
  have hC := coeff_bounds i
  have hC0 : 0 ≤ boxCoeff i := by omega
  have hp1 : (1:ℤ) ≤ (L:ℤ)^(degree i) := by
    simpa using pow_le_pow_left₀ (show (0:ℤ) ≤ 1 by omega) hL1 (degree i)
  have hlo : (L:ℤ)^(degree i) ≤ boxBounds L q i.succ.succ.succ := by
    rw [box_monomial]
    calc (L:ℤ)^(degree i) = (L:ℤ)^(leExp i)*(L:ℤ)^(qeExp i) := by rw [degree,pow_add]
         _ ≤ (L:ℤ)^(leExp i)*(q:ℤ)^(qeExp i) := by gcongr
         _ ≤ boxCoeff i*(L:ℤ)^(leExp i)*(q:ℤ)^(qeExp i) := by
           simpa only [one_mul,mul_assoc] using
             mul_le_mul_of_nonneg_right hC.1
               (mul_nonneg (pow_nonneg hL0 (leExp i)) (pow_nonneg hq0 (qeExp i)))
  have hhi : boxBounds L q i.succ.succ.succ ≤ 16*(L:ℤ)^(degree i) := by
    rw [box_monomial]
    calc boxCoeff i*(L:ℤ)^(leExp i)*(q:ℤ)^(qeExp i)
          ≤ boxCoeff i*(L:ℤ)^(leExp i)*(2*(L:ℤ))^(qeExp i) := by gcongr
         _ = (boxCoeff i*2^(qeExp i))*(L:ℤ)^(degree i) := by rw [degree,mul_pow,pow_add];ring
         _ ≤ 16*(L:ℤ)^(degree i) := mul_le_mul_of_nonneg_right hC.2 (pow_nonneg hL0 _)
  constructor <;> linarith

private theorem source_size_bounds (L q : ℕ) (hL : 1 ≤ L) (hlq : L ≤ q) (hql : q ≤ 2*L) :
    (L:ℤ)^55 ≤ ((sources L q).card:ℤ) ∧
      ((sources L q).card:ℤ) ≤ 32^18*(L:ℤ)^55 := by
  have hcard : ((sources L q).card:ℤ) = boxProd L q 1 := layer_product L q 1 1 (by omega)
  rw [hcard]
  have he : (∏ i : Fin 18, (L:ℤ)^(degree i)) = (L:ℤ)^55 := by
    rw [Finset.prod_pow_eq_pow_sum,degree_sum]
  constructor
  · rw [← he]
    apply Finset.prod_le_prod
    · intro i hi;positivity
    · intro i hi;simpa using (entry_bounds L q hL hlq hql i).1
  · calc boxProd L q 1 ≤ ∏ i : Fin 18, 32*(L:ℤ)^(degree i) := by
          apply Finset.prod_le_prod
          · intro i hi;have := box_nonneg L q i.succ.succ.succ;positivity
          · intro i hi;simpa using (entry_bounds L q hL hlq hql i).2
         _ = 32^18*(L:ℤ)^55 := by simp [Finset.prod_mul_distrib,he]

private theorem layer_coordinate (L q ell : ℕ) (r : ℤ) (v : Point)
    (hv : v ∈ layerBox L q ell r) : v 0 = (ell:ℤ) := by
  have hh := Fintype.mem_piFinset.mp hv 0
  simpa using hh

private theorem layer_disjoint (L q i j : ℕ) (r t : ℤ) (hij : i ≠ j) :
    Disjoint (layerBox L q i r) (layerBox L q j t) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have hi := layer_coordinate L q i r v hv
  have hj := layer_coordinate L q j t v hw
  apply hij
  omega

private theorem vertex_count (L q : ℕ) (hL : 1 ≤ L) :
    (vertices L q).card = (sources L q).card+(L-1)*(layerBox L q 0 2).card := by
  have hd : (↑(Finset.Icc 2 L) : Set ℕ).PairwiseDisjoint (fun ell => layerBox L q ell 2) := by
    intro i hi j hj hij
    exact layer_disjoint L q i j 2 2 hij
  have hs : Disjoint (sources L q) ((Finset.Icc 2 L).biUnion (fun ell => layerBox L q ell 2)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨ell,hell,hv'⟩ := Finset.mem_biUnion.mp hw
    exact Finset.disjoint_left.mp (layer_disjoint L q 1 ell 1 2 (by have := (Finset.mem_Icc.mp hell).1;omega)) hv hv'
  rw [vertices,Finset.card_union_of_disjoint hs,Finset.card_biUnion hd]
  have he (ell : ℕ) : (layerBox L q ell 2).card = (layerBox L q 0 2).card :=
    layer_card_eq L q ell 0 2 (by omega)
  simp_rw [he]
  have hc : (Finset.Icc 2 L).card = L-1 := by rw [Nat.card_Icc];omega
  simp [hc]

private theorem vertex_comparisons (L q : ℕ) (hL : 1 ≤ L) :
    (L:ℤ)*(sources L q).card ≤ ((vertices L q).card:ℤ) ∧
    ((vertices L q).card:ℤ) ≤ 2^18*(L:ℤ)*(sources L q).card := by
  have hs0 : (0:ℤ) ≤ (sources L q).card := by positivity
  have hl : (1:ℤ) ≤ L := by exact_mod_cast hL
  have hcount : ((vertices L q).card:ℤ) = (sources L q).card+((L:ℤ)-1)*(layerBox L q 0 2).card := by
    rw [vertex_count L q hL]
    push_cast
    rw [Nat.cast_sub hL]
    norm_num
  have hd := boxProd_scale L q
  have hS : ((sources L q).card:ℤ) = boxProd L q 1 := layer_product L q 1 1 (by omega)
  have hD : ((layerBox L q 0 2).card:ℤ) = boxProd L q 2 := layer_product L q 0 2 (by omega)
  rw [← hS,← hD] at hd
  have hm1 := mul_le_mul_of_nonneg_left hd.1 (show (0:ℤ) ≤ (L:ℤ)-1 by omega)
  have hm2 := mul_le_mul_of_nonneg_left hd.2 (show (0:ℤ) ≤ (L:ℤ)-1 by omega)
  constructor <;> nlinarith

open SteinerShortcuts.Main
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private theorem source_layer (L q : ℕ) (s : Point) (hs : s ∈ sources L q) : s 0 = 1 := by
  have hh := Fintype.mem_piFinset.mp hs 0
  simpa [layerBox] using hh

private theorem critical_source_injective (q : ℕ) (a b : Fin q) (i : ℕ) :
    Function.Injective (fun s : Point => criticalVertex q s a b i) := by
  induction i with
  | zero => intro s t he;exact he
  | succ i ih => intro s t he;exact ih (step_source_injective q (if i%2=0 then a else b) he)

private theorem critical_edge (L q : ℕ) (h : Admissible L q) (s : Point)
    (hs : s ∈ sources L q) (a b : Fin q) (i : ℕ) (hi : i < L-1) :
    (construction L q).Adj (criticalVertex q s a b i) (criticalVertex q s a b (i+1)) := by
  have hm : critical L q s a b ∈ criticalPaths L q := by
    apply Finset.mem_image.mpr
    refine ⟨(s,(a,b)),?_,rfl⟩
    simpa using hs
  have hc := (critical_paths_valid L q h _ hm).1
  unfold IsPath at hc
  rw [critical_vertices,List.isChain_map,List.isChain_range_succ] at hc
  exact hc i hi

private theorem edge_upper (L q : ℕ) :
    (constructionEdges L q).card ≤ (vertices L q).card*q := by
  let dom := vertices L q ×ˢ (Finset.univ : Finset (Fin q))
  let f := fun vt : Point × Fin q => (vt.1,step q vt.1 vt.2)
  have hsub : constructionEdges L q ⊆ dom.image f := by
    intro e he
    have ha := (Finset.mem_filter.mp he).2
    obtain ⟨hv,hw,hL,t,ht⟩ := ha
    apply Finset.mem_image.mpr
    refine ⟨(e.1,t),?_,?_⟩
    · simpa [dom] using hv
    · exact Prod.ext rfl ht.symm
  calc (constructionEdges L q).card ≤ (dom.image f).card := Finset.card_le_card hsub
       _ ≤ dom.card := Finset.card_image_le
       _ = (vertices L q).card*q := by simp [dom]

private def edgeAt (q : ℕ) (x : Point × (Fin q × ℕ)) : Point × Point :=
  (criticalVertex q x.1 x.2.1 x.2.1 x.2.2,criticalVertex q x.1 x.2.1 x.2.1 (x.2.2+1))

private theorem edge_lower (L q : ℕ) (h : Admissible L q) :
    (L-1)*(sources L q).card*q ≤ (constructionEdges L q).card := by
  let dom := sources L q ×ˢ ((Finset.univ : Finset (Fin q)) ×ˢ Finset.range (L-1))
  have hmem : ∀ x ∈ dom, edgeAt q x ∈ constructionEdges L q := by
    intro x hx
    have hs := (Finset.mem_product.mp hx).1
    have hi := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_product.mp hx).2).2
    have ha := critical_edge L q h x.1 hs x.2.1 x.2.1 x.2.2 hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha.1,ha.2.1⟩,ha⟩
  have hinj : Set.InjOn (edgeAt q) dom := by
    intro x hx y hy he
    rcases x with ⟨s,t,i⟩
    rcases y with ⟨s',t',i'⟩
    have hs := (Finset.mem_product.mp hx).1
    have hs' := (Finset.mem_product.mp hy).1
    have hh := congrArg (fun e : Point × Point => e.1 0) he
    change criticalVertex q s t t i 0 = criticalVertex q s' t' t' i' 0 at hh
    rw [critical_layer,critical_layer,source_layer L q s hs,source_layer L q s' hs'] at hh
    have hii : i=i' := by omega
    subst i'
    have hlabel := congrArg (fun e : Point × Point => edgeLabel e.1 e.2) he
    change edgeLabel (criticalVertex q s t t i) (criticalVertex q s t t (i+1)) =
      edgeLabel (criticalVertex q s' t' t' i) (criticalVertex q s' t' t' (i+1)) at hlabel
    have hstep (s : Point) (t : Fin q) : criticalVertex q s t t (i+1) = step q (criticalVertex q s t t i) t := by
      simp [criticalVertex]
    rw [hstep,hstep,step_label,step_label] at hlabel
    have htt : t=t' := by apply Fin.ext;exact_mod_cast hlabel
    subst t'
    have hsource := congrArg Prod.fst he
    change criticalVertex q s t t i = criticalVertex q s' t t i at hsource
    have hss := critical_source_injective q t t i hsource
    subst s'
    rfl
  have hh := Finset.card_le_card_of_injOn (edgeAt q) hmem hinj
  simpa [dom,mul_assoc,mul_comm,mul_left_comm] using hh

open SteinerShortcuts.Main
attribute [local instance] Classical.propDecidable

private theorem direction_injective (q : ℕ) : Function.Injective (direction q) := by
  intro a b he
  have hh := congrFun he 0
  apply Fin.ext
  exact_mod_cast (show (a.val:ℤ)=(b.val:ℤ) by simpa [direction] using hh)

private theorem direction_card (q : ℕ) : (directions q).card = q := by
  rw [directions,Finset.card_image_of_injOn (direction_injective q).injOn]
  simp

private theorem critical_card (L q : ℕ) (hL : 3 ≤ L) :
    (criticalPaths L q).card = (sources L q).card*q^2 := by
  rw [criticalPaths,Finset.card_image_of_injOn (critical_injective L q hL).injOn]
  simp [pow_two,mul_assoc]

private theorem critical_index_injective (L q : ℕ) (hL : 3 ≤ L) :
    Function.Injective (fun sab : ↥(sources L q) × (Fin q × Fin q) =>
      critical L q sab.1.val sab.2.1 sab.2.2) := by
  intro x y he
  have hh : (x.1.val,x.2) = (y.1.val,y.2) := critical_injective L q hL he
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun z : Point × (Fin q × Fin q) => z.2) hh)

set_option maxHeartbeats 800000

private theorem size_arithmetic (c C L q S n m p : ℝ)
    (hc : 0 ≤ c) (hch : c ≤ 1/2) (hck : c*2^18 ≤ 1) (hC : 2^19*32^18 ≤ C)
    (hL : 4 ≤ L) (hql : L ≤ q) (hqu : q ≤ 2*L) (hS : 0 ≤ S) (hm : 0 ≤ m)
    (hSl : L^55 ≤ S) (hSu : S ≤ 32^18*L^55)
    (hnl : L*S ≤ n) (hnu : n ≤ 2^18*L*S)
    (hml : (L-1)*S*q ≤ m) (hmu : m ≤ n*q) (hp : p = S*q^2) :
    (c*(L*S) ≤ n ∧ n ≤ C*(L*S)) ∧
    (c*L^56 ≤ n ∧ n ≤ C*L^56) ∧
    (c*(L*S*q) ≤ m ∧ m ≤ C*(L*S*q)) ∧
    (c*L^57 ≤ m ∧ m ≤ C*L^57) ∧
    (c*m ≤ p ∧ p ≤ C*m) := by
  have hL0 : 0 ≤ L := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hCk : (2:ℝ)^18 ≤ C := by norm_num at hC ⊢;linarith
  have hCkm : (2:ℝ)^18*32^18 ≤ C := by norm_num at hC ⊢;linarith
  have hC4 : (4:ℝ) ≤ C := by norm_num at hC ⊢;linarith
  have hp0 : 0 ≤ p := by rw [hp];positivity
  have hnlo : L^56 ≤ n := by
    calc L^56 = L*L^55 := by ring
         _ ≤ L*S := mul_le_mul_of_nonneg_left hSl hL0
         _ ≤ n := hnl
  have hnhi : n ≤ (2^18*32^18)*L^56 := by
    calc n ≤ 2^18*L*S := hnu
         _ ≤ 2^18*L*(32^18*L^55) := mul_le_mul_of_nonneg_left hSu (by positivity)
         _ = (2^18*32^18)*L^56 := by ring
  have hmlo : (1/2)*L*S*q ≤ m := by
    have hh := mul_le_mul_of_nonneg_right (show L/2 ≤ L-1 by linarith) (mul_nonneg hS hq0)
    nlinarith
  have hmhi : m ≤ 2^18*(L*S*q) := by
    have hh := mul_le_mul_of_nonneg_right hnu hq0
    nlinarith
  have hmlp : (1/2)*L^57 ≤ m := by
    calc (1/2)*L^57 = (1/2)*L*L^55*L := by ring
         _ ≤ (1/2)*L*S*q := by gcongr
         _ ≤ m := hmlo
  have hmhp : m ≤ (2^19*32^18)*L^57 := by
    calc m ≤ n*q := hmu
         _ ≤ ((2^18*32^18)*L^56)*(2*L) := by gcongr
         _ = (2^19*32^18)*L^57 := by ring
  have hmp : m ≤ 2^18*p := by
    calc m ≤ 2^18*(L*S*q) := hmhi
         _ ≤ 2^18*(q*S*q) := by gcongr
         _ = 2^18*p := by rw [hp];ring
  have hpm : p ≤ 4*m := by
    have hh := mul_le_mul_of_nonneg_right hqu (mul_nonneg hS hq0)
    rw [hp]
    nlinarith
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact (show c*(L*S) ≤ L*S by nlinarith [mul_nonneg hL0 hS]).trans hnl
  · exact hnu.trans (by nlinarith [mul_nonneg hL0 hS])
  · exact (mul_le_of_le_one_left (pow_nonneg hL0 _) hc1).trans hnlo
  · exact hnhi.trans (mul_le_mul_of_nonneg_right hCkm (pow_nonneg hL0 _))
  · exact (mul_le_mul_of_nonneg_right hch (mul_nonneg (mul_nonneg hL0 hS) hq0)).trans (by nlinarith [hmlo])
  · exact hmhi.trans (mul_le_mul_of_nonneg_right hCk (mul_nonneg (mul_nonneg hL0 hS) hq0))
  · exact (mul_le_mul_of_nonneg_right hch (pow_nonneg hL0 _)).trans hmlp
  · exact hmhp.trans (mul_le_mul_of_nonneg_right hC (pow_nonneg hL0 _))
  · calc c*m ≤ c*(2^18*p) := mul_le_mul_of_nonneg_left hmp hc
         _ = (c*2^18)*p := by ring
         _ ≤ 1*p := mul_le_mul_of_nonneg_right hck hp0
         _ = p := one_mul p
  · exact hpm.trans (mul_le_mul_of_nonneg_right hC4 hm)


/-- All constants precede L and q; counts are counts of tuples, edges, and routes. -/
theorem solution :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ L q : ℕ, Admissible L q →
      (c * ((L * (sources L q).card : ℕ) : ℝ) ≤ ((vertices L q).card : ℝ) ∧
        ((vertices L q).card : ℝ) ≤ C * ((L * (sources L q).card : ℕ) : ℝ)) ∧
      (c * (L : ℝ)^56 ≤ ((vertices L q).card : ℝ) ∧
        ((vertices L q).card : ℝ) ≤ C * (L : ℝ)^56) ∧
      (c * ((L * (sources L q).card * (directions q).card : ℕ) : ℝ) ≤
          ((constructionEdges L q).card : ℝ) ∧
        ((constructionEdges L q).card : ℝ) ≤
          C * ((L * (sources L q).card * (directions q).card : ℕ) : ℝ)) ∧
      (c * (L : ℝ)^57 ≤ ((constructionEdges L q).card : ℝ) ∧
        ((constructionEdges L q).card : ℝ) ≤ C * (L : ℝ)^57) ∧
      (criticalPaths L q).card = (sources L q).card * (directions q).card^2 ∧
      (c * ((constructionEdges L q).card : ℝ) ≤ ((criticalPaths L q).card : ℝ) ∧
        ((criticalPaths L q).card : ℝ) ≤ C * ((constructionEdges L q).card : ℝ)) ∧
      (∀ P ∈ criticalPaths L q, IsPath (construction L q) P ∧
        ∀ v ∈ P.vertices, v ∈ vertices L q) ∧
      (Function.Injective (fun sab : ↥(sources L q) × (Fin q × Fin q) =>
        critical L q sab.1.val sab.2.1 sab.2.2)) := by
  refine ⟨1/(2:ℝ)^18,(2:ℝ)^110,by norm_num,by norm_num,?_⟩
  intro L q h
  have hL : 1 ≤ L := by have := h.1;omega
  have hL3 : 3 ≤ L := by have := h.1;omega
  have hs : (L:ℝ)^55 ≤ ((sources L q).card:ℝ) ∧
      ((sources L q).card:ℝ) ≤ 32^18*(L:ℝ)^55 := by
    exact_mod_cast source_size_bounds L q hL h.2.2.2.1 h.2.2.2.2
  have hn : (L:ℝ)*(sources L q).card ≤ ((vertices L q).card:ℝ) ∧
      ((vertices L q).card:ℝ) ≤ 2^18*(L:ℝ)*(sources L q).card := by
    exact_mod_cast vertex_comparisons L q hL
  have hmu : ((constructionEdges L q).card:ℝ) ≤ ((vertices L q).card:ℝ)*(q:ℝ) := by
    exact_mod_cast edge_upper L q
  have hml : ((L:ℝ)-1)*(sources L q).card*(q:ℝ) ≤ ((constructionEdges L q).card:ℝ) := by
    have hh : ((L-1:ℕ):ℝ)*(sources L q).card*(q:ℝ) ≤ ((constructionEdges L q).card:ℝ) := by
      exact_mod_cast edge_lower L q h
    simpa only [Nat.cast_sub hL,Nat.cast_one] using hh
  have hpc : ((criticalPaths L q).card:ℝ) = ((sources L q).card:ℝ)*(q:ℝ)^2 := by
    exact_mod_cast critical_card L q hL3
  have ha := size_arithmetic (1/(2:ℝ)^18) ((2:ℝ)^110) (L:ℝ) (q:ℝ)
    ((sources L q).card:ℝ) ((vertices L q).card:ℝ) ((constructionEdges L q).card:ℝ)
    ((criticalPaths L q).card:ℝ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast h.1) (by exact_mod_cast h.2.2.2.1) (by exact_mod_cast h.2.2.2.2)
    (by positivity) (by positivity) hs.1 hs.2 hn.1 hn.2 hml hmu hpc
  obtain ⟨hA,hB,hC,hD,hE⟩ := ha
  refine ⟨?_,hB,?_,hD,?_,hE,critical_paths_valid L q h,critical_index_injective L q hL3⟩
  · simpa only [Nat.cast_mul] using hA
  · rw [direction_card]
    simpa only [Nat.cast_mul] using hC
  · simpa only [direction_card] using critical_card L q hL3



