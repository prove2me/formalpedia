-- Prove2me | solution 1 for SteinerShortcuts.Main.critical_paths_valid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:41:24.756917+00:00
-- url     : https://prove2.me/submissions/d39b27c4-3998-4cbe-9fe4-a455f961a9c4

import Definitions.Def_SteinerShortcuts_Main_Construction
open SteinerShortcuts.Main
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private def incBounds (L q : ℕ) : Point :=
  let l : ℤ := L
  let p : ℤ := q
  ![0,0,0,p,p,p,p^2,p,p,p,p^2,p^2,
    2*l*p,2*l^2*p,4*l^2*p^2,
    2*l*p,2*l^2*p,4*l^2*p^2,
    2*l*p^2,2*l*p,l*p]

private theorem bounds_scale (L q : ℕ) (j : Fin 21) :
    boxBounds L q j = (L:ℤ)*incBounds L q j := by
  fin_cases j <;> simp [boxBounds,incBounds] <;> ring

private theorem inc_nonneg (L q : ℕ) (j : Fin 21) : 0 ≤ incBounds L q j := by
  fin_cases j <;> simp [incBounds] <;> positivity

private theorem direction_bounds (q : ℕ) (hq : 0 < q) (t : Fin q) :
    (∀ j : Fin 3, 0 ≤ direction q t ⟨j.val,by omega⟩ ∧ direction q t ⟨j.val,by omega⟩ ≤ (q:ℤ)) ∧
    0 ≤ direction q t 3 ∧ direction q t 3 ≤ (q:ℤ)^2 ∧
    0 ≤ labelY q t.val ∧ labelY q t.val ≤ (q:ℤ) := by
  have hq' : (0:ℤ) < q := by exact_mod_cast hq
  have ht0 : (0:ℤ) ≤ t.val := by positivity
  have htq : (t.val:ℤ) ≤ q := by have := t.isLt; omega
  have hy0 : 0 ≤ labelY q t.val := Int.emod_nonneg _ hq'.ne'
  have hyq : labelY q t.val ≤ (q:ℤ) := by
    have := Int.emod_lt_of_pos ((t.val:ℤ)^2) hq'; dsimp [labelY]; omega
  have hquot0 : (0:ℤ) ≤ (t.val:ℤ)^2/(q:ℤ) := Int.ediv_nonneg (sq_nonneg _) hq'.le
  have hid : (t.val:ℤ)^2 - labelY q t.val = (q:ℤ)*((t.val:ℤ)^2/(q:ℤ)) := by
    have := Int.emod_add_mul_ediv ((t.val:ℤ)^2) (q:ℤ)
    dsimp [labelY]; omega
  have hzeq : ((t.val:ℤ)^2-labelY q t.val)/(q:ℤ) = (t.val:ℤ)^2/(q:ℤ) := by
    rw [hid]
    exact Int.mul_ediv_cancel_left _ hq'.ne'
  have hquotq : (t.val:ℤ)^2/(q:ℤ) ≤ q :=
    Int.ediv_le_of_le_mul hq' (by nlinarith [mul_self_le_mul_self ht0 htq])
  have hprod0 : 0 ≤ (t.val:ℤ)*labelY q t.val := mul_nonneg ht0 hy0
  have hprodq : (t.val:ℤ)*labelY q t.val ≤ (q:ℤ)^2 := by
    nlinarith [mul_le_mul htq hyq hy0 hq'.le]
  refine ⟨?_,by simpa [direction] using hprod0,by simpa [direction] using hprodq,hy0,hyq⟩
  intro j
  fin_cases j <;> simp [direction,hzeq] <;> omega

private theorem update_bounds (L q : ℕ) (hq : 0 < q) (p : Position) (t : Fin q)
    (hp1 : 0 ≤ p 1 ∧ p 1 ≤ (L:ℤ)) (hp2 : 0 ≤ p 2 ∧ p 2 ≤ (L:ℤ))
    (hp3 : 0 ≤ p 3 ∧ p 3 ≤ 2*(L:ℤ)*(q:ℤ))
    (hp7 : 0 ≤ p 7 ∧ p 7 ≤ 2*(L:ℤ)*(q:ℤ)) (j : Fin 21) (hj : 3 ≤ j.val) :
    0 ≤ update q p t j ∧ update q p t j ≤ incBounds L q j := by
  obtain ⟨hc,hc30,hc3q,hy0,hyq⟩ := direction_bounds q hq t
  have hc0 : 0 ≤ direction q t 0 ∧ direction q t 0 ≤ (q:ℤ) := hc 0
  have hc1 : 0 ≤ direction q t 1 ∧ direction q t 1 ≤ (q:ℤ) := hc 1
  have hc2 : 0 ≤ direction q t 2 ∧ direction q t 2 ≤ (q:ℤ) := hc 2
  have hy2 : (labelY q t.val)^2 ≤ (q:ℤ)^2 := by nlinarith [mul_self_le_mul_self hy0 hyq]
  have hx3sq : (p 3)^2 ≤ 4*(L:ℤ)^2*(q:ℤ)^2 := by nlinarith [mul_self_le_mul_self hp3.1 hp3.2]
  have hx7sq : (p 7)^2 ≤ 4*(L:ℤ)^2*(q:ℤ)^2 := by nlinarith [mul_self_le_mul_self hp7.1 hp7.2]
  have hrx3 : p 1 * p 3 ≤ 2*(L:ℤ)^2*(q:ℤ) := by
    nlinarith [mul_le_mul hp1.2 hp3.2 hp3.1 (show (0:ℤ) ≤ L by positivity)]
  have hrx7 : p 2 * p 7 ≤ 2*(L:ℤ)^2*(q:ℤ) := by
    nlinarith [mul_le_mul hp2.2 hp7.2 hp7.1 (show (0:ℤ) ≤ L by positivity)]
  have ht0 : (0:ℤ) ≤ t.val := by positivity
  have htq : (t.val:ℤ) ≤ q := by have := t.isLt; omega
  have htx7 : (t.val:ℤ)*p 7 ≤ 2*(L:ℤ)*(q:ℤ)^2 := by
    nlinarith [mul_le_mul htq hp7.2 hp7.1 (show (0:ℤ) ≤ q by positivity)]
  have hrt : p 1 * (t.val:ℤ) ≤ (L:ℤ)*(q:ℤ) := by
    nlinarith [mul_le_mul hp1.2 htq ht0 (show (0:ℤ) ≤ L by positivity)]
  by_cases ho : p 0 % 2 = 1 <;>
    fin_cases j <;> norm_num at hj <;>
    simp [update,incBounds,ho] <;>
    constructor <;> first | positivity | omega | nlinarith

private theorem critical_layer (q : ℕ) (s : Point) (a b : Fin q) (i : ℕ) :
    criticalVertex q s a b i 0 = s 0 + (i:ℤ) := by
  induction i with
  | zero => simp [criticalVertex]
  | succ i ih => simp [criticalVertex, step, update, ih]; ring

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

private theorem critical_bounds (L q : ℕ) (hL : 1 ≤ L) (hq : 0 < q) (s : Point)
    (hs : s ∈ sources L q) (a b : Fin q) (i : ℕ) (hi : i ≤ L-1) :
    ∀ j : Fin 21, 3 ≤ j.val →
      0 ≤ criticalVertex q s a b i j ∧
      criticalVertex q s a b i j ≤ s j + (i:ℤ)*incBounds L q j := by
  have hsource := (source_coordinates L q s hs).2.2.2
  induction i with
  | zero => intro j hj; simpa [criticalVertex] using (hsource j hj).1
  | succ i ih =>
    have hi' : i ≤ L-1 := by omega
    have ih := ih hi'
    have hcounter := critical_counters L q s hs a b i
    have hb (j : Fin 21) (hj : 3 ≤ j.val) : criticalVertex q s a b i j ≤ 2*boxBounds L q j := by
      have hh := (ih j hj).2
      have hs := (hsource j hj).2
      have hm := mul_le_mul_of_nonneg_right (show (i:ℤ) ≤ L by omega) (inc_nonneg L q j)
      rw [← bounds_scale] at hm
      linarith
    have hp1 : 0 ≤ position (criticalVertex q s a b i) 1 ∧
        position (criticalVertex q s a b i) 1 ≤ (L:ℤ) := by
      change 0 ≤ criticalVertex q s a b i 1 ∧ criticalVertex q s a b i 1 ≤ (L:ℤ)
      rw [hcounter.1]; omega
    have hp2 : 0 ≤ position (criticalVertex q s a b i) 2 ∧
        position (criticalVertex q s a b i) 2 ≤ (L:ℤ) := by
      change 0 ≤ criticalVertex q s a b i 2 ∧ criticalVertex q s a b i 2 ≤ (L:ℤ)
      rw [hcounter.2]; omega
    have hp3 : 0 ≤ position (criticalVertex q s a b i) 3 ∧
        position (criticalVertex q s a b i) 3 ≤ 2*(L:ℤ)*(q:ℤ) := by
      constructor
      · exact (ih 3 (by decide)).1
      · simpa [position,boxBounds,mul_assoc] using hb 3 (by decide)
    have hp7 : 0 ≤ position (criticalVertex q s a b i) 7 ∧
        position (criticalVertex q s a b i) 7 ≤ 2*(L:ℤ)*(q:ℤ) := by
      constructor
      · exact (ih 7 (by decide)).1
      · simpa [position,boxBounds,mul_assoc] using hb 7 (by decide)
    intro j hj
    have hu := update_bounds L q hq (position (criticalVertex q s a b i))
      (if i%2=0 then a else b) hp1 hp2 hp3 hp7 j hj
    have hh := ih j hj
    simp only [criticalVertex,step,Pi.add_apply,Nat.cast_add,Nat.cast_one]
    constructor <;> nlinarith [inc_nonneg L q j]

private theorem critical_in_vertices (L q : ℕ) (hL : 1 ≤ L) (hq : 0 < q)
    (s : Point) (hs : s ∈ sources L q) (a b : Fin q) (i : ℕ) (hi : i ≤ L-1) :
    criticalVertex q s a b i ∈ vertices L q := by
  have hs0 := (source_coordinates L q s hs).1
  cases i with
  | zero => exact Finset.mem_union_left _ hs
  | succ i =>
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨i+2,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    have h0 := critical_layer q s a b (i+1)
    have hc := critical_counters L q s hs a b (i+1)
    by_cases hj0 : j = 0
    · subst j
      simp [hs0,Nat.cast_add] at h0 ⊢
      omega
    by_cases hj1 : j = 1
    · subst j
      have hh := hc.1
      simp [Fin.ext_iff,Int.natCast_ediv,Nat.cast_add] at hh ⊢
      omega
    by_cases hj2 : j = 2
    · subst j
      simpa [Fin.ext_iff,Int.natCast_ediv,Nat.cast_add] using hc.2
    have hj : 3 ≤ j.val := by
      have h0 : j.val ≠ 0 := by intro he; exact hj0 (Fin.ext he)
      have h1 : j.val ≠ 1 := by intro he; exact hj1 (Fin.ext he)
      have h2 : j.val ≠ 2 := by intro he; exact hj2 (Fin.ext he)
      omega
    have hb := critical_bounds L q hL hq s hs a b (i+1) hi j hj
    have hsource := (source_coordinates L q s hs).2.2.2 j hj
    have hm := mul_le_mul_of_nonneg_right (show ((i+1:ℕ):ℤ) ≤ L by omega) (inc_nonneg L q j)
    rw [← bounds_scale] at hm
    have hh : 0 ≤ criticalVertex q s a b (i+1) j ∧
        criticalVertex q s a b (i+1) j ≤ 2*boxBounds L q j := by constructor <;> linarith
    simpa [hj0,hj1,hj2] using hh

private theorem critical_vertices (L q : ℕ) (s : Point) (a b : Fin q) :
    (critical L q s a b).vertices = (List.range (L-1+1)).map (criticalVertex q s a b) := by
  simp [Route.vertices, critical, List.range_succ_eq_map, List.map_map,
    Function.comp_def, criticalVertex]

private theorem critical_valid (L q : ℕ) (hL : 1 ≤ L) (hq : 0 < q)
    (s : Point) (hs : s ∈ sources L q) (a b : Fin q) :
    IsPath (construction L q) (critical L q s a b) ∧
    ∀ v ∈ (critical L q s a b).vertices, v ∈ vertices L q := by
  have hs0 := (source_coordinates L q s hs).1
  constructor
  · unfold IsPath
    rw [critical_vertices,List.isChain_map,List.isChain_range_succ]
    intro i hi
    refine ⟨critical_in_vertices L q hL hq s hs a b i (by omega),
      critical_in_vertices L q hL hq s hs a b (i+1) (by omega),?_,?_⟩
    · rw [critical_layer,hs0]; omega
    · exact ⟨if i%2=0 then a else b,rfl⟩
  · intro v hv
    rw [critical_vertices] at hv
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    exact critical_in_vertices L q hL hq s hs a b i (by have := List.mem_range.mp hi;omega)

 theorem solution (L q : ℕ) (h : Admissible L q) :
    ∀ P ∈ criticalPaths L q, IsPath (construction L q) P ∧
      ∀ v ∈ P.vertices, v ∈ vertices L q := by
  intro P hP
  obtain ⟨sab,hsab,rfl⟩ := Finset.mem_image.mp hP
  exact critical_valid L q (by have := h.1;omega) h.2.2.1.pos sab.1
    (Finset.mem_product.mp hsab).1 sab.2.1 sab.2.2
