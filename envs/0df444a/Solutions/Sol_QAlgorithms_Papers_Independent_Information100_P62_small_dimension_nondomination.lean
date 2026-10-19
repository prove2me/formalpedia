-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.small_dimension_nondomination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:22:00.443012+00:00
-- url     : https://prove2.me/submissions/8bf15569-8413-4054-8774-ab2419e4c4a0

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_kraus_geometric_converse
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_sequential_converse
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_equal_block_packing
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_small_block_embedding

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset
attribute [local instance] Classical.propDecidable

private lemma kraus_graph_le {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] {r : ℕ} (E : Fin r → Matrix O I ℂ) :
    graph (krausApply E) ≤ Submodule.span ℂ (Set.range (fun p : Fin r × Fin r => (E p.1)ᴴ * E p.2)) := by
  classical
  apply Submodule.span_le.mpr
  rintro X ⟨s,B,_hB,hEq,i,j,rfl⟩
  let M : Matrix (O × I) (Fin r) ℂ := fun a t => E t a.1 a.2
  let N : Matrix (O × I) (Fin s) ℂ := fun a t => B t a.1 a.2
  have hMN : M * Mᴴ = N * Nᴴ := by
    ext ⟨a,b⟩ ⟨c,d⟩
    change (∑ t, E t a b * conj (E t c d)) = ∑ t, B t a b * conj (B t c d)
    have hh := congrFun (congrFun (hEq (Matrix.single b d 1)) a) c
    simpa [M,N,Matrix.of_apply,krausApply,Matrix.mul_apply,Matrix.sum_apply,
      Matrix.conjTranspose_apply,Complex.conj_ofNat,Matrix.single_apply,ite_and] using hh
  have hrange : LinearMap.range (Matrix.toEuclideanLin M) =
      LinearMap.range (Matrix.toEuclideanLin N) := by
    calc
      _ = LinearMap.range (Matrix.toEuclideanLin (M * Mᴴ)) := by
        rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
          LinearMap.range_self_comp_adjoint]
      _ = LinearMap.range (Matrix.toEuclideanLin (N * Nᴴ)) := by rw [hMN]
      _ = _ := by
        rw [Matrix.toLpLin_mul_same,Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
          LinearMap.range_self_comp_adjoint]
  have hcoeff (t : Fin s) : ∃ v : EuclideanSpace ℂ (Fin r), B t = ∑ u, v u • E u := by
    have hn : Matrix.toEuclideanLin N (ket t) ∈ LinearMap.range (Matrix.toEuclideanLin M) := by
      rw [hrange]
      exact ⟨ket t,rfl⟩
    obtain ⟨v,hv⟩ := hn
    refine ⟨v,?_⟩
    ext a b
    have hh := congrArg (fun x : EuclideanSpace ℂ (O × I) => x (a,b)) hv
    change (∑ u, M (a,b) u * v u) = ∑ u, N (a,b) u * (ket t) u at hh
    simpa [M,N,ket,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_comm] using hh.symm
  obtain ⟨v,hv⟩ := hcoeff i
  obtain ⟨w,hw⟩ := hcoeff j
  rw [hv,hw,Matrix.conjTranspose_sum,Matrix.sum_mul]
  apply Submodule.sum_mem
  intro a _
  rw [Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_sum]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro b _
  rw [Matrix.mul_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(a,b),rfl⟩

private theorem h62_trace_idem {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (h : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [← Matrix.trace_toLin_eq P (Pi.basisFun ℂ n), Matrix.toLin_eq_toLin', this, Matrix.rank]
  rfl

private lemma valid_quantum (d : ℕ) (hd : 0 < d) : Valid (quantum d) := by
  simp [Valid,quantum,hd]
private lemma valid_classical (d : ℕ) (hd : 0 < d) : Valid (classical d) := by
  constructor
  · intro hz; have hh := congrArg Multiset.card hz; simp [classical,equalBlocks] at hh; omega
  · intro a ha; have hh : a = 1 := Multiset.eq_of_mem_replicate ha; omega

private def c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
private lemma c_def : (Real.sqrt 2 : ℂ)⁻¹ = c := rfl
private lemma cs : conj c = c := by simp [c]
private lemma cp : c ^ 2 = (1/2:ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  simp only [c,inv_pow,hs]
  norm_num

private abbrev E := example42Kraus
private def Q : Matrix (Fin 4) (Fin 4) ℂ := unit 0 0 + unit 1 1
private def idx : Fin 3 → Fin 4 := ![0,2,3]
private def R (k : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ := unit (idx k) (idx k)

private lemma e00 : (E 0)ᴴ * E 0 = Q := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]

private lemma e01 : (E 0)ᴴ * E 1 = c • unit 1 2 := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]

private lemma e02 : (E 0)ᴴ * E 2 = c • unit 1 3 := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]

private lemma e10 : (E 1)ᴴ * E 0 = c • unit 2 1 := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]

private lemma e11 : (E 1)ᴴ * E 1 = R 1 := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]
  all_goals ring_nf
  all_goals norm_num [cp]

private lemma e12 : (E 1)ᴴ * E 2 = 0 := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]

private lemma e20 : (E 2)ᴴ * E 0 = c • unit 3 1 := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]

private lemma e21 : (E 2)ᴴ * E 1 = 0 := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]

private lemma e22 : (E 2)ᴴ * E 2 = R 2 := by
  ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,R,idx,c_def,cs, unit,Matrix.single_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.conj_ofNat,Fin.sum_univ_three,Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply]
  all_goals ring_nf
  all_goals norm_num [cp]

private lemma effects (i j : Fin 3) : (E i)ᴴ * E j =
    ![![Q,c • unit 1 2,c • unit 1 3],
      ![c • unit 2 1,R 1,0],![c • unit 3 1,0,R 2]] i j := by
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e02
  · exact e10
  · exact e11
  · exact e12
  · exact e20
  · exact e21
  · exact e22

private lemma normalized : IsKrausFamily E := by
  change (∑ i, (E i)ᴴ * E i) = 1
  simp only [Fin.sum_univ_three,effects,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  ext a b; fin_cases a <;> fin_cases b <;>
    norm_num [Q,R,idx,unit,Matrix.single_apply,Matrix.one_apply,Fin.ext_iff,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
private lemma channel : IsChannel example42 := ⟨3,E,normalized,fun _ => rfl⟩

private lemma projQ : IsProjection Q := by
  constructor
  · simp [Q,unit,Matrix.conjTranspose_add,Matrix.conjTranspose_single]
  · simp [Q,unit,Matrix.add_mul,Matrix.mul_add]
private lemma projR (i : Fin 3) : IsProjection (R i) := by
  constructor
  · simp [R,unit,Matrix.conjTranspose_single]
  · simp [R,unit]
private lemma rankQ : Q.rank = 2 := by
  have h := h62_trace_idem Q projQ.2
  have ht : Q.trace = 2 := by norm_num [Q,unit,Matrix.trace_single_eq_same,Matrix.trace_add]
  exact_mod_cast h.symm.trans ht
private lemma rankR (i : Fin 3) : (R i).rank = 1 := by
  have h := h62_trace_idem (R i) (projR i).2
  have ht : (R i).trace = 1 := by simp [R,unit,Matrix.trace_single_eq_same]
  exact_mod_cast h.symm.trans ht

private lemma code_of_effects {n : ℕ} (B : Fin n → Matrix (Fin 3) (Fin 4) ℂ)
    (C : Matrix (Fin 4) (Fin 4) ℂ) (hC : IsProjection C)
    (h : ∀ i j, ∃ z : ℂ, C * ((B i)ᴴ * B j) * C = z • C) :
    Code (graph (krausApply B)) C := by
  refine ⟨hC,?_⟩
  intro X hX
  have hh := kraus_graph_le B hX
  clear hX
  induction hh using Submodule.span_induction with
  | mem X hX => obtain ⟨⟨i,j⟩,rfl⟩ := hX; exact h i j
  | zero => exact ⟨0,by simp⟩
  | add X Y hX hY iX iY =>
      obtain ⟨a,ha⟩ := iX; obtain ⟨b,hb⟩ := iY
      exact ⟨a+b,by rw [Matrix.mul_add,Matrix.add_mul,ha,hb,add_smul]⟩
  | smul c X hX iX =>
      obtain ⟨a,ha⟩ := iX
      exact ⟨c*a,by rw [Matrix.mul_smul,Matrix.smul_mul,ha,smul_smul]⟩

private lemma compression_factor {n : ℕ} (B : Fin n → Matrix (Fin 3) (Fin 4) ℂ)
    (C : Matrix (Fin 4) (Fin 4) ℂ) (hC : IsProjection C) (i j : Fin n) :
    C * ((B i)ᴴ * B j) * C = (B i * C)ᴴ * (B j * C) := by
  rw [Matrix.conjTranspose_mul,hC.1]
  simp only [Matrix.mul_assoc]

private lemma e_on_Q (i : Fin 3) : E i * Q = if i = 0 then E 0 else 0 := by
  fin_cases i
  all_goals ext a b; fin_cases a <;> fin_cases b
  all_goals norm_num [E,example42Kraus,Q,unit,Matrix.single_apply,Matrix.mul_apply,
    Fin.sum_univ_four,Fin.ext_iff,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]

private lemma codeQ : Code (graph example42) Q := by
  apply code_of_effects E Q projQ
  intro i j
  refine ⟨if i = 0 ∧ j = 0 then 1 else 0,?_⟩
  rw [compression_factor E Q projQ,e_on_Q,e_on_Q]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi,hj,effects]

private lemma R_compression (a b i j : Fin 3) :
    R a * ((E i)ᴴ * E j) * R b =
      if a = b ∧ i = a ∧ j = a then R a else 0 := by
  rw [effects]
  simp only [R,unit,Matrix.single_mul_mul_single,one_mul,mul_one]
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [Q,R,idx,unit,Matrix.single_apply,Fin.ext_iff,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]

private lemma codeR (k : Fin 3) : Code (graph example42) (R k) := by
  apply code_of_effects E (R k) (projR k)
  intro i j
  refine ⟨if i = k ∧ j = k then 1 else 0,?_⟩
  rw [R_compression]
  by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi,hj]

private lemma orthR (a b : Fin 3) (hab : a ≠ b)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X ∈ graph example42) :
    R a * X * R b = 0 := by
  have hh := kraus_graph_le E hX
  clear hX
  induction hh using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨⟨i,j⟩,rfl⟩ := hX
      simp [R_compression,hab]
  | zero => simp
  | add X Y hX hY iX iY => simp [Matrix.mul_add,Matrix.add_mul,iX,iY]
  | smul c X hX iX => simp [iX]

private lemma quantum_transmits {B : Superop (Fin 4) (Fin 3)} (hB : IsChannel B)
    (d : ℕ) (hd : 0 < d) (C : Matrix (Fin 4) (Fin 4) ℂ)
    (hc : Code (graph B) C) (hr : C.rank = d) : Transmits B (quantum d) := by
  apply (orthogonal_codes B hB (quantum d) (valid_quantum d hd)).mpr
  refine ⟨fun _ => C,fun k => ⟨hc,?_⟩,?_⟩
  · rw [hr]
    symm
    exact Multiset.mem_singleton.mp (Multiset.mem_toList.mp (List.get_mem _ k))
  · intro k j hkj
    exfalso
    apply hkj
    apply Fin.ext
    have hk := k.isLt; have hj := j.isLt
    simp [quantum] at hk hj
    omega

private lemma classical_transmits : Transmits example42 (classical 3) := by
  let e : Block (classical 3) ≃ Fin 3 := finCongr (by simp [classical,equalBlocks])
  apply (orthogonal_codes _ channel (classical 3) (valid_classical 3 (by omega))).mpr
  refine ⟨fun k => R (e k),fun k => ⟨codeR _,?_⟩,?_⟩
  · have hm : blockSize (classical 3) k ∈ Multiset.replicate 3 1 :=
      Multiset.mem_toList.mp (List.get_mem _ k)
    exact (rankR _).trans (Multiset.eq_of_mem_replicate hm).symm
  · intro k j hkj X hX
    exact orthR _ _ (fun h => hkj (e.injective h)) X hX

private lemma length_bound (A : Shape) (hA : Transmits example42 A) : lengthDim A ≤ 3 := by
  have hb := ((kraus_geometric_converse E normalized A hA).2.2.1 1 (by omega)).1
  have hs : (∑ k : Block A, blockSize A k) = lengthDim A := by
    unfold blockSize lengthDim
    rw [← List.sum_ofFn,List.ofFn_get,Multiset.sum_toList]
  have hf : univ.filter (fun k : Block A => 1 ≤ blockSize A k) = univ := by
    apply Finset.filter_eq_self.mpr
    intro k _
    exact hA.1.2 _ (Multiset.mem_toList.mp (List.get_mem _ k))
  rw [hf,hs] at hb
  exact hb.trans (by simpa using (Submodule.finrank_le (⨆ i : {i : Fin 3 // 1 ≤ (E i).rank},
    imageSpace (E i.val) : Submodule ℂ (EuclideanSpace ℂ (Fin 3)))))

private lemma e_ranks (i : Fin 3) : (E i).rank = if i = 0 then 2 else 1 := by
  have h0 : (E 0).rank = 2 := by
    rw [← Matrix.rank_conjTranspose_mul_self,e00]
    exact rankQ
  have h1 : (E 1).rank = 1 := by
    rw [← Matrix.rank_conjTranspose_mul_self,e11]
    exact rankR 1
  have h2 : (E 2).rank = 1 := by
    rw [← Matrix.rank_conjTranspose_mul_self,e22]
    exact rankR 2
  fin_cases i
  · simpa [Fin.ext_iff] using h0
  · simpa [Fin.ext_iff] using h1
  · simpa [Fin.ext_iff] using h2

private lemma cross_positive (j : Fin 3) : 1 ≤ ((E 0)ᴴ * E j).rank := by
  have hn : (E 0)ᴴ * E j ≠ 0 := by
    intro h
    fin_cases j
    all_goals rw [effects] at h
    · have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 1 1) h
      norm_num [Q,unit,Matrix.single_apply,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply] at hh
    · have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 1 2) h
      norm_num [c,unit,Matrix.single_apply,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply] at hh
    · have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 1 3) h
      norm_num [c,unit,Matrix.single_apply,Fin.ext_iff,Matrix.cons_val,Matrix.head_cons,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.tail_cons,Matrix.of_apply] at hh
  have hr : ((E 0)ᴴ * E j).rank ≠ 0 := by
    intro hz
    have hb : LinearMap.range (((E 0)ᴴ * E j).mulVecLin) = ⊥ :=
      Submodule.finrank_eq_zero.mp hz
    have hl := LinearMap.range_eq_bot.mp hb
    apply hn
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply',Matrix.toLin'_apply',Matrix.mulVecLin_zero]
    exact hl
  omega

private lemma excludes21 : ¬ Transmits example42 (quantum 2 + quantum 1) := by
  intro h
  obtain ⟨i,j,hi,_,hij,hcross,_⟩ := (sequential_converse E normalized).2 2 1 (by omega) (by omega) h
  have hi0 : i = 0 := by
    rw [e_ranks] at hi
    split_ifs at hi with hh
    · exact hh
    · omega
  subst i
  have hj := e_ranks j
  by_cases he : j = 0
  · subst j
    have hh := hij rfl
    norm_num [e_ranks] at hh
  · rw [if_neg he] at hj
    have hc := hcross (by simp [e_ranks])
    have hp := cross_positive j
    omega

private lemma block_bound (A : Shape) (hA : Transmits example42 A) : ∀ d ∈ A, d ≤ 2 := by
  intro d hd
  obtain ⟨k,hk⟩ := List.get_of_mem (Multiset.mem_toList.mpr hd)
  have hb := (kraus_geometric_converse E normalized A hA).2.1 k
  change A.toList.get k ≤ _ at hb
  rw [hk] at hb
  exact hb.trans (Finset.sup_le fun i _ => by rw [e_ranks]; split_ifs <;> omega)

private lemma enum_list (L : List ℕ) (hp : ∀ a ∈ L, 0 < a) (hs : L.sum ≤ 3) :
    L = [] ∨ L = [1] ∨ L = [2] ∨ L = [3] ∨ L = [1,1] ∨ L = [1,2] ∨ L = [2,1] ∨ L = [1,1,1] := by
  rcases L with _ | ⟨a,L⟩
  · simp
  have ha := hp a (by simp)
  rcases L with _ | ⟨b,L⟩
  · simp only [List.sum_cons,List.sum_nil,add_zero] at hs
    interval_cases a <;> simp_all
  have hb := hp b (by simp)
  rcases L with _ | ⟨d,L⟩
  · simp only [List.sum_cons,List.sum_nil,add_zero] at hs
    have ha2 : a ≤ 2 := by omega
    have hb2 : b ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> simp_all
  have hd := hp d (by simp)
  rcases L with _ | ⟨e,L⟩
  · simp only [List.sum_cons,List.sum_nil,add_zero] at hs
    have haa : a = 1 := by omega
    have hbb : b = 1 := by omega
    have hdd : d = 1 := by omega
    simp [haa,hbb,hdd]
  have he := hp e (by simp)
  simp only [List.sum_cons] at hs
  omega

private lemma classified (A : Shape) (hA : Transmits example42 A) :
    A = classical 1 ∨ A = classical 2 ∨ A = classical 3 ∨ A = quantum 2 := by
  have hs := length_bound A hA
  have hen := enum_list A.toList (fun a ha => hA.1.2 a (Multiset.mem_toList.mp ha))
    (by simpa [lengthDim] using hs)
  rcases hen with h | h | h | h | h | h | h | h
  · have hz : A = 0 := by rw [← Multiset.coe_toList A,h]; rfl
    exact (hA.1.1 hz).elim
  · left; rw [← Multiset.coe_toList A,h]; rfl
  · right; right; right; rw [← Multiset.coe_toList A,h]; rfl
  · have hh := block_bound A hA 3 (by rw [← Multiset.coe_toList A,h]; simp)
    omega
  · right; left; rw [← Multiset.coe_toList A,h]; rfl
  · apply False.elim
    apply excludes21
    have he : A = quantum 2 + quantum 1 := by
      rw [← Multiset.coe_toList A,h]; simp [quantum,add_comm]; rfl
    rwa [← he]
  · apply False.elim
    apply excludes21
    have he : A = quantum 2 + quantum 1 := by rw [← Multiset.coe_toList A,h]; rfl
    rwa [← he]
  · right; right; left; rw [← Multiset.coe_toList A,h]; rfl

private lemma known_valid (A : Shape) (h : A = classical 1 ∨ A = classical 2 ∨ A = classical 3 ∨ A = quantum 2) :
    Valid A ∧ ∀ d ∈ A, d ≤ 3 := by
  rcases h with rfl | rfl | rfl | rfl
  all_goals constructor
  · exact valid_classical _ (by omega)
  · simp [classical,equalBlocks]
  · exact valid_classical _ (by omega)
  · simp [classical,equalBlocks]
  · exact valid_classical _ (by omega)
  · simp [classical,equalBlocks]
  · exact valid_quantum _ (by omega)
  · simp [quantum]

private lemma comparisons (A B : Shape)
    (hA : A = classical 1 ∨ A = classical 2 ∨ A = classical 3 ∨ A = quantum 2)
    (hB : B = classical 1 ∨ B = classical 2 ∨ B = classical 3 ∨ B = quantum 2) :
    Embeds A B ↔ ∀ d ∈ Icc 1 3,
      (A.map (fun n => n/d)).sum ≤ (B.map (fun n => n/d)).sum := by
  obtain ⟨ha,ha3⟩ := known_valid A hA
  obtain ⟨hb,hb3⟩ := known_valid B hB
  rw [small_block_embedding B A hb ha hb3 ha3]
  apply forall₂_congr
  intro d hd
  rw [(equal_block_packing A ha d (by have := (mem_Icc.mp hd).1; omega)).1,
    (equal_block_packing B hb d (by have := (mem_Icc.mp hd).1; omega)).1]

private lemma range3 : (Icc 1 3 : Finset ℕ) = {1,2,3} := by decide
private lemma to_classical (d : ℕ) (hd : d = 1 ∨ d = 2) : Embeds (classical d) (classical 3) := by
  rcases hd with rfl | rfl
  all_goals rw [comparisons _ _ (by simp) (by simp)]
  all_goals norm_num [range3,classical,equalBlocks]

private lemma quantum2_transmits : Transmits example42 (quantum 2) :=
  quantum_transmits channel 2 (by omega) Q codeQ rankQ

private lemma quantum_maximal : Maximal example42 (quantum 2) := by
  refine ⟨(quantum_transmits channel 2 (by omega) Q codeQ rankQ),?_⟩
  intro B hB he
  rcases classified B hB with rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals
    have hh := (comparisons _ _ (by simp) (by simp)).mp he 2 (by decide)
    norm_num [quantum,classical,equalBlocks] at hh

private lemma classical_maximal : Maximal example42 (classical 3) := by
  refine ⟨classical_transmits,?_⟩
  intro B hB he
  rcases classified B hB with rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals
    have hh := (comparisons _ _ (by simp) (by simp)).mp he 1 (by decide)
    norm_num [quantum,classical,equalBlocks] at hh

private lemma conclusion :
    maximals example42 = {quantum 2, classical 3} ∧ ¬ HasDominating example42 := by
  refine ⟨?_,?_⟩
  · ext A
    constructor
    · intro hA
      rcases classified A hA.1 with rfl | rfl | rfl | rfl
      · have hh := hA.2 _ classical_transmits (to_classical 1 (by omega))
        have hc := congrArg Multiset.card hh
        norm_num [classical,equalBlocks] at hc
      · have hh := hA.2 _ classical_transmits (to_classical 2 (by omega))
        have hc := congrArg Multiset.card hh
        norm_num [classical,equalBlocks] at hc
      · simp
      · simp
    · intro h
      rcases (Set.mem_insert_iff.mp h) with rfl | h
      · exact quantum_maximal
      · have hh := Set.mem_singleton_iff.mp h
        subst A
        exact classical_maximal
  · rintro ⟨A,hA,hd⟩
    have hq := hd _ quantum2_transmits
    have hc := hd _ classical_transmits
    rcases classified A hA with rfl | rfl | rfl | rfl
    · have hh := (comparisons _ _ (by simp) (by simp)).mp hq 2 (by decide)
      norm_num [quantum,classical,equalBlocks] at hh
    · have hh := (comparisons _ _ (by simp) (by simp)).mp hq 2 (by decide)
      norm_num [quantum,classical,equalBlocks] at hh
    · have hh := (comparisons _ _ (by simp) (by simp)).mp hq 2 (by decide)
      norm_num [quantum,classical,equalBlocks] at hh
    · have hh := (comparisons _ _ (by simp) (by simp)).mp hc 1 (by decide)
      norm_num [quantum,classical,equalBlocks] at hh

theorem solution : IsChannel example42 ∧
    maximals example42 = {quantum 2, classical 3} ∧ ¬ HasDominating example42 := by
  exact ⟨channel,conclusion⟩

#print axioms solution
