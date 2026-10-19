-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.negative_reconstruction_example
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:26:16.352524+00:00
-- url     : https://prove2.me/submissions/c9b42686-5ac5-4746-a129-131dbb92cf6e

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_kraus_geometric_converse

set_option autoImplicit false
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
      Matrix.conjTranspose_apply,Matrix.single_apply,ite_and] using hh
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

private def E : Fin 3 → Matrix (Fin 7) (Fin 7) ℂ :=
  ![unit 0 0 + unit 1 1 + unit 2 2, unit 0 3 + unit 1 4, unit 2 5 + unit 6 6]
private lemma neg_def : krausApply E = negativeExample := rfl

private def DP (S : Finset (Fin 7)) : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.diagonal (fun a => if a ∈ S then 1 else 0)
private lemma diag_proj (S : Finset (Fin 7)) : IsProjection (DP S) := by
  constructor
  · ext a b; simp [DP,Matrix.conjTranspose_apply,Matrix.diagonal_apply]; split_ifs <;> simp_all
  · rw [DP,Matrix.diagonal_mul_diagonal]
    congr 1; funext a; split_ifs <;> simp
private lemma diag_rank (S : Finset (Fin 7)) : (DP S).rank = S.card := by
  have h := h62_trace_idem (DP S) (diag_proj S).2
  have ht : (DP S).trace = (S.card : ℂ) := by simp [DP,Matrix.trace_diagonal]
  exact_mod_cast h.symm.trans ht
private lemma diag_sandwich (S T : Finset (Fin 7)) (X : Matrix (Fin 7) (Fin 7) ℂ) (a b : Fin 7) :
    (DP S * X * DP T) a b = if a ∈ S ∧ b ∈ T then X a b else 0 := by
  simp only [DP,Matrix.diagonal_mul,Matrix.mul_diagonal]
  split_ifs <;> simp_all

private lemma effects (i j : Fin 3) : (E i)ᴴ * E j =
    ![![unit 0 0 + unit 1 1 + unit 2 2, unit 0 3 + unit 1 4, unit 2 5],
      ![unit 3 0 + unit 4 1,unit 3 3 + unit 4 4,0],
      ![unit 5 2,0,unit 5 5 + unit 6 6]] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [E,unit,Matrix.conjTranspose_add,Matrix.add_mul,Matrix.mul_add,
      Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne]

private lemma normalized : IsKrausFamily E := by
  change (∑ i, (E i)ᴴ * E i) = 1
  simp only [Fin.sum_univ_three,effects,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [unit,Matrix.single_apply,Matrix.one_apply,Fin.ext_iff]
private lemma channel : IsChannel negativeExample := ⟨3,E,normalized,fun _ => rfl⟩

private lemma code_of_effects (S : Finset (Fin 7))
    (h : ∀ i j, ∃ c : ℂ, DP S * ((E i)ᴴ * E j) * DP S = c • DP S) :
    Code (graph negativeExample) (DP S) := by
  refine ⟨diag_proj S,?_⟩
  intro X hX
  have hh := kraus_graph_le E (show X ∈ graph (krausApply E) from hX)
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
private lemma orth_of_effects (S T : Finset (Fin 7))
    (h : ∀ i j, DP S * ((E i)ᴴ * E j) * DP T = 0)
    (X : Matrix (Fin 7) (Fin 7) ℂ) (hX : X ∈ graph negativeExample) :
    DP S * X * DP T = 0 := by
  have hh := kraus_graph_le E (show X ∈ graph (krausApply E) from hX)
  clear hX
  induction hh using Submodule.span_induction with
  | mem X hX => obtain ⟨⟨i,j⟩,rfl⟩ := hX; exact h i j
  | zero => simp
  | add X Y hX hY iX iY => simp [Matrix.mul_add,Matrix.add_mul,iX,iY]
  | smul c X hX iX => simp [iX]

private def S3 : Finset (Fin 7) := {0,1,2}
private def S2 (k : Fin 2) : Finset (Fin 7) := if k = 0 then {3,4} else {5,6}
private def S1 (k : Fin 4) : Finset (Fin 7) := {![0,1,2,6] k}

private lemma sandwich_scalar (S : Finset (Fin 7)) (X : Matrix (Fin 7) (Fin 7) ℂ) (c : ℂ)
    (h : ∀ a ∈ S, ∀ b ∈ S, X a b = if a = b then c else 0) :
    DP S * X * DP S = c • DP S := by
  ext a b
  rw [diag_sandwich]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · rw [if_pos ⟨ha,hb⟩,h a ha b hb]
    simp [DP,Matrix.diagonal_apply,ha]
  · have hab : a ≠ b := by intro hh; subst b; exact hb ha
    simp [DP,ha,hb,hab]
  · simp [DP,Matrix.diagonal_apply,ha,hb]
  · simp [DP,Matrix.diagonal_apply,ha,hb]
private lemma sandwich_zero (S T : Finset (Fin 7)) (X : Matrix (Fin 7) (Fin 7) ℂ)
    (h : ∀ a ∈ S, ∀ b ∈ T, X a b = 0) : DP S * X * DP T = 0 := by
  ext a b
  rw [diag_sandwich]
  split_ifs with hh
  · exact h a hh.1 b hh.2
  · rfl

private lemma code3 : Code (graph negativeExample) (DP S3) := by
  apply code_of_effects
  intro i j
  refine ⟨if i = 0 ∧ j = 0 then 1 else 0,?_⟩
  apply sandwich_scalar
  intro a ha b hb
  simp only [S3,mem_insert,mem_singleton] at ha hb
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl <;>
    fin_cases i <;> fin_cases j <;>
    simp [effects,unit,Fin.ext_iff,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
private lemma code2 (k : Fin 2) : Code (graph negativeExample) (DP (S2 k)) := by
  apply code_of_effects
  intro i j
  refine ⟨if i = j ∧ i.val = k.val + 1 then 1 else 0,?_⟩
  apply sandwich_scalar
  intro a ha b hb
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp_all [S2,Fin.ext_iff]
  all_goals fin_cases i <;> fin_cases j <;>
    simp [effects,unit,Fin.ext_iff,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
private lemma orth2 (k l : Fin 2) (hkl : k ≠ l)
    (X : Matrix (Fin 7) (Fin 7) ℂ) (hX : X ∈ graph negativeExample) :
    DP (S2 k) * X * DP (S2 l) = 0 := by
  apply orth_of_effects _ _ ?_ X hX
  intro i j
  apply sandwich_zero
  intro a ha b hb
  fin_cases k <;> fin_cases l <;> norm_num at hkl
  all_goals fin_cases a <;> fin_cases b <;> simp_all [S2,Fin.ext_iff]
  all_goals fin_cases i <;> fin_cases j <;>
    simp [effects,unit,Fin.ext_iff,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

private lemma code1 (k : Fin 4) : Code (graph negativeExample) (DP (S1 k)) := by
  apply code_of_effects
  intro i j
  refine ⟨((E i)ᴴ * E j) (![0,1,2,6] k) (![0,1,2,6] k),?_⟩
  ext a b
  rw [diag_sandwich]
  simp only [S1,mem_singleton,Matrix.smul_apply,DP,Matrix.diagonal_apply,smul_eq_mul]
  split_ifs <;> simp_all
private lemma orth1 (k l : Fin 4) (hkl : k ≠ l)
    (X : Matrix (Fin 7) (Fin 7) ℂ) (hX : X ∈ graph negativeExample) :
    DP (S1 k) * X * DP (S1 l) = 0 := by
  apply orth_of_effects _ _ ?_ X hX
  intro i j
  ext a b
  rw [diag_sandwich,effects]
  simp only [S1,mem_singleton,Matrix.zero_apply]
  split_ifs with h
  · obtain ⟨rfl,rfl⟩ := h
    fin_cases k <;> fin_cases l <;> norm_num at hkl
    all_goals fin_cases i <;> fin_cases j <;>
      norm_num [unit,Matrix.single_apply,Fin.ext_iff,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · rfl

private lemma valid_equal (d c : ℕ) (hd : 0 < d) (hc : 0 < c) : Valid (equalBlocks d c) := by
  constructor
  · intro hz; have h := congrArg Multiset.card hz; simp [equalBlocks] at h; omega
  · intro a ha; have h : a = d := Multiset.eq_of_mem_replicate ha; omega
private lemma quantum_transmits : Transmits negativeExample (quantum 3) := by
  apply (orthogonal_codes negativeExample channel (quantum 3) (by simp [Valid,quantum])).mpr
  refine ⟨fun _ => DP S3,fun k => ⟨code3,?_⟩,?_⟩
  · rw [diag_rank]
    have h : blockSize (quantum 3) k = 3 :=
      Multiset.mem_singleton.mp (Multiset.mem_toList.mp (List.get_mem _ k))
    norm_num [S3,h,Fin.ext_iff]
  · intro k j hkj
    exfalso
    apply hkj
    apply Fin.ext
    have hk := k.isLt; have hj := j.isLt
    simp [quantum] at hk hj
    omega
private lemma two_transmits : Transmits negativeExample (equalBlocks 2 2) := by
  classical
  let e : Block (equalBlocks 2 2) ≃ Fin 2 := finCongr (by simp [equalBlocks])
  apply (orthogonal_codes negativeExample channel _ (valid_equal 2 2 (by omega) (by omega))).mpr
  refine ⟨fun k => DP (S2 (e k)),fun k => ⟨code2 _,?_⟩,?_⟩
  · rw [diag_rank]
    have h : blockSize (equalBlocks 2 2) k = 2 :=
      Multiset.eq_of_mem_replicate (Multiset.mem_toList.mp (List.get_mem _ k))
    rw [h]; simp only [S2]; split_ifs <;> norm_num [Fin.ext_iff]
  · intro k j hkj X hX
    exact orth2 _ _ (fun h => hkj (e.injective h)) X hX
private lemma four_transmits : Transmits negativeExample (equalBlocks 1 4) := by
  classical
  let e : Block (equalBlocks 1 4) ≃ Fin 4 := finCongr (by simp [equalBlocks])
  apply (orthogonal_codes negativeExample channel _ (valid_equal 1 4 (by omega) (by omega))).mpr
  refine ⟨fun k => DP (S1 (e k)),fun k => ⟨code1 _,?_⟩,?_⟩
  · rw [diag_rank]
    have h : blockSize (equalBlocks 1 4) k = 1 :=
      Multiset.eq_of_mem_replicate (Multiset.mem_toList.mp (List.get_mem _ k))
    simp [h,S1]
  · intro k j hkj X hX
    exact orth1 _ _ (fun h => hkj (e.injective h)) X hX

private lemma rank_image {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M : Matrix O I ℂ) :
    M.rank = Module.finrank ℂ (imageSpace M) := by
  rw [Matrix.rank_eq_finrank_range_toLin M
    (EuclideanSpace.basisFun O ℂ).toBasis (EuclideanSpace.basisFun I ℂ).toBasis]
  rfl
private lemma DP_units (S : Finset (Fin 7)) : DP S = ∑ i ∈ S, unit i i := by
  unfold DP
  rw [← Matrix.sum_single_eq_diagonal]
  have h (i : Fin 7) : Matrix.single i i (if i ∈ S then (1:ℂ) else 0) =
      if i ∈ S then unit i i else 0 := by
    split_ifs <;> simp [unit]
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp
private lemma ranks (i : Fin 3) : (E i).rank = if i = 0 then 3 else 2 := by
  have he : (E i)ᴴ * E i = DP (if i = 0 then S3 else if i = 1 then {3,4} else {5,6}) := by
    fin_cases i <;> simp [effects,DP_units,S3,Fin.ext_iff,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,add_assoc]
  rw [← Matrix.rank_conjTranspose_mul_self,he,diag_rank]
  fin_cases i <;> norm_num [S3,Fin.ext_iff]

private lemma output : krausApply E 1 = Matrix.diagonal (![2,2,2,0,0,0,1] : Fin 7 → ℂ) := by
  simp [krausApply,Fin.sum_univ_three,E,unit,Matrix.conjTranspose_add,
    Matrix.add_mul,Matrix.mul_add,Matrix.single_mul_single_of_ne]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.single_apply,Matrix.diagonal_apply,Fin.ext_iff]
private lemma output_rank : (krausApply E 1).rank = 4 := by
  rw [output,Matrix.rank_diagonal,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  norm_num [Fin.sum_univ_succ,Matrix.cons_val,Matrix.cons_val_zero]

private lemma length_bound (A : Shape) (hA : Transmits negativeExample A) : lengthDim A ≤ 4 := by
  have hh := kraus_geometric_converse E normalized A hA
  have hpos (k : Block A) : 1 ≤ blockSize A k :=
    hA.1.2 _ (Multiset.mem_toList.mp (List.get_mem _ k))
  have hf : univ.filter (fun k : Block A => 1 ≤ blockSize A k) = univ := by
    ext k; simp [hpos]
  have hsum : ∑ k : Block A, blockSize A k = lengthDim A := by
    unfold blockSize lengthDim
    rw [← List.sum_ofFn,List.ofFn_get,Multiset.sum_toList]
  have hb := (hh.2.2.1 1 (by omega)).1
  rw [hf,hsum] at hb
  calc lengthDim A ≤ _ := hb
    _ ≤ Module.finrank ℂ (⨆ i : Fin 3, imageSpace (E i) : Submodule ℂ (EuclideanSpace ℂ (Fin 7))) :=
      Submodule.finrank_mono (show (⨆ i : {i : Fin 3 // 1 ≤ (E i).rank}, imageSpace (E i.val) : Submodule ℂ (EuclideanSpace ℂ (Fin 7))) ≤ ⨆ i : Fin 3, imageSpace (E i) from
        iSup_le fun i => le_iSup (fun j : Fin 3 => imageSpace (E j)) i.val)
    _ = 4 := by rw [hh.2.2.2,← rank_image,output_rank]

private lemma quantum_bound (d : ℕ) (hd : Transmits negativeExample (quantum d)) : d ≤ 3 := by
  have hh := (kraus_geometric_converse E normalized _ hd).2.1
  let k : Block (quantum d) := ⟨0,by simp [quantum]⟩
  have hk : blockSize (quantum d) k = d :=
    Multiset.mem_singleton.mp (Multiset.mem_toList.mp (List.get_mem _ k))
  have h := hh k
  rw [hk] at h
  exact h.trans (Finset.sup_le (fun i _ => by rw [ranks]; split_ifs <;> omega))

private lemma dmax_value : dmax negativeExample = 3 := by
  unfold dmax
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    exact quantum_bound d.val (Finset.mem_filter.mp hd).2
  · exact Finset.le_sup (f := Fin.val) (show (⟨3,by simp⟩ : Fin (Fintype.card (Fin 7) + 1)) ∈
      univ.filter (fun d => Transmits negativeExample (quantum d.val)) from
        mem_filter.mpr ⟨mem_univ _,quantum_transmits⟩)
private lemma hybrid_bound (d : ℕ) (hd : 0 < d) : hybrid negativeExample d ≤ 4 / d := by
  unfold hybrid
  rw [if_neg (by omega)]
  apply Finset.sup_le
  intro c hc
  apply (Nat.le_div_iff_mul_le hd).mpr
  have h := length_bound _ (Finset.mem_filter.mp hc).2
  simpa [lengthDim,equalBlocks,Multiset.sum_replicate,nsmul_eq_mul] using h

private lemma hybrid_lower (d c : ℕ) (hd : d ≠ 0) (hc : c ≤ 7)
    (h : Transmits negativeExample (equalBlocks d c)) : c ≤ hybrid negativeExample d := by
  unfold hybrid
  rw [if_neg hd]
  exact Finset.le_sup (f := Fin.val) (show (⟨c,by simp; omega⟩ : Fin (Fintype.card (Fin 7) + 1)) ∈
    univ.filter (fun n => Transmits negativeExample (equalBlocks d n.val)) from
      mem_filter.mpr ⟨mem_univ _,h⟩)
private lemma hybrid1 : hybrid negativeExample 1 = 4 := by
  apply le_antisymm
  · simpa using hybrid_bound 1 (by omega)
  · exact hybrid_lower 1 4 (by omega) (by omega) four_transmits
private lemma hybrid2 : hybrid negativeExample 2 = 2 := by
  apply le_antisymm
  · simpa using hybrid_bound 2 (by omega)
  · exact hybrid_lower 2 2 (by omega) (by omega) two_transmits
private lemma hybrid3 : hybrid negativeExample 3 = 1 := by
  apply le_antisymm
  · simpa using hybrid_bound 3 (by omega)
  · apply hybrid_lower 3 1 (by omega) (by omega)
    simpa [equalBlocks,quantum] using quantum_transmits

private lemma mult3 : QAlgorithms.Papers.Independent.Information100.P62.multiplicity negativeExample 3 = 1 := by
  norm_num [QAlgorithms.Papers.Independent.Information100.P62.multiplicity,dmax_value,reconstruction,hybrid1,hybrid2,hybrid3,
    Finset.sum_Icc_succ_top]
private lemma mult2 : QAlgorithms.Papers.Independent.Information100.P62.multiplicity negativeExample 2 = 1 := by
  norm_num [QAlgorithms.Papers.Independent.Information100.P62.multiplicity,dmax_value,reconstruction,hybrid1,hybrid2,hybrid3,
    Finset.sum_Icc_succ_top]
private lemma mult1 : QAlgorithms.Papers.Independent.Information100.P62.multiplicity negativeExample 1 = -1 := by
  norm_num [QAlgorithms.Papers.Independent.Information100.P62.multiplicity,dmax_value,reconstruction,hybrid1,hybrid2,hybrid3,
    Finset.sum_Icc_succ_top]

theorem solution :
    IsChannel negativeExample ∧ Transmits negativeExample (quantum 3) ∧
    Transmits negativeExample (equalBlocks 2 2) ∧ dmax negativeExample = 3 ∧
    hybrid negativeExample 1 = 4 ∧ hybrid negativeExample 2 = 2 ∧ hybrid negativeExample 3 = 1 ∧
    QAlgorithms.Papers.Independent.Information100.P62.multiplicity negativeExample 3 = 1 ∧ QAlgorithms.Papers.Independent.Information100.P62.multiplicity negativeExample 2 = 1 ∧
    QAlgorithms.Papers.Independent.Information100.P62.multiplicity negativeExample 1 = -1 ∧ capacityAlgebra negativeExample = none := by
  refine ⟨channel,quantum_transmits,two_transmits,dmax_value,hybrid1,hybrid2,hybrid3,
    mult3,mult2,mult1,?_⟩
  apply if_neg
  intro h
  have hh := h 1 (by simp [dmax_value])
  rw [mult1] at hh
  norm_num at hh
