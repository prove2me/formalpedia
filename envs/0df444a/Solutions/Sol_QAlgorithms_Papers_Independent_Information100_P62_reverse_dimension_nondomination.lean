-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.reverse_dimension_nondomination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:05:06.079828+00:00
-- url     : https://prove2.me/submissions/f359647c-e272-47ab-bb3d-262cf650a4fe

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_full_support_converse
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_equal_block_packing
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_small_block_embedding

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

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

#print axioms kraus_graph_le

private def c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
private lemma c_def : (Real.sqrt 2 : ℂ)⁻¹ = c := rfl
private lemma cs : conj c = c := by simp [c]
private lemma cc : c * c = (1 / 2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  unfold c
  rw [← pow_two,inv_pow,hs]
  norm_num

private def D : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1,0,-1]

private lemma effects (i j : Fin 2) :
    (example43Kraus i)ᴴ * example43Kraus j =
      if i = j then if i = 0 then (1/2 : ℂ) • (1 + D) else (1/2 : ℂ) • (1 - D) else 0 := by
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [example43Kraus,unit,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.single_apply,Fin.ext_iff,Fin.sum_univ_four,Matrix.of_apply,D,Matrix.diagonal, c_def,cs,cc]

private lemma normalized : IsKrausFamily example43Kraus := by
  change (∑ i, (example43Kraus i)ᴴ * example43Kraus i) = 1
  simp only [Fin.sum_univ_two,effects,ite_true,Fin.isValue]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [D,Matrix.diagonal,Matrix.of_apply]

private lemma channel : IsChannel example43 := ⟨2,example43Kraus,normalized,fun _ => rfl⟩

private lemma graph_form (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X ∈ graph example43) :
    ∃ a b : ℂ, X = a • (1 : Matrix (Fin 3) (Fin 3) ℂ) + b • D := by
  have hh : X ∈ Submodule.span ℂ (Set.range (fun p : Fin 2 × Fin 2 =>
      (example43Kraus p.1)ᴴ * example43Kraus p.2)) := kraus_graph_le example43Kraus hX
  clear hX
  induction hh using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨⟨i,j⟩,rfl⟩ := hX
      change ∃ a b, (example43Kraus i)ᴴ * example43Kraus j = a • 1 + b • D
      fin_cases i <;> fin_cases j <;> rw [effects] <;> norm_num
      · exact ⟨1/2,1/2,by simp⟩
      · exact ⟨0,0,by simp⟩
      · exact ⟨0,0,by simp⟩
      · exact ⟨1/2,-(1/2),by simp [smul_add,sub_eq_add_neg]⟩
  | zero => exact ⟨0,0,by simp⟩
  | add X Y hX hY iX iY =>
      obtain ⟨a,b,rfl⟩ := iX; obtain ⟨d,e,rfl⟩ := iY
      exact ⟨a+d,b+e,by simp [add_smul]; abel⟩
  | smul z X hX iX =>
      obtain ⟨a,b,rfl⟩ := iX
      exact ⟨z*a,z*b,by simp [smul_add,smul_smul]⟩

private theorem h62_trace_idem {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (h : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [← Matrix.trace_toLin_eq P (Pi.basisFun ℂ n), Matrix.toLin_eq_toLin', this, Matrix.rank]
  rfl

private theorem h62_rank_pos {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (h : P * P = P)
    (h0 : P ≠ 0) : 1 ≤ P.rank := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  by_contra hc
  have h1 : P.trace = 0 := by rw [h62_trace_idem P h]; simp; omega
  rw [← Matrix.trace_toLin_eq P (Pi.basisFun ℂ n), Matrix.toLin_eq_toLin', LinearMap.IsIdempotentElem.trace_eq_zero_iff hi] at h1
  exact h0 (Matrix.toLin'.injective (by rw [h1, map_zero]))

private theorem h62_pos (A : Shape) (hA : ∀ d ∈ A, 0 < d) (k : Block A) : 0 < blockSize A k :=
  hA _ (Multiset.mem_toList.mp (List.get_mem _ _))

private theorem h62_one (A : Shape) :
    (1 : Algebra A) = ∑ k : Block A, ∑ α : Fin (blockSize A k),
      (Pi.single k (Matrix.single α α (1:ℂ)) : Algebra A) := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · rw [Finset.sum_apply]
    simp only [Pi.single_eq_same]
    ext a b
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp [Finset.filter_eq']
    · simp only [h, if_false]
      rw [eq_comm, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨rfl, rfl⟩; exact h rfl
  · intro b _ hb
    rw [Finset.sum_apply]
    simp [Pi.single_eq_of_ne' hb]
  · simp

private theorem h62_sum_blocks (A : Shape) : ∑ k : Block A, blockSize A k = lengthDim A := by
  unfold blockSize lengthDim
  rw [← List.sum_ofFn, List.ofFn_get, Multiset.sum_toList]

variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

private theorem input_bound (A : Shape) (hA : Valid A)
    (f : Algebra A →ₗ[ℂ] Matrix I I ℂ) (hf : Faithful f) : lengthDim A ≤ Fintype.card I := by
  let z : ∀ k : Block A, Fin (blockSize A k) := fun k => ⟨0, h62_pos A hA.2 k⟩
  let e : ∀ k : Block A, Fin (blockSize A k) → Fin (blockSize A k) → Algebra A :=
    fun k a b => Pi.single k (Matrix.single a b 1)
  have emul : ∀ k a b c, e k a b * e k b c = e k a c := by
    intro k a b c
    simp only [e, ← Pi.single_mul, Matrix.single_mul_single_same, mul_one]
  have idem : ∀ X : Algebra A, X * X = X → f X * f X = f X := by
    intro X hX; rw [← hf.2.1, hX]
  have tr : ∀ k a, (f (e k a a)).trace = (f (e k (z k) (z k))).trace := by
    intro k a
    rw [← emul k a (z k) a, ← emul k (z k) a (z k), hf.2.1, hf.2.1, Matrix.trace_mul_comm]
  have he : ∀ k, 1 ≤ (f (e k (z k) (z k))).rank := by
    intro k
    apply h62_rank_pos _ (idem _ (emul _ _ _ _))
    intro hz
    have h0 : e k (z k) (z k) = 0 := hf.1 (by rw [hz, map_zero])
    have := congrFun (congrFun (congrFun h0 k) (z k)) (z k)
    simp [e] at this
  have htrace : ((∑ k, (f (e k (z k) (z k))).rank * blockSize A k : ℕ) : ℂ) =
      ((f 1).rank : ℂ) := by
    rw [← h62_trace_idem _ (idem 1 (mul_one 1)), h62_one A, map_sum, Matrix.trace_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [map_sum, Matrix.trace_sum]
    have htr : ∀ a, (f (e k a a)).trace = ((f (e k (z k) (z k))).rank : ℂ) := by
      intro a; rw [tr, h62_trace_idem _ (idem _ (emul _ _ _ _))]
    simp only [e] at htr
    simp [htr, mul_comm]
    exact Or.inl rfl
  calc lengthDim A = ∑ k : Block A, blockSize A k := (h62_sum_blocks A).symm
    _ ≤ ∑ k, (f (e k (z k) (z k))).rank * blockSize A k :=
      Finset.sum_le_sum (fun k _ => Nat.le_mul_of_pos_left _ (he k))
    _ = (f 1).rank := Nat.cast_injective htrace
    _ ≤ Fintype.card I := Matrix.rank_le_card_width _

omit [DecidableEq O] in
private theorem transmits_bound (F : Superop I O) (A : Shape) (hA : Transmits F A) :
    lengthDim A ≤ Fintype.card I := by
  obtain ⟨ha, f, hf, -⟩ := hA
  exact input_bound A ha f hf


private lemma valid_quantum (d : ℕ) (hd : 0 < d) : Valid (quantum d) := by
  simp [Valid,quantum,hd]
private lemma valid_classical (d : ℕ) (hd : 0 < d) : Valid (classical d) := by
  constructor
  · intro hz; have hh := congrArg Multiset.card hz; simp [classical,equalBlocks] at hh; omega
  · intro a ha; have hh : a = 1 := Multiset.eq_of_mem_replicate ha; omega

private def P : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/2,0,1/2; 0,1,0; 1/2,0,1/2]
private lemma projP : IsProjection P := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [P,Matrix.conjTranspose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [P,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.ext_iff,Fin.sum_univ_three,Matrix.cons_val_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
private lemma rankP : P.rank = 2 := by
  have hh := h62_trace_idem P projP.2
  have ht : P.trace = 2 := by norm_num [P,Matrix.trace,Fin.sum_univ_three,Matrix.cons_val_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  exact_mod_cast hh.symm.trans ht
private lemma PDP : P * D * P = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [P,D,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.ext_iff,Fin.sum_univ_three,Matrix.of_apply,Matrix.cons_val_two,Matrix.head_cons]
private lemma codeP : Code (graph example43) P := by
  refine ⟨projP,?_⟩
  intro X hX
  obtain ⟨a,b,rfl⟩ := graph_form X hX
  refine ⟨a,?_⟩
  rw [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.mul_smul,
    Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_one,projP.2,PDP,smul_zero,add_zero]

private lemma quantum_transmits : Transmits example43 (quantum 2) := by
  apply (orthogonal_codes example43 channel (quantum 2) (valid_quantum 2 (by omega))).mpr
  refine ⟨fun _ => P,fun k => ⟨codeP,?_⟩,?_⟩
  · rw [rankP]
    symm
    exact Multiset.mem_singleton.mp (Multiset.mem_toList.mp (List.get_mem _ k))
  · intro k j hkj
    exfalso
    apply hkj
    apply Fin.ext
    have hk := k.isLt; have hj := j.isLt
    simp [quantum] at hk hj
    omega

private def Q (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i => if i = a then 1 else 0)
private lemma projQ (a : Fin 3) : IsProjection (Q a) := by
  constructor
  · ext i j; simp [Q,Matrix.conjTranspose_apply,Matrix.diagonal_apply]; split_ifs <;> simp_all
  · rw [Q,Matrix.diagonal_mul_diagonal]
    congr 1; funext i; split_ifs <;> simp
private lemma rankQ (a : Fin 3) : (Q a).rank = 1 := by
  have hh := h62_trace_idem (Q a) (projQ a).2
  have ht : (Q a).trace = 1 := by simp [Q,Matrix.trace_diagonal]
  exact_mod_cast hh.symm.trans ht
private lemma diagonal_graph (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X ∈ graph example43) :
    ∃ w : Fin 3 → ℂ, X = Matrix.diagonal w := by
  obtain ⟨u,v,rfl⟩ := graph_form X hX
  refine ⟨fun i => u+v*(![1,0,-1] i),?_⟩
  ext i j
  by_cases hij : i = j
  · subst j; simp [D,Matrix.smul_apply,smul_eq_mul]
  · simp [D,Matrix.smul_apply,Matrix.diagonal_apply_ne _ hij,Matrix.one_apply_ne hij]

private lemma codeQ (a : Fin 3) : Code (graph example43) (Q a) := by
  refine ⟨projQ a,?_⟩
  intro X hX
  obtain ⟨w,rfl⟩ := diagonal_graph X hX
  refine ⟨w a,?_⟩
  simp only [Q,Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> simp_all
private lemma orthQ (a b : Fin 3) (hab : a ≠ b)
    (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : X ∈ graph example43) : Q a * X * Q b = 0 := by
  obtain ⟨w,rfl⟩ := diagonal_graph X hX
  simp only [Q,Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply,Matrix.zero_apply]
  split_ifs <;> simp_all
private lemma classical_transmits : Transmits example43 (classical 3) := by
  classical
  let e : Block (classical 3) ≃ Fin 3 := finCongr (by simp [classical,equalBlocks])
  apply (orthogonal_codes example43 channel (classical 3) (valid_classical 3 (by omega))).mpr
  refine ⟨fun k => Q (e k),fun k => ⟨codeQ _,?_⟩,?_⟩
  · have hm : blockSize (classical 3) k ∈ Multiset.replicate 3 1 :=
      Multiset.mem_toList.mp (List.get_mem _ k)
    exact (rankQ _).trans (Multiset.eq_of_mem_replicate hm).symm
  · intro k j hkj X hX
    exact orthQ _ _ (fun h => hkj (e.injective h)) X hX

private lemma D_graph : D ∈ graph example43 := by
  have h0 : (example43Kraus 0)ᴴ * example43Kraus 0 ∈ graph example43 :=
    Submodule.subset_span ⟨2,example43Kraus,normalized,fun _ => rfl,0,0,rfl⟩
  have h1 : (example43Kraus 1)ᴴ * example43Kraus 1 ∈ graph example43 :=
    Submodule.subset_span ⟨2,example43Kraus,normalized,fun _ => rfl,1,1,rfl⟩
  have he : (example43Kraus 0)ᴴ * example43Kraus 0 - (example43Kraus 1)ᴴ * example43Kraus 1 = D := by
    rw [effects,effects]
    norm_num
    ext i j
    simp
    ring
  rw [← he]
  exact Submodule.sub_mem _ h0 h1

private lemma simple_spectrum (t : ℝ) :
    Module.finrank ℂ (kernelSpace (D - (t : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))) ≤ 1 := by
  classical
  let X := D - (t : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
  have hn := LinearMap.finrank_range_add_finrank_ker (Matrix.toEuclideanLin X)
  have hrange : Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin X)) = X.rank := by
    rw [Matrix.rank_eq_finrank_range_toLin X
      (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis (EuclideanSpace.basisFun (Fin 3) ℂ).toBasis]
    rfl
  rw [hrange,finrank_euclideanSpace,Fintype.card_fin] at hn
  change Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin X)) ≤ 1
  suffices 2 ≤ X.rank by omega
  have he : X = Matrix.diagonal (fun i : Fin 3 => ![1,0,-1] i - (t : ℂ)) := by
    simp [X,D,Matrix.smul_one_eq_diagonal,Matrix.diagonal_sub]
  rw [he,Matrix.rank_diagonal,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_three]
  by_cases h1 : (t : ℂ) = 1 <;> by_cases h0 : (t : ℂ) = 0 <;> by_cases hm : (t : ℂ) = -1 <;>
    norm_num [h1,h0,hm,sub_eq_zero,eq_comm,Matrix.cons_val_two,Matrix.head_cons]
  have hn1 : (0:ℂ) ≠ 1-(t:ℂ) := Ne.symm (sub_ne_zero.mpr (Ne.symm h1))
  have hnm : (0:ℂ) ≠ -1-(t:ℂ) := Ne.symm (sub_ne_zero.mpr (Ne.symm hm))
  simp [hn1,hnm]

private lemma full_classical (A : Shape) (hA : Transmits example43 A) (hfull : lengthDim A = 3) :
    ∀ d ∈ A, d = 1 := by
  have hdherm : D.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [D,Matrix.conjTranspose_apply]
  obtain ⟨lam,hlam⟩ := (full_support_converse example43 channel A hA hfull).2 D D_graph hdherm
  intro d hd
  have hdlist := Multiset.mem_toList.mpr hd
  obtain ⟨k,hk⟩ := List.get_of_mem hdlist
  have hsize : blockSize A k = d := hk
  have hle : d ≤ ∑ j ∈ univ.filter (fun j => lam j = lam k), blockSize A j := by
    rw [← hsize]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (by simp)
  rw [← hlam] at hle
  have hu := simple_spectrum (lam k)
  have hp := hA.1.2 d hd
  omega

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

private lemma classified (A : Shape) (hA : Transmits example43 A) :
    A = classical 1 ∨ A = classical 2 ∨ A = classical 3 ∨ A = quantum 2 := by
  have hs : lengthDim A ≤ 3 := transmits_bound example43 A hA
  have hen := enum_list A.toList (fun a ha => hA.1.2 a (Multiset.mem_toList.mp ha))
    (by simpa [lengthDim] using hs)
  rcases hen with h | h | h | h | h | h | h | h
  · have hz : A = 0 := by rw [← Multiset.coe_toList A,h]; rfl
    exact (hA.1.1 hz).elim
  · left; rw [← Multiset.coe_toList A,h]; rfl
  · right; right; right; rw [← Multiset.coe_toList A,h]; rfl
  · have hh : lengthDim A = 3 := by rw [lengthDim,← Multiset.sum_toList,h]; rfl
    have h3 := full_classical A hA hh 3 (by rw [← Multiset.coe_toList A,h]; simp)
    omega
  · right; left; rw [← Multiset.coe_toList A,h]; rfl
  · have hh : lengthDim A = 3 := by rw [lengthDim,← Multiset.sum_toList,h]; rfl
    have h2 := full_classical A hA hh 2 (by rw [← Multiset.coe_toList A,h]; simp)
    omega
  · have hh : lengthDim A = 3 := by rw [lengthDim,← Multiset.sum_toList,h]; rfl
    have h2 := full_classical A hA hh 2 (by rw [← Multiset.coe_toList A,h]; simp)
    omega
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

private lemma quantum_maximal : Maximal example43 (quantum 2) := by
  refine ⟨quantum_transmits,?_⟩
  intro B hB he
  rcases classified B hB with rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals
    have hh := (comparisons _ _ (by simp) (by simp)).mp he 2 (by decide)
    norm_num [quantum,classical,equalBlocks] at hh

private lemma classical_maximal : Maximal example43 (classical 3) := by
  refine ⟨classical_transmits,?_⟩
  intro B hB he
  rcases classified B hB with rfl | rfl | rfl | rfl
  all_goals try rfl
  all_goals
    have hh := (comparisons _ _ (by simp) (by simp)).mp he 1 (by decide)
    norm_num [quantum,classical,equalBlocks] at hh

theorem solution : IsChannel example43 ∧
    maximals example43 = {quantum 2, classical 3} ∧ ¬ HasDominating example43 := by
  refine ⟨channel,?_,?_⟩
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
    have hq := hd _ quantum_transmits
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

#print axioms solution
