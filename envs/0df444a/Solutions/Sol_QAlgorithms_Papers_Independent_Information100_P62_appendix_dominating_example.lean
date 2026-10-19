-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.appendix_dominating_example
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:48:30.015988+00:00
-- url     : https://prove2.me/submissions/a952459c-4da8-4d74-81f9-27ef9036873c

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_kraus_geometric_converse

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_equal_block_packing
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_small_block_embedding

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

private def E : Fin 2 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![unit 0 0 + unit 1 1, unit 1 2 + unit 3 3]

private def DP (S : Finset (Fin 4)) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun a => if a ∈ S then 1 else 0)
private lemma diag_proj (S : Finset (Fin 4)) : IsProjection (DP S) := by
  constructor
  · ext a b; simp [DP,Matrix.conjTranspose_apply,Matrix.diagonal_apply]; split_ifs <;> simp_all
  · rw [DP,Matrix.diagonal_mul_diagonal]
    congr 1; funext a; split_ifs <;> simp
private lemma diag_rank (S : Finset (Fin 4)) : (DP S).rank = S.card := by
  have h := h62_trace_idem (DP S) (diag_proj S).2
  have ht : (DP S).trace = (S.card : ℂ) := by simp [DP,Matrix.trace_diagonal]
  exact_mod_cast h.symm.trans ht
private lemma diag_sandwich (S T : Finset (Fin 4)) (X : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    (DP S * X * DP T) a b = if a ∈ S ∧ b ∈ T then X a b else 0 := by
  simp only [DP,Matrix.diagonal_mul,Matrix.mul_diagonal]
  split_ifs <;> simp_all

private lemma effects (i j : Fin 2) : (E i)ᴴ * E j =
    ![![unit 0 0 + unit 1 1, unit 1 2],
      ![unit 2 1,unit 2 2 + unit 3 3]] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [E,unit,Matrix.conjTranspose_add,Matrix.add_mul,Matrix.mul_add,
      Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne]

private lemma normalized : IsKrausFamily E := by
  change (∑ i, (E i)ᴴ * E i) = 1
  simp only [Fin.sum_univ_two,effects,Matrix.cons_val_zero,Matrix.cons_val_one]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [unit,Matrix.single_apply,Matrix.one_apply,Fin.ext_iff]
private lemma channel : IsChannel appendixExample := ⟨2,E,normalized,fun _ => rfl⟩

private lemma code_of_effects (S : Finset (Fin 4))
    (h : ∀ i j, ∃ c : ℂ, DP S * ((E i)ᴴ * E j) * DP S = c • DP S) :
    Code (graph appendixExample) (DP S) := by
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
private lemma orth_of_effects (S T : Finset (Fin 4))
    (h : ∀ i j, DP S * ((E i)ᴴ * E j) * DP T = 0)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X ∈ graph appendixExample) :
    DP S * X * DP T = 0 := by
  have hh := kraus_graph_le E (show X ∈ graph (krausApply E) from hX)
  clear hX
  induction hh using Submodule.span_induction with
  | mem X hX => obtain ⟨⟨i,j⟩,rfl⟩ := hX; exact h i j
  | zero => simp
  | add X Y hX hY iX iY => simp [Matrix.mul_add,Matrix.add_mul,iX,iY]
  | smul c X hX iX => simp [iX]

private lemma sandwich_scalar (S : Finset (Fin 4)) (X : Matrix (Fin 4) (Fin 4) ℂ) (c : ℂ)
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
private lemma sandwich_zero (S T : Finset (Fin 4)) (X : Matrix (Fin 4) (Fin 4) ℂ)
    (h : ∀ a ∈ S, ∀ b ∈ T, X a b = 0) : DP S * X * DP T = 0 := by
  ext a b
  rw [diag_sandwich]
  split_ifs with hh
  · exact h a hh.1 b hh.2
  · rfl

private lemma code_left (S : Finset (Fin 4)) (hS : ∀ a ∈ S, a.val < 2) :
    Code (graph appendixExample) (DP S) := by
  apply code_of_effects
  intro i j
  refine ⟨if i = 0 ∧ j = 0 then 1 else 0,?_⟩
  apply sandwich_scalar
  intro a ha b hb
  have ha' := hS a ha; have hb' := hS b hb
  fin_cases a <;> fin_cases b <;> simp_all only [Nat.reduceLT]
  all_goals fin_cases i <;> fin_cases j <;> simp [effects,unit,Fin.ext_iff]

private lemma code_single (v : Fin 4) : Code (graph appendixExample) (DP {v}) := by
  apply code_of_effects
  intro i j
  refine ⟨((E i)ᴴ * E j) v v,?_⟩
  apply sandwich_scalar
  intro a ha b hb
  simp only [mem_singleton] at ha hb
  subst a; subst b; simp

private lemma orth_disjoint (S T : Finset (Fin 4)) (h : ∀ a ∈ S, ∀ b ∈ T,
    a ≠ b ∧ ¬ (a = 1 ∧ b = 2) ∧ ¬ (a = 2 ∧ b = 1))
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X ∈ graph appendixExample) : DP S * X * DP T = 0 := by
  apply orth_of_effects _ _ ?_ X hX
  intro i j
  apply sandwich_zero
  intro a ha b hb
  obtain ⟨hne,h12,h21⟩ := h a ha b hb
  have hz (u : Fin 4) : ¬ (u = a ∧ u = b) := by rintro ⟨rfl,rfl⟩; exact hne rfl
  have h12' : ¬ (1 = a ∧ 2 = b) := by rintro ⟨rfl,rfl⟩; exact h12 ⟨rfl,rfl⟩
  have h21' : ¬ (2 = a ∧ 1 = b) := by rintro ⟨rfl,rfl⟩; exact h21 ⟨rfl,rfl⟩
  fin_cases i <;> fin_cases j <;>
    simp [effects,unit,hz,h12',h21']

private lemma valid_sum (d e : ℕ) (hd : 0 < d) (he : 0 < e) : Valid (quantum d + quantum e) := by
  constructor
  · intro hz; have h := congrArg Multiset.card hz; simp [quantum] at h
  · intro a ha; simp only [quantum,Multiset.mem_add,Multiset.mem_singleton] at ha
    rcases ha with rfl|rfl <;> assumption

private lemma block_mem (A : Shape) (k : Block A) : blockSize A k ∈ A :=
  Multiset.mem_toList.mp (List.get_mem _ k)
private lemma size_inj (A : Shape) (h : A.Nodup) : Function.Injective (blockSize A) :=
  (show A.toList.Nodup by rwa [← Multiset.coe_nodup,Multiset.coe_toList]).injective_get

private lemma sum_transmits (d e : ℕ) (hd : 0 < d) (he : 0 < e) (hne : d ≠ e)
    (S T : Finset (Fin 4)) (hS : Code (graph appendixExample) (DP S))
    (hT : Code (graph appendixExample) (DP T)) (hdS : S.card = d) (heT : T.card = e)
    (hst : ∀ a ∈ S, ∀ b ∈ T, a ≠ b ∧ ¬ (a = 1 ∧ b = 2) ∧ ¬ (a = 2 ∧ b = 1)) :
    Transmits appendixExample (quantum d + quantum e) := by
  let A := quantum d + quantum e
  have hs (k : Block A) : blockSize A k = d ∨ blockSize A k = e := by
    simpa [A,quantum] using block_mem A k
  have hinj : Function.Injective (blockSize A) := size_inj A (by simp [A,quantum,hne])
  apply (orthogonal_codes appendixExample channel A (valid_sum d e hd he)).mpr
  refine ⟨fun k => if blockSize A k = d then DP S else DP T,?_,?_⟩
  · intro k
    rcases hs k with hk|hk
    · simp only [hk,ite_true]
      exact ⟨hS,(diag_rank S).trans hdS⟩
    · have hkd : blockSize A k ≠ d := by rw [hk]; exact Ne.symm hne
      simp only [if_neg hkd]
      exact ⟨hT,(diag_rank T).trans (heT.trans hk.symm)⟩
  · intro k l hkl X hX
    have hn : blockSize A k ≠ blockSize A l := fun h => hkl (hinj h)
    rcases hs k with hk|hk <;> rcases hs l with hl|hl
    · exact False.elim (hn (hk.trans hl.symm))
    · simp only [hk,hl,ite_true,if_neg (Ne.symm hne)]
      exact orth_disjoint S T hst X hX
    · simp only [hk,hl,ite_true,if_neg (Ne.symm hne)]
      apply orth_disjoint T S ?_ X hX
      intro a ha b hb
      obtain ⟨hn,h12,h21⟩ := hst b hb a ha
      exact ⟨Ne.symm hn,fun ⟨ha,hb⟩ => h21 ⟨hb,ha⟩,fun ⟨ha,hb⟩ => h12 ⟨hb,ha⟩⟩
    · exact False.elim (hn (hk.trans hl.symm))

private lemma transmits21 : Transmits appendixExample (quantum 2 + quantum 1) := by
  apply sum_transmits 2 1 (by omega) (by omega) (by omega) {0,1} {3}
    (code_left _ (by intro a ha; simp only [mem_insert,mem_singleton] at ha; rcases ha with rfl|rfl <;> decide))
    (code_single 3) (by norm_num [Fin.ext_iff]) (by simp)
  intro a ha b hb
  simp only [mem_insert,mem_singleton] at ha hb
  subst b
  rcases ha with rfl|rfl <;> norm_num [Fin.ext_iff]

private lemma rank_image {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M : Matrix O I ℂ) :
    M.rank = Module.finrank ℂ (imageSpace M) := by
  rw [Matrix.rank_eq_finrank_range_toLin M
    (EuclideanSpace.basisFun O ℂ).toBasis (EuclideanSpace.basisFun I ℂ).toBasis]
  rfl
private lemma DP_units (S : Finset (Fin 4)) : DP S = ∑ i ∈ S, unit i i := by
  unfold DP
  rw [← Matrix.sum_single_eq_diagonal]
  have h (i : Fin 4) : Matrix.single i i (if i ∈ S then (1:ℂ) else 0) =
      if i ∈ S then unit i i else 0 := by
    split_ifs <;> simp [unit]
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp
private lemma ranks (i : Fin 2) : (E i).rank = if i = 0 then 2 else 2 := by
  have he : (E i)ᴴ * E i = DP (if i = 0 then {0,1} else {2,3}) := by
    fin_cases i <;> simp [effects,DP_units,Fin.ext_iff]
  rw [← Matrix.rank_conjTranspose_mul_self,he,diag_rank]
  fin_cases i <;> norm_num [Fin.ext_iff]

private lemma output : krausApply E 1 = Matrix.diagonal (![1,2,0,1] : Fin 4 → ℂ) := by
  simp [krausApply,Fin.sum_univ_two,E,unit,Matrix.conjTranspose_add,
    Matrix.add_mul,Matrix.mul_add,Matrix.single_mul_single_of_ne]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.single_apply,Matrix.diagonal_apply,Fin.ext_iff]
private lemma output_rank : (krausApply E 1).rank = 3 := by
  rw [output,Matrix.rank_diagonal,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  norm_num [Fin.sum_univ_succ,Matrix.cons_val,Matrix.cons_val_zero]
private lemma length_bound (A : Shape) (hA : Transmits appendixExample A) : lengthDim A ≤ 3 := by
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
    _ ≤ Module.finrank ℂ (⨆ i : Fin 2, imageSpace (E i) : Submodule ℂ (EuclideanSpace ℂ (Fin 4))) :=
      Submodule.finrank_mono (show (⨆ i : {i : Fin 2 // 1 ≤ (E i).rank}, imageSpace (E i.val) : Submodule ℂ (EuclideanSpace ℂ (Fin 4))) ≤ ⨆ i : Fin 2, imageSpace (E i) from
        iSup_le fun i => le_iSup (fun j : Fin 2 => imageSpace (E j)) i.val)
    _ = 3 := by rw [hh.2.2.2,← rank_image,output_rank]

private lemma block_bound (A : Shape) (hA : Transmits appendixExample A) :
    ∀ d ∈ A, d ≤ 2 := by
  intro d hd
  have hlist := Multiset.mem_toList.mpr hd
  obtain ⟨k,hk⟩ := List.get_of_mem hlist
  have hb := (kraus_geometric_converse E normalized A hA).2.1 k
  change A.toList.get k ≤ _ at hb
  rw [hk] at hb
  exact hb.trans (Finset.sup_le (fun i _ => by rw [ranks]; split_ifs <;> omega))

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

private lemma classified (A : Shape) (hA : Transmits appendixExample A) :
    A = classical 1 ∨ A = classical 2 ∨ A = classical 3 ∨ A = quantum 2 ∨
    A = quantum 2 + quantum 1 := by
  have hs := length_bound A hA
  have hen := enum_list A.toList (fun a ha => hA.1.2 a (Multiset.mem_toList.mp ha))
    (by simpa [lengthDim] using hs)
  rcases hen with h | h | h | h | h | h | h | h
  · have hz : A = 0 := by rw [← Multiset.coe_toList A,h]; rfl
    exact (hA.1.1 hz).elim
  · left; rw [← Multiset.coe_toList A,h]; rfl
  · right; right; right; left; rw [← Multiset.coe_toList A,h]; rfl
  · have h3 := block_bound A hA 3 (by rw [← Multiset.coe_toList A,h]; simp)
    omega
  · right; left; rw [← Multiset.coe_toList A,h]; rfl
  · right; right; right; right
    rw [← Multiset.coe_toList A,h]
    simp [quantum,add_comm]
    rfl
  · right; right; right; right
    rw [← Multiset.coe_toList A,h]; rfl
  · right; right; left; rw [← Multiset.coe_toList A,h]; rfl

private lemma known_valid (A : Shape)
    (h : A = classical 1 ∨ A = classical 2 ∨ A = classical 3 ∨ A = quantum 2 ∨
      A = quantum 2 + quantum 1) : Valid A ∧ ∀ d ∈ A, d ≤ 3 := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals try { simp [classical,equalBlocks,quantum] }
  all_goals try { exact valid_sum 2 1 (by omega) (by omega) }
  all_goals constructor
  all_goals simp [classical,equalBlocks,quantum]

private lemma comparisons (A B : Shape)
    (hA : A = classical 1 ∨ A = classical 2 ∨ A = classical 3 ∨ A = quantum 2 ∨ A = quantum 2 + quantum 1)
    (hB : B = classical 1 ∨ B = classical 2 ∨ B = classical 3 ∨ B = quantum 2 ∨ B = quantum 2 + quantum 1) :
    Embeds A B ↔ ∀ d ∈ Icc 1 3,
      (A.map (fun n => n/d)).sum ≤ (B.map (fun n => n/d)).sum := by
  obtain ⟨ha,ha3⟩ := known_valid A hA
  obtain ⟨hb,hb3⟩ := known_valid B hB
  rw [small_block_embedding B A hb ha hb3 ha3]
  apply forall₂_congr
  intro d hd
  rw [(equal_block_packing A ha d (by have := (mem_Icc.mp hd).1; omega)).1,
    (equal_block_packing B hb d (by have := (mem_Icc.mp hd).1; omega)).1]

private lemma dominates : Dominating appendixExample (quantum 2 + quantum 1) := by
  refine ⟨transmits21,?_⟩
  intro A hA
  have hc := classified A hA
  rw [comparisons _ _ hc (by simp)]
  have hr : (Icc 1 3 : Finset ℕ) = {1,2,3} := by decide
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [hr,classical,equalBlocks,quantum]

theorem solution :
    IsChannel appendixExample ∧ Dominating appendixExample (quantum 2 + quantum 1) :=
  ⟨channel,dominates⟩
