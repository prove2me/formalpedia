-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.capacity_algebra_need_not_dominate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:41:24.911623+00:00
-- url     : https://prove2.me/submissions/7ec9c1f8-e514-47a1-8b34-9335087352b8

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_orthogonal_codes
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_kraus_geometric_converse

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_embedding_packing
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_capacity_necessity_and_maximality

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

private def E : Fin 2 → Matrix (Fin 6) (Fin 6) ℂ :=
  ![unit 0 0 + unit 1 1 + unit 2 2 + unit 3 3, unit 3 4 + unit 4 5]

private def DP (S : Finset (Fin 6)) : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal (fun a => if a ∈ S then 1 else 0)
private lemma diag_proj (S : Finset (Fin 6)) : IsProjection (DP S) := by
  constructor
  · ext a b; simp [DP,Matrix.conjTranspose_apply,Matrix.diagonal_apply]; split_ifs <;> simp_all
  · rw [DP,Matrix.diagonal_mul_diagonal]
    congr 1; funext a; split_ifs <;> simp
private lemma diag_rank (S : Finset (Fin 6)) : (DP S).rank = S.card := by
  have h := h62_trace_idem (DP S) (diag_proj S).2
  have ht : (DP S).trace = (S.card : ℂ) := by simp [DP,Matrix.trace_diagonal]
  exact_mod_cast h.symm.trans ht
private lemma diag_sandwich (S T : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℂ) (a b : Fin 6) :
    (DP S * X * DP T) a b = if a ∈ S ∧ b ∈ T then X a b else 0 := by
  simp only [DP,Matrix.diagonal_mul,Matrix.mul_diagonal]
  split_ifs <;> simp_all

private lemma effects (i j : Fin 2) : (E i)ᴴ * E j =
    ![![unit 0 0 + unit 1 1 + unit 2 2 + unit 3 3, unit 3 4],
      ![unit 4 3,unit 4 4 + unit 5 5]] i j := by
  fin_cases i <;> fin_cases j <;>
    simp [E,unit,Matrix.conjTranspose_add,Matrix.add_mul,Matrix.mul_add,
      Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne]

private lemma normalized : IsKrausFamily E := by
  change (∑ i, (E i)ᴴ * E i) = 1
  simp only [Fin.sum_univ_two,effects,Matrix.cons_val_zero,Matrix.cons_val_one]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [unit,Matrix.single_apply,Matrix.one_apply,Fin.ext_iff]
private lemma channel : IsChannel capacityExample := ⟨2,E,normalized,fun _ => rfl⟩

private lemma code_of_effects (S : Finset (Fin 6))
    (h : ∀ i j, ∃ c : ℂ, DP S * ((E i)ᴴ * E j) * DP S = c • DP S) :
    Code (graph capacityExample) (DP S) := by
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
private lemma orth_of_effects (S T : Finset (Fin 6))
    (h : ∀ i j, DP S * ((E i)ᴴ * E j) * DP T = 0)
    (X : Matrix (Fin 6) (Fin 6) ℂ) (hX : X ∈ graph capacityExample) :
    DP S * X * DP T = 0 := by
  have hh := kraus_graph_le E (show X ∈ graph (krausApply E) from hX)
  clear hX
  induction hh using Submodule.span_induction with
  | mem X hX => obtain ⟨⟨i,j⟩,rfl⟩ := hX; exact h i j
  | zero => simp
  | add X Y hX hY iX iY => simp [Matrix.mul_add,Matrix.add_mul,iX,iY]
  | smul c X hX iX => simp [iX]

private lemma sandwich_scalar (S : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℂ) (c : ℂ)
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
private lemma sandwich_zero (S T : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℂ)
    (h : ∀ a ∈ S, ∀ b ∈ T, X a b = 0) : DP S * X * DP T = 0 := by
  ext a b
  rw [diag_sandwich]
  split_ifs with hh
  · exact h a hh.1 b hh.2
  · rfl

private lemma code_left (S : Finset (Fin 6)) (hS : ∀ a ∈ S, a.val < 4) :
    Code (graph capacityExample) (DP S) := by
  apply code_of_effects
  intro i j
  refine ⟨if i = 0 ∧ j = 0 then 1 else 0,?_⟩
  apply sandwich_scalar
  intro a ha b hb
  have ha' := hS a ha; have hb' := hS b hb
  fin_cases a <;> fin_cases b <;> simp_all only [Nat.reduceLT]
  all_goals fin_cases i <;> fin_cases j <;> simp [effects,unit,Fin.ext_iff]

private lemma code_right : Code (graph capacityExample) (DP {4,5}) := by
  apply code_of_effects
  intro i j
  refine ⟨if i = 1 ∧ j = 1 then 1 else 0,?_⟩
  apply sandwich_scalar
  intro a ha b hb
  simp only [mem_insert,mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;>
    fin_cases i <;> fin_cases j <;> simp [effects,unit,Fin.ext_iff]

private lemma code_single (v : Fin 6) : Code (graph capacityExample) (DP {v}) := by
  apply code_of_effects
  intro i j
  refine ⟨((E i)ᴴ * E j) v v,?_⟩
  apply sandwich_scalar
  intro a ha b hb
  simp only [mem_singleton] at ha hb
  subst a; subst b; simp

private lemma orth_disjoint (S T : Finset (Fin 6)) (h : ∀ a ∈ S, ∀ b ∈ T,
    a ≠ b ∧ ¬ (a = 3 ∧ b = 4) ∧ ¬ (a = 4 ∧ b = 3))
    (X : Matrix (Fin 6) (Fin 6) ℂ) (hX : X ∈ graph capacityExample) : DP S * X * DP T = 0 := by
  apply orth_of_effects _ _ ?_ X hX
  intro i j
  apply sandwich_zero
  intro a ha b hb
  obtain ⟨hne,h34,h43⟩ := h a ha b hb
  have hz (u : Fin 6) : ¬ (u = a ∧ u = b) := by rintro ⟨rfl,rfl⟩; exact hne rfl
  have h34' : ¬ (3 = a ∧ 4 = b) := by rintro ⟨rfl,rfl⟩; exact h34 ⟨rfl,rfl⟩
  have h43' : ¬ (4 = a ∧ 3 = b) := by rintro ⟨rfl,rfl⟩; exact h43 ⟨rfl,rfl⟩
  fin_cases i <;> fin_cases j <;>
    simp [effects,unit,hz,h34',h43']

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
    (S T : Finset (Fin 6)) (hS : Code (graph capacityExample) (DP S))
    (hT : Code (graph capacityExample) (DP T)) (hdS : S.card = d) (heT : T.card = e)
    (hst : ∀ a ∈ S, ∀ b ∈ T, a ≠ b ∧ ¬ (a = 3 ∧ b = 4) ∧ ¬ (a = 4 ∧ b = 3)) :
    Transmits capacityExample (quantum d + quantum e) := by
  let A := quantum d + quantum e
  have hs (k : Block A) : blockSize A k = d ∨ blockSize A k = e := by
    simpa [A,quantum] using block_mem A k
  have hinj : Function.Injective (blockSize A) := size_inj A (by simp [A,quantum,hne])
  apply (orthogonal_codes capacityExample channel A (valid_sum d e hd he)).mpr
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
      obtain ⟨hn,h34,h43⟩ := hst b hb a ha
      exact ⟨Ne.symm hn,fun ⟨ha,hb⟩ => h43 ⟨hb,ha⟩,fun ⟨ha,hb⟩ => h34 ⟨hb,ha⟩⟩
    · exact False.elim (hn (hk.trans hl.symm))

private lemma transmits41 : Transmits capacityExample (quantum 4 + quantum 1) := by
  apply sum_transmits 4 1 (by omega) (by omega) (by omega) {0,1,2,3} {5}
    (code_left _ (by intro a ha; simp only [mem_insert,mem_singleton] at ha; rcases ha with rfl|rfl|rfl|rfl <;> decide))
    (code_single 5) (by norm_num [Fin.ext_iff]) (by simp)
  intro a ha b hb
  simp only [mem_insert,mem_singleton] at ha hb
  subst b
  rcases ha with rfl|rfl|rfl|rfl <;> norm_num [Fin.ext_iff]

private lemma transmits32 : Transmits capacityExample (quantum 3 + quantum 2) := by
  apply sum_transmits 3 2 (by omega) (by omega) (by omega) {0,1,2} {4,5}
    (code_left _ (by intro a ha; simp only [mem_insert,mem_singleton] at ha; rcases ha with rfl|rfl|rfl <;> decide))
    code_right (by norm_num [Fin.ext_iff]) (by norm_num [Fin.ext_iff])
  intro a ha b hb
  simp only [mem_insert,mem_singleton] at ha hb
  rcases ha with rfl|rfl|rfl <;> rcases hb with rfl|rfl <;> norm_num [Fin.ext_iff]

private lemma valid_equal (d c : ℕ) (hd : 0 < d) (hc : 0 < c) : Valid (equalBlocks d c) := by
  constructor
  · intro hz; have h := congrArg Multiset.card hz; simp [equalBlocks] at h; omega
  · intro a ha; have h : a = d := Multiset.eq_of_mem_replicate ha; omega
private lemma quantum_transmits (S : Finset (Fin 6)) (hd : 0 < S.card)
    (hS : Code (graph capacityExample) (DP S)) : Transmits capacityExample (quantum S.card) := by
  apply (orthogonal_codes capacityExample channel _ (by simpa [Valid,quantum] using hd)).mpr
  refine ⟨fun _ => DP S,fun k => ⟨hS,?_⟩,?_⟩
  · rw [diag_rank]
    exact (Multiset.mem_singleton.mp (block_mem (quantum S.card) k)).symm
  · intro k j hkj
    exfalso
    apply hkj
    apply Fin.ext
    have hk := k.isLt; have hj := j.isLt
    simp [quantum] at hk hj
    omega
private lemma quantum4 : Transmits capacityExample (quantum 4) := by
  have h := quantum_transmits {0,1,2,3} (by norm_num [Fin.ext_iff])
    (code_left _ (by intro a ha; simp only [mem_insert,mem_singleton] at ha; rcases ha with rfl|rfl|rfl|rfl <;> decide))
  norm_num [Fin.ext_iff] at h
  exact h
private lemma quantum3 : Transmits capacityExample (quantum 3) := by
  have h := quantum_transmits {0,1,2} (by norm_num [Fin.ext_iff])
    (code_left _ (by intro a ha; simp only [mem_insert,mem_singleton] at ha; rcases ha with rfl|rfl|rfl <;> decide))
  norm_num [Fin.ext_iff] at h
  exact h
private def S2 (k : Fin 2) : Finset (Fin 6) := if k = 0 then {0,1} else {2,3}
private lemma code2 (k : Fin 2) : Code (graph capacityExample) (DP (S2 k)) := by
  apply code_left
  intro a ha
  fin_cases k <;> fin_cases a <;> simp_all [S2,Fin.ext_iff]
private lemma orth2 (k l : Fin 2) (hkl : k ≠ l)
    (X : Matrix (Fin 6) (Fin 6) ℂ) (hX : X ∈ graph capacityExample) :
    DP (S2 k) * X * DP (S2 l) = 0 := by
  apply orth_disjoint _ _ ?_ X hX
  intro a ha b hb
  fin_cases k <;> fin_cases l <;> norm_num at hkl
  all_goals fin_cases a <;> fin_cases b <;> simp_all [S2,Fin.ext_iff]
private def S1 (k : Fin 5) : Finset (Fin 6) := {![0,1,2,3,5] k}
private lemma orth1 (k l : Fin 5) (hkl : k ≠ l)
    (X : Matrix (Fin 6) (Fin 6) ℂ) (hX : X ∈ graph capacityExample) :
    DP (S1 k) * X * DP (S1 l) = 0 := by
  apply orth_disjoint _ _ ?_ X hX
  intro a ha b hb
  simp only [S1,mem_singleton] at ha hb
  subst a; subst b
  fin_cases k <;> fin_cases l <;> norm_num at hkl
  all_goals norm_num [Fin.ext_iff]
private lemma two_transmits : Transmits capacityExample (equalBlocks 2 2) := by
  classical
  let e : Block (equalBlocks 2 2) ≃ Fin 2 := finCongr (by simp [equalBlocks])
  apply (orthogonal_codes capacityExample channel _ (valid_equal 2 2 (by omega) (by omega))).mpr
  refine ⟨fun k => DP (S2 (e k)),fun k => ⟨code2 _,?_⟩,?_⟩
  · rw [diag_rank]
    have h : blockSize (equalBlocks 2 2) k = 2 :=
      Multiset.eq_of_mem_replicate (Multiset.mem_toList.mp (List.get_mem _ k))
    rw [h]; simp only [S2]; split_ifs <;> norm_num [Fin.ext_iff]
  · intro k j hkj X hX
    exact orth2 _ _ (fun h => hkj (e.injective h)) X hX
private lemma five_transmits : Transmits capacityExample (equalBlocks 1 5) := by
  classical
  let e : Block (equalBlocks 1 5) ≃ Fin 5 := finCongr (by simp [equalBlocks])
  apply (orthogonal_codes capacityExample channel _ (valid_equal 1 5 (by omega) (by omega))).mpr
  refine ⟨fun k => DP (S1 (e k)),fun k => ⟨code_single _,?_⟩,?_⟩
  · rw [diag_rank]
    have h : blockSize (equalBlocks 1 5) k = 1 :=
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
private lemma DP_units (S : Finset (Fin 6)) : DP S = ∑ i ∈ S, unit i i := by
  unfold DP
  rw [← Matrix.sum_single_eq_diagonal]
  have h (i : Fin 6) : Matrix.single i i (if i ∈ S then (1:ℂ) else 0) =
      if i ∈ S then unit i i else 0 := by
    split_ifs <;> simp [unit]
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp
private lemma ranks (i : Fin 2) : (E i).rank = if i = 0 then 4 else 2 := by
  have he : (E i)ᴴ * E i = DP (if i = 0 then {0,1,2,3} else {4,5}) := by
    fin_cases i <;> simp [effects,DP_units,Fin.ext_iff,add_assoc]
  rw [← Matrix.rank_conjTranspose_mul_self,he,diag_rank]
  fin_cases i <;> norm_num [Fin.ext_iff]

private lemma output : krausApply E 1 = Matrix.diagonal (![1,1,1,2,1,0] : Fin 6 → ℂ) := by
  simp [krausApply,Fin.sum_univ_two,E,unit,Matrix.conjTranspose_add,
    Matrix.add_mul,Matrix.mul_add,Matrix.single_mul_single_of_ne]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.single_apply,Matrix.diagonal_apply,Fin.ext_iff]
private lemma output_rank : (krausApply E 1).rank = 5 := by
  rw [output,Matrix.rank_diagonal,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  norm_num [Fin.sum_univ_succ,Matrix.cons_val,Matrix.cons_val_zero]
private lemma length_bound (A : Shape) (hA : Transmits capacityExample A) : lengthDim A ≤ 5 := by
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
    _ ≤ Module.finrank ℂ (⨆ i : Fin 2, imageSpace (E i) : Submodule ℂ (EuclideanSpace ℂ (Fin 6))) :=
      Submodule.finrank_mono (show (⨆ i : {i : Fin 2 // 1 ≤ (E i).rank}, imageSpace (E i.val) : Submodule ℂ (EuclideanSpace ℂ (Fin 6))) ≤ ⨆ i : Fin 2, imageSpace (E i) from
        iSup_le fun i => le_iSup (fun j : Fin 2 => imageSpace (E j)) i.val)
    _ = 5 := by rw [hh.2.2.2,← rank_image,output_rank]

private lemma quantum_bound (d : ℕ) (hd : Transmits capacityExample (quantum d)) : d ≤ 4 := by
  have hh := (kraus_geometric_converse E normalized _ hd).2.1
  let k : Block (quantum d) := ⟨0,by simp [quantum]⟩
  have hk : blockSize (quantum d) k = d :=
    Multiset.mem_singleton.mp (Multiset.mem_toList.mp (List.get_mem _ k))
  have h := hh k
  rw [hk] at h
  exact h.trans (Finset.sup_le (fun i _ => by rw [ranks]; split_ifs <;> omega))

private lemma dmax_value : dmax capacityExample = 4 := by
  unfold dmax
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    exact quantum_bound d.val (Finset.mem_filter.mp hd).2
  · exact Finset.le_sup (f := Fin.val) (show (⟨4,by simp⟩ : Fin (Fintype.card (Fin 6) + 1)) ∈
      univ.filter (fun d => Transmits capacityExample (quantum d.val)) from
        mem_filter.mpr ⟨mem_univ _,quantum4⟩)
private lemma hybrid_bound (d : ℕ) (hd : 0 < d) : hybrid capacityExample d ≤ 5 / d := by
  unfold hybrid
  rw [if_neg (by omega)]
  apply Finset.sup_le
  intro c hc
  apply (Nat.le_div_iff_mul_le hd).mpr
  have h := length_bound _ (Finset.mem_filter.mp hc).2
  simpa [lengthDim,equalBlocks,Multiset.sum_replicate,nsmul_eq_mul] using h

private lemma hybrid_lower (d c : ℕ) (hd : d ≠ 0) (hc : c ≤ 6)
    (h : Transmits capacityExample (equalBlocks d c)) : c ≤ hybrid capacityExample d := by
  unfold hybrid
  rw [if_neg hd]
  exact Finset.le_sup (f := Fin.val) (show (⟨c,by simp; omega⟩ : Fin (Fintype.card (Fin 6) + 1)) ∈
    univ.filter (fun n => Transmits capacityExample (equalBlocks d n.val)) from
      mem_filter.mpr ⟨mem_univ _,h⟩)
private lemma hybrid1 : hybrid capacityExample 1 = 5 := by
  apply le_antisymm
  · simpa using hybrid_bound 1 (by omega)
  · exact hybrid_lower 1 5 (by omega) (by omega) five_transmits
private lemma hybrid2 : hybrid capacityExample 2 = 2 := by
  apply le_antisymm
  · simpa using hybrid_bound 2 (by omega)
  · exact hybrid_lower 2 2 (by omega) (by omega) two_transmits
private lemma hybrid3 : hybrid capacityExample 3 = 1 := by
  apply le_antisymm
  · simpa using hybrid_bound 3 (by omega)
  · apply hybrid_lower 3 1 (by omega) (by omega)
    simpa [equalBlocks,quantum] using quantum3

private lemma hybrid4 : hybrid capacityExample 4 = 1 := by
  apply le_antisymm
  · simpa using hybrid_bound 4 (by omega)
  · apply hybrid_lower 4 1 (by omega) (by omega)
    simpa [equalBlocks,quantum] using quantum4

private lemma mult1 : QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample 1 = 1 := by
  norm_num [QAlgorithms.Papers.Independent.Information100.P62.multiplicity,dmax_value,reconstruction,hybrid1,hybrid2,hybrid3,hybrid4,
    Finset.sum_Icc_succ_top]
private lemma mult2 : QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample 2 = 0 := by
  norm_num [QAlgorithms.Papers.Independent.Information100.P62.multiplicity,dmax_value,reconstruction,hybrid1,hybrid2,hybrid3,hybrid4,
    Finset.sum_Icc_succ_top]
private lemma mult3 : QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample 3 = 0 := by
  norm_num [QAlgorithms.Papers.Independent.Information100.P62.multiplicity,dmax_value,reconstruction,hybrid1,hybrid2,hybrid3,hybrid4,
    Finset.sum_Icc_succ_top]
private lemma mult4 : QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample 4 = 1 := by
  norm_num [QAlgorithms.Papers.Independent.Information100.P62.multiplicity,dmax_value,reconstruction,hybrid1,hybrid2,hybrid3,hybrid4,
    Finset.sum_Icc_succ_top]

private lemma capacity_value : capacityAlgebra capacityExample = some (quantum 4 + quantum 1) := by
  have hn : ∀ d ∈ Icc 1 (dmax capacityExample), 0 ≤ QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample d := by
    intro d hd
    rw [dmax_value] at hd
    obtain ⟨hd1,hd4⟩ := mem_Icc.mp hd
    interval_cases d <;> norm_num [mult1,mult2,mult3,mult4]
  rw [capacityAlgebra,if_pos hn,dmax_value]
  norm_num [List.range_succ,mult1,mult2,mult3,mult4,quantum,add_comm]
  rfl

private lemma nonembedding : ¬ Embeds (quantum 3 + quantum 2) (quantum 4 + quantum 1) := by
  intro h
  obtain ⟨f,hf⟩ := (embedding_packing _ _ (valid_sum 3 2 (by omega) (by omega))
    (valid_sum 4 1 (by omega) (by omega))).1.mp h
  let A := quantum 3 + quantum 2
  let B := quantum 4 + quantum 1
  have hA (k : Block A) : blockSize A k = 3 ∨ blockSize A k = 2 := by
    simpa [A,quantum] using block_mem A k
  have hB (j : Block B) : blockSize B j = 4 ∨ blockSize B j = 1 := by
    simpa [B,quantum] using block_mem B j
  have hle (k : Block A) : blockSize A k ≤ blockSize B (f k) := by
    have hmem : k ∈ univ.filter (fun l => f l = f k) := mem_filter.mpr ⟨mem_univ _,rfl⟩
    exact (Finset.single_le_sum (f := fun l : Block A => blockSize A l)
      (fun _ _ => Nat.zero_le _) hmem).trans (hf (f k))
  have h4 (k : Block A) : blockSize B (f k) = 4 := by
    have hk := hA k
    have hj := hB (f k)
    have hh := hle k
    omega
  have hinj : Function.Injective (blockSize B) := size_inj B (by simp [B,quantum])
  have hne : Nonempty (Block A) := by
    apply Fin.pos_iff_nonempty.mp
    simp [A,quantum]
  obtain ⟨k⟩ := hne
  have hall (l : Block A) : f l = f k := hinj ((h4 l).trans (h4 k).symm)
  have hh := hf (f k)
  have hfilter : univ.filter (fun l => f l = f k) = univ := by ext l; simp [hall]
  rw [hfilter] at hh
  have hsum : ∑ l : Block A, blockSize A l = 5 := by
    unfold blockSize
    rw [← List.sum_ofFn,List.ofFn_get,Multiset.sum_toList]
    norm_num [A,quantum]
  rw [hsum,h4] at hh
  omega

private lemma no_dominating : ¬ HasDominating capacityExample := by
  rintro ⟨A,hA⟩
  have h := (capacity_necessity_and_maximality capacityExample channel).1 A hA
  have heq : A = quantum 4 + quantum 1 := Option.some.inj (h.2.symm.trans capacity_value)
  have he := hA.2 _ transmits32
  rw [heq] at he
  exact nonembedding he

theorem solution :
    IsChannel capacityExample ∧
    Transmits capacityExample (quantum 4 + quantum 1) ∧
    Transmits capacityExample (quantum 3 + quantum 2) ∧ dmax capacityExample = 4 ∧
    hybrid capacityExample 1 = 5 ∧ hybrid capacityExample 2 = 2 ∧
    hybrid capacityExample 3 = 1 ∧ hybrid capacityExample 4 = 1 ∧
    QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample 1 = 1 ∧
    QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample 2 = 0 ∧
    QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample 3 = 0 ∧
    QAlgorithms.Papers.Independent.Information100.P62.multiplicity capacityExample 4 = 1 ∧
    capacityAlgebra capacityExample = some (quantum 4 + quantum 1) ∧
    ¬ Embeds (quantum 3 + quantum 2) (quantum 4 + quantum 1) ∧ ¬ HasDominating capacityExample := by
  exact ⟨channel,transmits41,transmits32,dmax_value,hybrid1,hybrid2,hybrid3,hybrid4,
    mult1,mult2,mult3,mult4,capacity_value,nonembedding,no_dominating⟩
