-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.ppt_satisfies_spectral_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:07:03.147973+00:00
-- url     : https://prove2.me/submissions/fb2d36db-652c-4ab8-a8d3-32c551881730

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators Matrix ComplexOrder

namespace PSE

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {M : Type*} [Fintype M] [DecidableEq M]

def F {α : Type*} [Fintype α] [DecidableEq α] (Y : Matrix M M ℂ) (σ : Equiv.Perm α) : ℂ :=
  ∑ κ : α → M, ∏ r, Y (κ r) (κ (σ r))

theorem F_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (Y : Matrix M M ℂ) (e : α ≃ β) (σ : Equiv.Perm α) : F Y (e.permCongr σ) = F Y σ := by
  unfold F
  rw [← (e.arrowCongr (Equiv.refl M)).sum_comp]
  refine Fintype.sum_congr _ _ fun κ => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]
  exact e.symm.prod_comp (fun r => Y (κ r) (κ (σ r)))

theorem F_conj {α : Type*} [Fintype α] [DecidableEq α] (Y : Matrix M M ℂ) (c σ : Equiv.Perm α) :
    F Y (c * σ * c⁻¹) = F Y σ := by
  have : c * σ * c⁻¹ = c.permCongr σ := by
    ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]
  rw [this, F_permCongr]

theorem F_sumCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (Y : Matrix M M ℂ) (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    F Y (Equiv.Perm.sumCongr σ τ) = F Y σ * F Y τ := by
  unfold F
  rw [← (Equiv.sumArrowEquivProdArrow α β M).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  refine Fintype.sum_congr _ _ fun u => Fintype.sum_congr _ _ fun v => ?_
  simp [Fintype.prod_sum_type]

theorem pow_path (Y : Matrix M M ℂ) : ∀ (m : ℕ) (a b : M), (Y ^ (m + 1)) a b =
    ∑ κ : Fin m → M, ∏ r : Fin (m + 1),
      Y ((Fin.cons a κ : Fin (m + 1) → M) r) ((Fin.snoc κ b : Fin (m + 1) → M) r)
  | 0, a, b => by
    simp [Fin.snoc]
  | m + 1, a, b => by
    rw [pow_succ', Matrix.mul_apply]
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => M).sum_comp, Fintype.sum_prod_type]
    refine Fintype.sum_congr _ _ fun c => ?_
    rw [pow_path Y m c b, Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun κ => ?_
    rw [Fin.prod_univ_succ (n := m + 1)]
    change Y a c * _ = Y a ((Fin.snoc (Fin.cons c κ : Fin (m+1) → M) b : Fin (m+2) → M) 0) *
      ∏ x : Fin (m+1), Y ((Fin.cons c κ : Fin (m+1) → M) x)
        ((Fin.snoc (Fin.cons c κ : Fin (m+1) → M) b : Fin (m+2) → M) x.succ)
    rw [← Fin.cons_snoc_eq_snoc_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]

theorem F_finRotate (Y : Matrix M M ℂ) (m : ℕ) : F Y (finRotate (m + 1)) = (Y ^ (m + 1)).trace := by
  unfold F
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, pow_path Y m]
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => M).sum_comp, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun κ => ?_
  refine Fintype.prod_congr _ _ fun r => ?_
  simp only [Fin.consEquiv_apply]
  congr 1
  induction r using Fin.lastCases with
  | last => simp [finRotate_last]
  | cast i =>
    rw [Fin.snoc_castSucc, finRotate_apply]
    have : (Fin.castSucc i + 1 : Fin (m + 1)) = i.succ := by
      ext; simp [Fin.val_add, Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)]
    rw [this, Fin.cons_succ]


def P : (L : List ℕ) → Equiv.Perm (Fin L.sum)
  | [] => 1
  | k :: L => (finSumFinEquiv).permCongr (Equiv.Perm.sumCongr (finRotate k) (P L))

theorem ct_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) : (e.permCongr σ).cycleType = σ.cycleType := by
  let f : α ≃ {b : β // True} := e.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm
  have : σ.extendDomain f = e.permCongr σ := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype _ _ trivial]
    simp [f, Equiv.permCongr_apply]
  rw [← this, Equiv.Perm.cycleType_extendDomain]

theorem ct_sumCongr_left {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm α) : (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).cycleType = σ.cycleType := by
  classical
  let f := Equiv.ofInjective (Sum.inl : α → α ⊕ β) Sum.inl_injective
  have : σ.extendDomain f = Equiv.Perm.sumCongr σ (1 : Equiv.Perm β) := by
    ext x
    rcases x with a | b
    · rw [Equiv.Perm.extendDomain_apply_subtype _ _ (Set.mem_range_self a)]
      have : f.symm ⟨Sum.inl a, Set.mem_range_self a⟩ = a :=
        Equiv.ofInjective_symm_apply Sum.inl_injective a
      simp [this, f]
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)]
      simp
  rw [← this, Equiv.Perm.cycleType_extendDomain]

theorem ct_sumCongr_right {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (τ : Equiv.Perm β) : (Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ).cycleType = τ.cycleType := by
  classical
  let f := Equiv.ofInjective (Sum.inr : β → α ⊕ β) Sum.inr_injective
  have : τ.extendDomain f = Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ := by
    ext x
    rcases x with a | b
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)]
      simp
    · rw [Equiv.Perm.extendDomain_apply_subtype _ _ (Set.mem_range_self b)]
      have : f.symm ⟨Sum.inr b, Set.mem_range_self b⟩ = b :=
        Equiv.ofInjective_symm_apply Sum.inr_injective b
      simp [this, f]
  rw [← this, Equiv.Perm.cycleType_extendDomain]

theorem ct_sumCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    (Equiv.Perm.sumCongr σ τ).cycleType = σ.cycleType + τ.cycleType := by
  have h : Equiv.Perm.sumCongr σ τ =
      Equiv.Perm.sumCongr σ (1 : Equiv.Perm β) * Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ := by
    rw [Equiv.Perm.sumCongr_mul]; simp
  have hd : (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).Disjoint
      (Equiv.Perm.sumCongr (1 : Equiv.Perm α) τ) := by
    intro x; rcases x with a | b <;> simp
  rw [h, hd.cycleType_mul, ct_sumCongr_left, ct_sumCongr_right]

theorem ct_finRotate (k : ℕ) :
    (finRotate k).cycleType = if 2 ≤ k then {k} else 0 := by
  split_ifs with h
  · exact cycleType_finRotate_of_le h
  · have : finRotate k = 1 := by
      ext i
      have : k = 1 := by have := i.pos; omega
      subst this
      simp [Subsingleton.elim ((finRotate 1) i) i]
    rw [this, Equiv.Perm.cycleType_one]

theorem ct_P : ∀ L : List ℕ, (P L).cycleType = ((L.filter (fun k => decide (2 ≤ k)) : List ℕ) : Multiset ℕ)
  | [] => by simp only [List.filter_nil, Multiset.coe_nil]; exact Equiv.Perm.cycleType_one
  | k :: L => by
    have e1 : (P (k :: L)).cycleType = ((finRotate k).sumCongr (P L)).cycleType :=
      ct_permCongr (finSumFinEquiv (m := k) (n := L.sum)) _
    rw [e1, ct_sumCongr, ct_finRotate, ct_P L, List.filter_cons]
    split_ifs with h1 h2 h2 <;> (simp_all <;> omega)


def blk (n s k : ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (s ≤ i.val ∧ i.val < s + k))

theorem blk_nodup (n s k : ℕ) : (blk n s k).Nodup := (List.nodup_finRange n).filter _

theorem mem_blk {n s k : ℕ} (i : Fin n) : i ∈ blk n s k ↔ s ≤ i.val ∧ i.val < s + k := by
  simp [blk]

theorem blk_length {n s k : ℕ} (h : s + k ≤ n) : (blk n s k).length = k := by
  rw [← List.toFinset_card_of_nodup (blk_nodup n s k)]
  have : (blk n s k).toFinset.map Fin.valEmbedding = Finset.Ico s (s + k) := by
    ext x
    simp only [Finset.mem_map, List.mem_toFinset, mem_blk, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, this, Nat.card_Ico]; omega

theorem ct_blk {n s k : ℕ} (h : s + k ≤ n) :
    (blk n s k).formPerm.cycleType = if 2 ≤ k then {k} else 0 := by
  have hl := blk_length h
  split_ifs with hk
  · rw [(List.isCycle_formPerm (blk_nodup n s k) (by omega)).cycleType,
      List.support_formPerm_of_nodup _ (blk_nodup n s k), List.toFinset_card_of_nodup
      (blk_nodup n s k), hl]
    intro x hx; rw [hx] at hl; simp at hl; omega
  · rw [(List.formPerm_eq_one_iff _ (blk_nodup n s k)).mpr (by omega), Equiv.Perm.cycleType_one]

theorem ct_prod {n : ℕ} : ∀ (Q : List (ℕ × ℕ)) (hQ : Q.Pairwise (fun p q => p.1 + p.2 ≤ q.1))
    (hb : ∀ q ∈ Q, q.1 + q.2 ≤ n),
    (Q.map fun q => (blk n q.1 q.2).formPerm).prod.cycleType =
      (((Q.map Prod.snd).filter (fun k => decide (2 ≤ k)) : List ℕ) : Multiset ℕ)
  | [], _, _ => by simp
  | q :: Q, hQ, hb => by
    rw [List.pairwise_cons] at hQ
    have hd : (blk n q.1 q.2).formPerm.Disjoint
        (Q.map fun q => (blk n q.1 q.2).formPerm).prod := by
      apply Equiv.Perm.disjoint_prod_right
      intro g hg
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hg
      have h1 := hQ.1 q' hq'
      intro x
      by_cases hx : x ∈ blk n q.1 q.2
      · right
        apply List.formPerm_apply_of_notMem
        rw [mem_blk] at hx ⊢; omega
      · left; exact List.formPerm_apply_of_notMem hx
    rw [List.map_cons, List.prod_cons, hd.cycleType_mul, ct_blk (hb q (by simp)),
      ct_prod Q hQ.2 (fun q hq => hb q (by simp [hq])), List.map_cons, List.filter_cons]
    split_ifs with h1 h2 h2 <;> (simp_all <;> omega)

theorem take_sum_mono (L : List ℕ) {i j : ℕ} (h : i ≤ j) : (L.take i).sum ≤ (L.take j).sum :=
  (List.take_sublist_take_left h).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem ct_canon (L : List ℕ) :
    (((L.zipIdx).map fun z =>
      ((List.finRange L.sum).filter fun i =>
        (L.take z.2).sum ≤ i.val ∧ i.val < (L.take z.2).sum + z.1).formPerm).prod).cycleType =
      ((L.filter (fun k => decide (2 ≤ k)) : List ℕ) : Multiset ℕ) := by
  have := ct_prod (n := L.sum) (L.zipIdx.map fun z => ((L.take z.2).sum, z.1)) ?_ ?_
  · rw [List.map_map, List.map_map,
      show (Prod.snd ∘ fun z : ℕ × ℕ => ((L.take z.2).sum, z.1)) = Prod.fst from rfl,
      List.zipIdx_map_fst] at this
    exact this
  · rw [List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_zipIdx, zero_add]
    have hi' : i < L.length := by simpa using hi
    rw [← List.sum_take_succ L i hi']
    exact take_sum_mono L hij
  · intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    simp only [List.getElem_zipIdx, zero_add]
    have hi' : i < L.length := by simpa using hi
    rw [← List.sum_take_succ L i hi']
    calc _ ≤ (L.take L.length).sum := take_sum_mono L (by omega)
      _ = L.sum := by rw [List.take_length]

end PSE

namespace PSE
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open QAlgorithms.Papers.Independent.Information100.P19

theorem F_one {M : Type*} [Fintype M] [DecidableEq M] (Y : Matrix M M ℂ) :
    F Y (1 : Equiv.Perm (Fin 0)) = 1 := by
  simp [F]

theorem F_P {M : Type*} [Fintype M] [DecidableEq M] (Y : Matrix M M ℂ) :
    ∀ L : List ℕ, (∀ k ∈ L, 0 < k) → F Y (P L) = (L.map fun k => (Y ^ k).trace).prod
  | [], _ => F_one Y
  | k :: L, hL => by
    have e1 : F Y (P (k :: L)) = F Y ((finRotate k).sumCongr (P L)) :=
      F_permCongr Y (finSumFinEquiv (m := k) (n := L.sum)) _
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := hL k (by simp); omega⟩
    rw [e1, F_sumCongr, F_finRotate, F_P Y L (fun k hk => hL k (by simp [hk])), List.map_cons,
      List.prod_cons]

theorem F_canon {M : Type*} [Fintype M] [DecidableEq M] (Y : Matrix M M ℂ) {n : ℕ} (l : Part n) :
    F Y (canonicalPerm l) = (l.val.map fun k => (Y ^ k).trace).prod := by
  obtain ⟨L, h1, h2, h3⟩ := l
  subst h3
  have hc : (canonicalPerm (⟨L, h1, h2, rfl⟩ : Part L.sum)).cycleType = _ := ct_canon L
  have hconj : IsConj (P L) (canonicalPerm (⟨L, h1, h2, rfl⟩ : Part L.sum)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr ((ct_P L).trans hc.symm)
  obtain ⟨c, hc'⟩ := isConj_iff.mp hconj
  rw [← hc', F_conj, F_P Y L h2]

theorem tt_diag {n a b : ℕ} (Y : Bip a b) (σ : Equiv.Perm (Fin n)) :
    tensorTrace (σ, σ) Y = F Y σ := by
  unfold tensorTrace F
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin a) (fun _ => Fin b)).symm.sum_comp,
    Fintype.sum_prod_type]
  rfl

theorem tt_ppt {n a b : ℕ} (X : Bip a b) (σ : Equiv.Perm (Fin n)) :
    tensorTrace (σ, σ⁻¹) X = tensorTrace (σ, σ) (transposeB X) := by
  unfold tensorTrace transposeB
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [← (Equiv.arrowCongr σ.symm (Equiv.refl (Fin b))).sum_comp]
  refine Fintype.sum_congr _ _ fun j => ?_
  refine Fintype.prod_congr _ _ fun r => ?_
  simp [Equiv.arrowCongr_apply]

theorem trace_pow_herm {I : Type*} [Fintype I] [DecidableEq I] {Y : Matrix I I ℂ}
    (hY : Y.IsHermitian) (k : ℕ) :
    (Y ^ k).trace = ((∑ i, hY.eigenvalues i ^ k : ℝ) : ℂ) := by
  have hs := hY.spectral_theorem
  have : Y ^ k = Unitary.conjStarAlgAut ℂ _ hY.eigenvectorUnitary
      ((Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues)) ^ k) := by
    rw [map_pow, ← hs]
  rw [this, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  push_cast
  rfl

theorem eval_embed {n a b : ℕ} (ppt : Bool) (f : Coeff n) (X : Bip a b) :
    tensorEval (embed ppt f) X = f.sum (fun l c => c *
      (tensorTrace (canonicalPerm l, if ppt then (canonicalPerm l)⁻¹ else canonicalPerm l) X).re) := by
  unfold tensorEval embed Finsupp.sum
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [ite_mul]

theorem nonneg_of {n a b : ℕ} (ha : 0 < a) (hb : 0 < b) (f : Coeff n) (hf : f ∈ psdCone n)
    (Y : Bip a b) (hY : Y.PosSemidef) :
    0 ≤ f.sum (fun l c => c * (F Y (canonicalPerm l)).re) := by
  set d := Fintype.card (Fin a × Fin b)
  have hd : 0 < d := Fintype.card_pos_iff.mpr ⟨(⟨0, ha⟩, ⟨0, hb⟩)⟩
  let x : Fin d → ℝ := fun i => hY.1.eigenvalues ((Fintype.equivFin _).symm i)
  have hx : ∀ i, 0 ≤ x i := fun i => hY.eigenvalues_nonneg _
  have h := hf d hd x hx
  unfold pairing at h
  convert h using 2
  funext l c
  congr 1
  rw [F_canon, spectralMoments]
  have hsum : ∀ k, (∑ i, x i ^ k) = ∑ p, hY.1.eigenvalues p ^ k := fun k =>
    (Fintype.equivFin _).symm.sum_comp (fun p => hY.1.eigenvalues p ^ k)
  have hl : ∀ L : List ℕ, (L.map fun k => (Y ^ k).trace).prod =
      (((L.map fun k => ∑ i, x i ^ k).prod : ℝ) : ℂ) := by
    intro L
    induction L with
    | nil => simp
    | cons k L ih =>
      rw [List.map_cons, List.prod_cons, ih, trace_pow_herm hY.1, ← hsum, List.map_cons,
        List.prod_cons, Complex.ofReal_mul]
  rw [hl, Complex.ofReal_re]

end PSE

open QAlgorithms.Papers.Independent.Information100.P19 in
theorem solution (n : ℕ) (hn : 1≤n) (f : Coeff n) (hf : f∈psdCone n)
    (a b : ℕ) (ha : 0<a) (hb : 0<b) (X : Bip a b)
    (hX : X.PosSemidef) (hPPT : (transposeB X).PosSemidef) :
    0≤tensorEval (embed false f) X ∧ 0≤tensorEval (embed true f) X := by
  constructor
  · rw [PSE.eval_embed]
    simp only [Bool.false_eq_true, if_false, PSE.tt_diag]
    exact PSE.nonneg_of ha hb f hf X hX
  · rw [PSE.eval_embed]
    simp only [if_true, PSE.tt_ppt, PSE.tt_diag]
    exact PSE.nonneg_of ha hb f hf (transposeB X) hPPT

