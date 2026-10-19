-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.explicit_forbidden_lists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:20:43.735985+00:00
-- url     : https://prove2.me/submissions/4a82bd51-08dd-4968-bbb9-b8cfd1ee5008

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P62
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.36, 37, Lemma 4.10: finite minimal obstruction set. -/
/- Embedding preliminaries adapted from the accepted proof of Lemma 4.10. -/
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

private theorem h62_E_MP (A B : Shape) (hA : ∀ d ∈ A, 0 < d) (h : Embeds A B) : MultiplicityPacking A B := by
  obtain ⟨f, hfi, hfm, -⟩ := h
  let z : ∀ k : Block A, Fin (blockSize A k) := fun k => ⟨0, h62_pos A hA k⟩
  let e : ∀ k : Block A, Fin (blockSize A k) → Fin (blockSize A k) → Algebra A :=
    fun k α β => Pi.single k (Matrix.single α β 1)
  have emul : ∀ k α β γ, e k α β * e k β γ = e k α γ := by
    intro k α β γ
    simp only [e, ← Pi.single_mul, Matrix.single_mul_single_same, mul_one]
  have tr : ∀ k α j, ((f (e k α α)) j).trace = ((f (e k (z k) (z k))) j).trace := by
    intro k α j
    rw [← emul k α (z k) α, ← emul k (z k) α (z k), hfm, hfm, Pi.mul_apply, Pi.mul_apply,
      Matrix.trace_mul_comm]
  have idem : ∀ X : Algebra A, X * X = X → ∀ j, (f X j) * (f X j) = f X j := by
    intro X hX j
    rw [← Pi.mul_apply, ← hfm, hX]
  refine ⟨fun k j => ((f (e k (z k) (z k))) j).rank, ?_, ?_⟩
  · intro j
    have h1 : ((∑ k, ((f (e k (z k) (z k))) j).rank * blockSize A k : ℕ) : ℂ) =
        (((f 1) j).rank : ℂ) := by
      rw [← h62_trace_idem _ (idem 1 (mul_one 1) j), h62_one A, map_sum, Finset.sum_apply,
        Matrix.trace_sum]
      push_cast
      apply Finset.sum_congr rfl
      intro k _
      rw [map_sum, Finset.sum_apply, Matrix.trace_sum]
      have : ∀ α, ((f (e k α α)) j).trace = (((f (e k (z k) (z k))) j).rank : ℂ) := by
        intro α
        rw [tr, h62_trace_idem _ (idem _ (emul _ _ _ _) j)]
      simp only [e] at this
      simp [this, mul_comm]
      exact Or.inl rfl
    have h2 := Nat.cast_injective h1
    rw [h2]
    simpa using Matrix.rank_le_card_width ((f 1) j)
  · intro k
    have hne : f (e k (z k) (z k)) ≠ 0 := by
      intro h0
      have : e k (z k) (z k) = 0 := hfi (by rw [h0, map_zero])
      have := congrFun this k
      simp only [e, Pi.single_eq_same, Pi.zero_apply] at this
      have := congrFun (congrFun this (z k)) (z k)
      simp at this
    obtain ⟨j, hj⟩ : ∃ j, (f (e k (z k) (z k))) j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (funext hc)
    calc 1 ≤ ((f (e k (z k) (z k))) j).rank := h62_rank_pos _ (idem _ (emul _ _ _ _) j) hj
      _ ≤ _ := Finset.single_le_sum (f := fun j => ((f (e k (z k) (z k))) j).rank)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

private theorem h62_P_E (A B : Shape) (h : Packs A B) : Embeds A B := by
  obtain ⟨p, hp⟩ := h
  let T : Block B → Type := fun j => Σ k : {k : Block A // p k = j}, Fin (blockSize A k.1)
  have hcard : ∀ j, Fintype.card (T j) ≤ blockSize B j := by
    intro j
    refine le_trans (le_of_eq ?_) (hp j)
    simp only [T, Fintype.card_sigma, Fintype.card_fin]
    exact (Finset.sum_subtype _ (by simp) _).symm
  have eqv : ∀ j, Fin (blockSize B j) ≃ T j ⊕ Fin (blockSize B j - Fintype.card (T j)) := fun j =>
    Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; have := hcard j; omega)
  let G : Algebra A → Algebra B := fun X j =>
    (Matrix.fromBlocks (Matrix.blockDiagonal' (fun k : {k : Block A // p k = j} => X k.1))
      (0 : Matrix (T j) (Fin (blockSize B j - Fintype.card (T j))) ℂ) 0 0).submatrix (eqv j) (eqv j)
  let Gl : Algebra A →ₗ[ℂ] Algebra B :=
    { toFun := G
      map_add' := by
        intro X Y; funext j
        simp only [G, Pi.add_apply]
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.add_apply]
        rcases (eqv j a) with x | x <;> rcases (eqv j b) with y | y <;>
          simp [Matrix.blockDiagonal'_apply] <;> split_ifs <;> simp
      map_smul' := by
        intro c X; funext j
        simp only [G, Pi.smul_apply, RingHom.id_apply]
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.smul_apply]
        rcases (eqv j a) with x | x <;> rcases (eqv j b) with y | y <;>
          simp [Matrix.blockDiagonal'_apply] <;> split_ifs <;> simp }
  refine ⟨Gl, ?_, ?_, ?_⟩
  · intro X Y hXY
    funext k
    ext α β
    have := congrFun (congrFun (congrFun hXY (p k)) ((eqv (p k)).symm (Sum.inl ⟨⟨k, rfl⟩, α⟩)))
      ((eqv (p k)).symm (Sum.inl ⟨⟨k, rfl⟩, β⟩))
    simpa [Gl, G, Matrix.blockDiagonal'_apply_eq] using this
  · intro X Y; funext j
    simp only [Gl, G, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, ← Matrix.blockDiagonal'_mul]
    simp
  · intro X; funext j
    simp only [Gl, G, LinearMap.coe_mk, AddHom.coe_mk, Pi.star_apply, Matrix.star_eq_conjTranspose]
    rw [Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
      Matrix.blockDiagonal'_conjTranspose]
    simp

private theorem h62_MP_P (A B : Shape) (h : MultiplicityPacking A B) : Packs A B := by
  obtain ⟨L, h1, h2⟩ := h
  have : ∀ k, ∃ j, 1 ≤ L k j := by
    intro k
    by_contra hc
    push Not at hc
    have := h2 k
    rw [Finset.sum_eq_zero (fun j _ => by have := hc j; omega)] at this
    omega
  choose f hf using this
  refine ⟨f, fun j => le_trans ?_ (h1 j)⟩
  calc ∑ k ∈ univ.filter (fun k => f k = j), blockSize A k
      ≤ ∑ k ∈ univ.filter (fun k => f k = j), L k j * blockSize A k := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [Finset.mem_filter] at hk
        have := hf k; rw [hk.2] at this
        exact Nat.le_mul_of_pos_left _ this
    _ ≤ ∑ k, L k j * blockSize A k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

private theorem h62_embeds_iff_packs (A B : Shape) (hA : Valid A) : Embeds A B ↔ Packs A B :=
  ⟨fun h => h62_MP_P A B (h62_E_MP A B hA.2 h), h62_P_E A B⟩

private theorem h62_sum_blocks (A : Shape) : ∑ k : Block A, blockSize A k = lengthDim A := by
  unfold blockSize lengthDim
  rw [← List.sum_ofFn, List.ofFn_get, Multiset.sum_toList]

private theorem h62_quantum_blockSize (D : ℕ) (j : Block (quantum D)) : blockSize (quantum D) j = D := by
  have : (quantum D).toList = [D] := by simp [quantum]
  unfold blockSize
  have hj : j.val = 0 := by
    have h2 := j.2
    have : (quantum D).toList.length = 1 := by rw [this]; rfl
    omega
  simp only [List.get_eq_getElem]
  simp [this, hj]

private theorem h62_packs_quantum (A : Shape) (D : ℕ) : Packs A (quantum D) ↔ lengthDim A ≤ D := by
  have hlen : (quantum D).toList.length = 1 := by simp [quantum]
  constructor
  · rintro ⟨f, hf⟩
    have j0 : Block (quantum D) := ⟨0, by omega⟩
    have := hf j0
    rw [h62_quantum_blockSize] at this
    rw [← h62_sum_blocks]
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext k
    simp only [Finset.mem_univ, Finset.mem_filter, true_and, true_iff]
    apply Fin.ext; omega
  · intro h
    refine ⟨fun _ => ⟨0, by omega⟩, fun j => ?_⟩
    rw [h62_quantum_blockSize]
    refine le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) ?_
    rw [h62_sum_blocks]; exact h

private theorem h62_sum_blocks_map (A : Shape) (g : ℕ → ℕ) :
    ∑ k : Block A, g (blockSize A k) = (A.map g).sum := by
  have : A.map g = ((A.toList.map g : List ℕ) : Multiset ℕ) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  rw [this, Multiset.sum_coe, ← List.sum_ofFn]
  unfold blockSize
  congr 1
  apply List.ext_get <;> simp

private theorem h62_eq_blockSize (d c : ℕ) (k : Block (equalBlocks d c)) : blockSize (equalBlocks d c) k = d :=
  Multiset.eq_of_mem_replicate (Multiset.mem_toList.mp (List.get_mem _ _))

private theorem h62_packs_equal (d c : ℕ) (hd : 0 < d) (B : Shape) :
    Packs (equalBlocks d c) B ↔ c ≤ (B.map (fun n => n / d)).sum := by
  rw [← h62_sum_blocks_map]
  have hlen : (equalBlocks d c).toList.length = c := by simp [equalBlocks]
  constructor
  · rintro ⟨f, hf⟩
    have hc : c = ∑ j : Block B, (univ.filter (fun k => f k = j)).card := by
      rw [← Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (f k))]
      simp [hlen]
    rw [hc]
    apply Finset.sum_le_sum
    intro j _
    have := hf j
    simp only [h62_eq_blockSize, Finset.sum_const, smul_eq_mul] at this
    exact (Nat.le_div_iff_mul_le hd).2 this
  · intro hc
    let m : Block B → ℕ := fun j => blockSize B j / d
    have hcard : Fintype.card (Block (equalBlocks d c)) ≤ Fintype.card (Σ j : Block B, Fin (m j)) := by
      simp [hlen, m, hc]
    obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
    refine ⟨fun k => (emb k).1, fun j => ?_⟩
    simp only [h62_eq_blockSize, Finset.sum_const, smul_eq_mul]
    have : (univ.filter (fun k => (emb k).1 = j)).card ≤ m j := by
      have := Finset.card_le_card_of_injOn (s := univ.filter (fun k => (emb k).1 = j))
        (t := (univ : Finset (Fin (m j))).map ⟨Sigma.mk j, sigma_mk_injective⟩)
        (fun k => emb k) ?_ (fun a _ b _ h => emb.injective h)
      · simpa using this
      · intro k hk
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hk
        simp only [Finset.coe_map, Finset.coe_univ, Set.image_univ, Function.Embedding.coeFn_mk,
          Set.mem_range]
        generalize emb k = x at *
        obtain ⟨j', i⟩ := x
        simp only at hk
        subst hk
        exact ⟨i, rfl⟩
    calc (univ.filter (fun k => (emb k).1 = j)).card * d ≤ m j * d := Nat.mul_le_mul_right _ this
      _ ≤ blockSize B j := Nat.div_mul_le_self _ _

private theorem h62_embeds_equal_iff (d c : ℕ) (hd : 0 < d) (B : Shape) :
    Embeds (equalBlocks d c) B ↔ c ≤ (B.map (fun n => n / d)).sum := by
  rw [← h62_packs_equal d c hd B]
  refine ⟨fun h => h62_MP_P _ _ (h62_E_MP _ _ ?_ h), h62_P_E _ _⟩
  intro x hx
  rw [Multiset.eq_of_mem_replicate hx]; exact hd

private theorem h62_shape_eq (A : Shape) : (univ : Finset (Block A)).val.map (blockSize A) = A := by
  conv_rhs => rw [← Multiset.coe_toList A]
  rw [Fin.univ_val_map]
  congr 1
  unfold blockSize
  exact List.ofFn_get _

private theorem h62_packs_trans (A B C : Shape) (h1 : Packs A B) (h2 : Packs B C) : Packs A C := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨g, hg⟩ := h2
  refine ⟨g ∘ f, fun l => le_trans ?_ (hg l)⟩
  calc ∑ k ∈ univ.filter (fun k => (g ∘ f) k = l), blockSize A k
      = ∑ j ∈ univ.filter (fun j => g j = l), ∑ k ∈ univ.filter (fun k => f k = j), blockSize A k := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun k => (g ∘ f) k = l))
          (t := univ.filter (fun j => g j = l)) (g := f)]
        · apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          congr 1
          ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
          constructor
          · exact fun h => h.2
          · intro h; exact ⟨by rw [h, hj], h⟩
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
          exact hk
    _ ≤ _ := Finset.sum_le_sum (fun j _ => hf j)

private theorem h62_packs_lengthDim (A B : Shape) (h : Packs A B) : lengthDim A ≤ lengthDim B := by
  obtain ⟨f, hf⟩ := h
  rw [← h62_sum_blocks, ← h62_sum_blocks, ← Finset.sum_fiberwise_of_maps_to (g := f) (t := univ)
    (fun _ _ => Finset.mem_univ _)]
  exact Finset.sum_le_sum (fun j _ => hf j)

private theorem h62_sq_le {ι : Type} (s : Finset ι) (c : ι → ℕ) :
    ∑ k ∈ s, c k * c k ≤ ∑ k ∈ s, c k * (∑ i ∈ s, c i) :=
  Finset.sum_le_sum (fun _k hk => Nat.mul_le_mul_left _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk))

private theorem h62_packs_eq (C B : Shape) (hC : ∀ d ∈ C, 0 < d) (hB : ∀ d ∈ B, 0 < d) (h : Packs C B)
    (hsq : ∑ j : Block B, blockSize B j * blockSize B j ≤ ∑ k : Block C, blockSize C k * blockSize C k) :
    C = B := by
  obtain ⟨f, hf⟩ := h
  set c := blockSize C with hc
  set b := blockSize B with hb
  have hj : ∀ j, ∑ k ∈ univ.filter (fun k => f k = j), c k * c k ≤ b j * b j := by
    intro j
    refine le_trans (h62_sq_le _ c) ?_
    rw [← Finset.sum_mul]
    exact Nat.mul_le_mul (hf j) (hf j)
  have htot : ∑ j, ∑ k ∈ univ.filter (fun k => f k = j), c k * c k = ∑ j, b j * b j := by
    apply le_antisymm (Finset.sum_le_sum (fun j _ => hj j))
    rw [Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)]
    exact hsq
  have heq := (Finset.sum_eq_sum_iff_of_le (fun j _ => hj j)).1 htot
  have key : ∀ j, ∃ k, univ.filter (fun k => f k = j) = {k} ∧ c k = b j := by
    intro j
    obtain ⟨S, hS⟩ : ∃ S, S = univ.filter (fun k => f k = j) := ⟨_, rfl⟩
    obtain ⟨T, hTd⟩ : ∃ T, T = ∑ i ∈ S, c i := ⟨_, rfl⟩
    have hT : T ≤ b j := by rw [hTd, hS]; exact hf j
    have e1 : ∑ k ∈ S, c k * c k = b j * b j := by rw [hS]; exact heq j (Finset.mem_univ _)
    have e2 : ∑ k ∈ S, c k * c k ≤ ∑ k ∈ S, c k * T := by rw [hTd]; exact h62_sq_le S c
    have e2' : ∑ k ∈ S, c k * T = T * T := by rw [← Finset.sum_mul, ← hTd]
    have hTb : T = b j := by
      by_contra hne
      have : T * T < b j * b j := Nat.mul_self_lt_mul_self (lt_of_le_of_ne hT hne)
      exact absurd (e1 ▸ (e2.trans e2'.le)) (not_le.mpr this)
    have hbpos : 0 < b j := hB _ (Multiset.mem_toList.mp (List.get_mem _ _))
    have hle : ∀ k ∈ S, c k * c k ≤ c k * T := fun k hk => Nat.mul_le_mul_left _
      (by rw [hTd]; exact Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) hk)
    have e3 : ∑ k ∈ S, c k * c k = ∑ k ∈ S, c k * T := by
      apply le_antisymm e2; rw [e2', e1, hTb]
    have hall : ∀ k ∈ S, c k = T := by
      intro k hk
      have := (Finset.sum_eq_sum_iff_of_le hle).1 e3 k hk
      have hcpos : 0 < c k := hC _ (Multiset.mem_toList.mp (List.get_mem _ _))
      exact Nat.eq_of_mul_eq_mul_left hcpos this
    have hcard : S.card * T = T := by
      rw [← Finset.sum_const_nat hall, ← hTd]
    have h1 : S.card = 1 := by
      have : 0 < T := by omega
      exact Nat.eq_of_mul_eq_mul_right this (by rw [one_mul]; exact hcard)
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 h1
    refine ⟨k, hS ▸ hk, ?_⟩
    rw [hall k (by rw [hk]; exact Finset.mem_singleton_self k), hTb]
  choose g hg using key
  have hbij : Function.Bijective f := by
    constructor
    · intro k k' hkk
      have h1 : k ∈ univ.filter (fun x => f x = f k) := by simp
      have h2 : k' ∈ univ.filter (fun x => f x = f k) := by simp [hkk]
      rw [(hg (f k)).1] at h1 h2
      simp at h1 h2; rw [h1, h2]
    · intro j
      have : g j ∈ univ.filter (fun x => f x = j) := by rw [(hg j).1]; simp
      exact ⟨g j, by simpa using this⟩
  have hcb : ∀ k, c k = b (f k) := by
    intro k
    have : k ∈ univ.filter (fun x => f x = f k) := by simp
    rw [(hg (f k)).1, Finset.mem_singleton] at this
    have h2 := (hg (f k)).2
    rw [← this] at h2
    exact h2
  rw [← h62_shape_eq C, ← h62_shape_eq B]
  have : (fun k => blockSize C k) = (fun k => blockSize B (f k)) := funext hcb
  rw [show (univ : Finset (Block C)).val.map (blockSize C) =
      ((univ : Finset (Block C)).val.map f).map (blockSize B) by
    rw [Multiset.map_map]; exact congrArg (fun φ => (univ : Finset (Block C)).val.map φ) this]
  rw [show (univ : Finset (Block C)).val.map f = (univ : Finset (Block B)).val from
    Multiset.map_univ_val_equiv (Equiv.ofBijective f hbij)]

private theorem h62_packs_sq (C B : Shape) (h : Packs C B) :
    ∑ k : Block C, blockSize C k * blockSize C k ≤ ∑ j : Block B, blockSize B j * blockSize B j := by
  obtain ⟨f, hf⟩ := h
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_le_sum
  intro j _
  refine le_trans (h62_sq_le _ _) ?_
  rw [← Finset.sum_mul]
  exact Nat.mul_le_mul (hf j) (hf j)

private theorem h62_packs_refl (A : Shape) : Packs A A :=
  ⟨id, fun j => by simp [Finset.filter_eq']⟩

private theorem h62_embeds_trans (A B C : Shape) (hA : Valid A) (hB : Valid B) (h1 : Embeds A B)
    (h2 : Embeds B C) : Embeds A C :=
  h62_P_E _ _ (h62_packs_trans A B C ((h62_embeds_iff_packs A B hA).1 h1)
    ((h62_embeds_iff_packs B C hB).1 h2))

private theorem h62_classical_valid (m : ℕ) (hm : 1 ≤ m) : Valid (classical m) := by
  refine ⟨?_, fun d hd => ?_⟩
  · unfold classical equalBlocks
    intro h
    have := congrArg Multiset.card h
    simp at this; omega
  · unfold classical equalBlocks at hd
    rw [Multiset.eq_of_mem_replicate hd]; exact Nat.one_pos

private theorem h62_classical_len (m : ℕ) : lengthDim (classical m) = m := by
  simp [lengthDim, classical, equalBlocks]

private theorem h62_classical_embeds (m : ℕ) (B : Shape) : Embeds (classical m) B ↔ m ≤ lengthDim B := by
  unfold classical
  rw [h62_embeds_equal_iff 1 m Nat.one_pos B]
  simp [lengthDim]

private theorem fo_bound (A B : Shape) (hB : B ∈ forbidden A) :
    lengthDim B ≤ lengthDim A + 1 := by
  by_contra hc
  have hcl := h62_classical_valid (lengthDim A + 1) (by omega)
  have hnA : ¬ Embeds (classical (lengthDim A + 1)) A := by
    rw [h62_classical_embeds]
    omega
  have hne : classical (lengthDim A + 1) ≠ B := by
    intro he
    have hh := congrArg lengthDim he
    rw [h62_classical_len] at hh
    omega
  exact hnA (hB.2.2 _ hcl ((h62_classical_embeds _ _).mpr (by omega)) hne)

attribute [-instance] Classical.propDecidable

private def finitePacks {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (a : α → ℕ) (b : β → ℕ) : Prop :=
  ∃ f : α → β, ∀ j, ∑ k ∈ univ.filter (fun k => f k = j), a k ≤ b j

private theorem weight_equiv {α β : Type} [Fintype α] [Fintype β]
    (a : α → ℕ) (b : β → ℕ)
    (h : (univ : Finset α).val.map a = (univ : Finset β).val.map b) :
    ∃ e : α ≃ β, ∀ i, b (e i) = a i := by
  classical
  have hc : ∀ t, Fintype.card {i // a i = t} = Fintype.card {j // b j = t} := by
    intro t
    have hh := congrArg (Multiset.count t) h
    simpa [Multiset.count_map, Fintype.card_subtype, ← Finset.filter_val, eq_comm] using hh
  exact ⟨Equiv.ofFiberEquiv (fun t => Fintype.equivOfCardEq (hc t)),
    Equiv.ofFiberEquiv_map _⟩

private theorem finitePacks_congr {α β γ δ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq β] [DecidableEq δ]
    (a : α → ℕ) (b : β → ℕ) (c : γ → ℕ) (d : δ → ℕ)
    (e : α ≃ γ) (g : β ≃ δ) (he : ∀ i, c (e i) = a i) (hg : ∀ j, d (g j) = b j) :
    finitePacks a b → finitePacks c d := by
  classical
  rintro ⟨f,hf⟩
  refine ⟨fun k => g (f (e.symm k)), fun j => ?_⟩
  have hs : (∑ k ∈ univ.filter (fun k => g (f (e.symm k)) = j), c k) =
      ∑ i ∈ univ.filter (fun i => f i = g.symm j), a i := by
    apply Finset.sum_equiv e.symm
    · intro k
      simp only [mem_filter, mem_univ, true_and]
      exact g.eq_symm_apply.symm
    · intro k _
      simpa using he (e.symm k)
  rw [hs]
  simpa only [g.apply_symm_apply] using (hf (g.symm j)).trans (hg (g.symm j)).symm.le

private def listPacks (a b : List ℕ) : Prop := finitePacks a.get b.get

private instance (a b : List ℕ) : Decidable (listPacks a b) :=
  inferInstanceAs (Decidable (∃ f : Fin a.length → Fin b.length,
    ∀ j, ∑ k ∈ univ.filter (fun k => f k = j), a.get k ≤ b.get j))

private theorem packs_lists (A B : Shape) (a b : List ℕ)
    (ha : (a : Shape) = A) (hb : (b : Shape) = B) :
    Packs A B ↔ listPacks a b := by
  classical
  have hre (l : List ℕ) : (univ : Finset (Fin l.length)).val.map l.get = (l : Shape) := by
    rw [Fin.univ_val_map, List.ofFn_get]
  obtain ⟨e,he⟩ := weight_equiv (blockSize A) a.get ((h62_shape_eq A).trans (ha.symm.trans (hre a).symm))
  obtain ⟨g,hg⟩ := weight_equiv (blockSize B) b.get ((h62_shape_eq B).trans (hb.symm.trans (hre b).symm))
  constructor
  · exact finitePacks_congr _ _ _ _ e g he hg
  · exact finitePacks_congr _ _ _ _ e.symm g.symm
      (fun i => by simpa using (he (e.symm i)).symm)
      (fun j => by simpa using (hg (g.symm j)).symm)

private def enumShapes : ℕ → Finset Shape
  | 0 => {0}
  | n+1 => enumShapes n ∪
    ((enumShapes n).biUnion (fun A => (Icc 1 (n+1)).image (fun d => d ::ₘ A))).filter
      (fun A => A.sum ≤ n+1)

private theorem mem_enum (n : ℕ) (A : Shape) (hp : ∀ d ∈ A, 0 < d) (hs : A.sum ≤ n) :
    A ∈ enumShapes n := by
  induction n generalizing A with
  | zero =>
    have : A = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro d hd
      have := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) d hd
      have := hp d hd
      omega
    simp [this, enumShapes]
  | succ n ih =>
    by_cases h0 : A = 0
    · subst A
      exact Finset.mem_union_left _ (ih 0 (by simp) (by simp))
    obtain ⟨d, hdmem⟩ := Multiset.exists_mem_of_ne_zero h0
    obtain ⟨C, rfl⟩ := Multiset.exists_cons_of_mem hdmem
    have hd := hp d (Multiset.mem_cons_self _ _)
    have hC : ∀ t ∈ C, 0 < t := fun t ht => hp t (Multiset.mem_cons_of_mem ht)
    have hsum : C.sum ≤ n := by simp only [Multiset.sum_cons] at hs; omega
    have hi := ih C hC hsum
    apply Finset.mem_union_right
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨⟨C, hi, d, by simp only [mem_Icc]; simp only [Multiset.sum_cons] at hs; omega, rfl⟩, hs⟩


private def canonicalList (A : Shape) : List ℕ :=
  Quot.liftOn A (List.insertionSort (· ≤ ·)) (fun a b h => by
    rw [← List.mergeSort_eq_insertionSort, ← List.mergeSort_eq_insertionSort]
    exact congrArg (fun C : Shape => C.sort (· ≤ ·)) (Quot.sound h))

private theorem canonicalList_coe (A : Shape) : (canonicalList A : Shape) = A := by
  induction A using Quot.inductionOn with
  | h l =>
    exact Quot.sound (List.perm_insertionSort (· ≤ ·) l)

private def checkPacks (A B : Shape) : Prop :=
  A.sum ≤ B.sum ∧ (A.map (fun n => n*n)).sum ≤ (B.map (fun n => n*n)).sum ∧
    (A = B ∨ A = classical A.sum ∨ listPacks (canonicalList A) (canonicalList B))

private instance (A B : Shape) : Decidable (checkPacks A B) :=
  inferInstanceAs (Decidable (A.sum ≤ B.sum ∧
    (A.map (fun n => n*n)).sum ≤ (B.map (fun n => n*n)).sum ∧
    (A = B ∨ A = classical A.sum ∨ listPacks (canonicalList A) (canonicalList B))))

private theorem checkPacks_iff (A B : Shape) : checkPacks A B ↔ Packs A B := by
  constructor
  · rintro ⟨hs, _, he | hc | hp⟩
    · subst A
      exact h62_packs_refl B
    · have hh : Packs (classical A.sum) B :=
        (h62_packs_equal 1 A.sum Nat.one_pos B).mpr (by simpa using hs)
      exact hc.symm ▸ hh
    · exact (packs_lists A B _ _ (canonicalList_coe _) (canonicalList_coe _)).mpr hp
  · intro h
    refine ⟨h62_packs_lengthDim A B h, ?_, Or.inr (Or.inr ?_)⟩
    · rw [← h62_sum_blocks_map A (fun n => n*n), ← h62_sum_blocks_map B (fun n => n*n)]
      exact h62_packs_sq A B h
    · exact (packs_lists A B _ _ (canonicalList_coe _) (canonicalList_coe _)).mp h

private theorem embeds_check (A B : Shape) (hA : Valid A) : Embeds A B ↔ checkPacks A B :=
  (h62_embeds_iff_packs A B hA).trans (checkPacks_iff A B).symm

private theorem valid_antisymm (A B : Shape) (hA : Valid A) (hB : Valid B)
    (hAB : Embeds A B) (hBA : Embeds B A) : A = B :=
  h62_packs_eq A B hA.2 hB.2 ((h62_embeds_iff_packs A B hA).mp hAB)
    (h62_packs_sq B A ((h62_embeds_iff_packs B A hB).mp hBA))

private theorem basis_forbidden (A : Shape) (S : Finset Shape)
    (hv : ∀ X ∈ S, Valid X) (hn : ∀ X ∈ S, ¬ Embeds X A)
    (hc : ∀ B, Valid B → ¬ Embeds B A → ∃ X ∈ S, Embeds X B)
    (hi : ∀ X ∈ S, ∀ Y ∈ S, Embeds X Y → X = Y) : forbidden A = (S : Set Shape) := by
  ext B
  constructor
  · rintro ⟨hB, hnB, hmin⟩
    obtain ⟨X,hXS,hXB⟩ := hc B hB hnB
    have : X = B := by
      by_contra hne
      exact hn X hXS (hmin X (hv X hXS) hXB hne)
    exact this ▸ hXS
  · intro hBS
    refine ⟨hv B hBS, hn B hBS, ?_⟩
    intro C hC hCB hne
    by_contra hnC
    obtain ⟨X,hXS,hXC⟩ := hc C hC hnC
    have hXB := h62_embeds_trans X C B (hv X hXS) hC hXC hCB
    have hXB' := hi X hXS B hBS hXB
    subst X
    exact hne (valid_antisymm C B hC (hv B hBS) hCB hXC)

private theorem valid_quantum (d : ℕ) (hd : 0 < d) : Valid (quantum d) := by
  simp [Valid, quantum, hd]

private theorem quantum_forbidden (d : ℕ) (hd : 1 ≤ d) :
    forbidden (quantum d) = {classical (d+1)} := by
  rw [← Finset.coe_singleton]
  apply basis_forbidden (quantum d) {classical (d+1)}
  · intro X hX
    simp only [mem_singleton] at hX
    subst X
    exact h62_classical_valid (d+1) (by omega)
  · intro X hX
    simp only [mem_singleton] at hX
    subst X
    rw [h62_classical_embeds]
    simp [lengthDim, quantum]
  · intro B hB hnB
    have hgt : d < lengthDim B := by
      by_contra h
      exact hnB ((h62_embeds_iff_packs B _ hB).mpr ((h62_packs_quantum B d).mpr (by omega)))
    exact ⟨classical (d+1), by simp, (h62_classical_embeds _ _).mpr hgt⟩
  · intro X hX Y hY _
    simp only [mem_singleton] at hX hY
    exact hX.trans hY.symm

private theorem q2_equal : quantum 2 = equalBlocks 2 1 := rfl

private theorem all_ones_of_no_q2 (B : Shape) (hB : Valid B) (hn : ¬ Embeds (quantum 2) B) :
    B = classical B.card := by
  have hsum : (B.map (fun n => n / 2)).sum = 0 := by
    rw [q2_equal, h62_embeds_equal_iff 2 1 (by omega)] at hn
    omega
  apply Multiset.eq_replicate_card.mpr
  intro d hd
  have hdiv : d/2 = 0 := (Multiset.sum_eq_zero_iff.mp hsum) _ (Multiset.mem_map.mpr ⟨d,hd,rfl⟩)
  have hpos := hB.2 d hd
  omega

private theorem classical_forbidden (c : ℕ) (hc : 2 ≤ c) :
    forbidden (classical c) = {quantum 2, classical (c+1)} := by
  have nq (m : ℕ) : ¬ Embeds (quantum 2) (classical m) := by
    rw [q2_equal, h62_embeds_equal_iff 2 1 (by omega)]
    simp [classical, equalBlocks]
  rw [← Finset.coe_singleton, ← Finset.coe_insert]
  apply basis_forbidden (classical c) {quantum 2, classical (c+1)}
  · intro X hX
    simp only [mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl
    · exact valid_quantum _ (by omega)
    · exact h62_classical_valid _ (by omega)
  · intro X hX
    simp only [mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl
    · exact nq c
    · rw [h62_classical_embeds, h62_classical_len]
      omega
  · intro B hB hnB
    by_cases hq : Embeds (quantum 2) B
    · exact ⟨quantum 2, by simp, hq⟩
    have he := all_ones_of_no_q2 B hB hq
    have hdim : c < lengthDim B := by
      by_contra hh
      apply hnB
      rw [he, h62_classical_embeds, h62_classical_len]
      have : lengthDim B = B.card := by rw [he, h62_classical_len]; simp [classical, equalBlocks]
      omega
    exact ⟨classical (c+1), by simp, (h62_classical_embeds _ _).mpr hdim⟩
  · intro X hX Y hY hXY
    simp only [mem_insert, mem_singleton] at hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · rfl
    · exact (nq (c+1) hXY).elim
    · rw [h62_classical_embeds] at hXY
      simp [lengthDim, quantum] at hXY
      omega
    · rfl


private instance (priority := 2000) {α : Type} (s : Finset α) (p : α → Prop)
    [DecidablePred p] : Decidable (∀ x ∈ s, p x) :=
  @Multiset.decidableForallMultiset α s.val p _

private instance (priority := 2000) {α : Type} (s : Multiset α) (p : α → Prop)
    [DecidablePred p] : Decidable (∀ x ∈ s, p x) :=
  @Multiset.decidableForallMultiset α s p _

private instance (A : Shape) : Decidable (Valid A) :=
  inferInstanceAs (Decidable (A ≠ 0 ∧ ∀ d ∈ A, 0 < d))

private def finiteForbidden (A : Shape) (N : ℕ) : Finset Shape :=
  (enumShapes N).filter (fun B => Valid B ∧ ¬ checkPacks B A ∧
    ∀ C ∈ enumShapes B.sum, Valid C → checkPacks C B → C ≠ B → checkPacks C A)

private theorem finiteForbidden_eq (A : Shape) (_hA : Valid A) (N : ℕ)
    (hN : lengthDim A + 1 ≤ N) : forbidden A = (finiteForbidden A N : Set Shape) := by
  ext B
  constructor
  · intro hB
    have hbound := fo_bound A B hB
    simp only [Finset.mem_coe, finiteForbidden, mem_filter]
    refine ⟨mem_enum N B hB.1.2 (hbound.trans hN), hB.1,
      fun h => hB.2.1 ((embeds_check B A hB.1).mpr h), ?_⟩
    intro C _ hC hCB hne
    exact (embeds_check C A hC).mp (hB.2.2 C hC ((embeds_check C B hC).mpr hCB) hne)
  · intro hB
    simp only [Finset.mem_coe, finiteForbidden, mem_filter] at hB
    refine ⟨hB.2.1, fun h => hB.2.2.1 ((embeds_check B A hB.2.1).mp h), ?_⟩
    intro C hC hCB hne
    have hbound := h62_packs_lengthDim C B ((h62_embeds_iff_packs C B hC).mp hCB)
    exact (embeds_check C A hC).mpr (hB.2.2.2 C (mem_enum B.sum C hC.2 hbound)
      hC ((embeds_check C B hC).mp hCB) hne)





set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_table1 :
    finiteForbidden (quantum 2 + quantum 1) 4 = {quantum 3, classical 4} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_table2 :
    finiteForbidden (quantum 3 + quantum 1) 5 = {equalBlocks 2 2, classical 5} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_table3 :
    finiteForbidden (quantum 3 + quantum 2) 6 = {quantum 4, classical 6} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_table4 :
    finiteForbidden (quantum 4 + quantum 1) 6 = {quantum 3 + quantum 2, classical 6} := by
  decide +kernel

/-- Table 1 of Salzmann–Singh, arXiv:2609.40054v1, PDF page 38. -/
theorem solution :
    (∀ d : ℕ, 1 ≤ d → forbidden (quantum d) = {classical (d + 1)}) ∧
    (∀ c : ℕ, 2 ≤ c → forbidden (classical c) = {quantum 2, classical (c + 1)}) ∧
    forbidden (quantum 2 + quantum 1) = {quantum 3, classical 4} ∧
    forbidden (quantum 3 + quantum 1) = {equalBlocks 2 2, classical 5} ∧
    forbidden (quantum 3 + quantum 2) = {quantum 4, classical 6} ∧
    forbidden (quantum 4 + quantum 1) = {quantum 3 + quantum 2, classical 6} ∧
    forbidden (quantum 1) = {classical 2} := by
  refine ⟨quantum_forbidden, classical_forbidden, ?_, ?_, ?_, ?_, quantum_forbidden 1 (by omega)⟩
  · rw [finiteForbidden_eq _ (by simp [Valid, quantum]) 4 (by simp [lengthDim, quantum]), small_table1]
    simp only [Finset.coe_insert, Finset.coe_singleton]
  · rw [finiteForbidden_eq _ (by simp [Valid, quantum]) 5 (by simp [lengthDim, quantum]), small_table2]
    simp only [Finset.coe_insert, Finset.coe_singleton]
  · rw [finiteForbidden_eq _ (by simp [Valid, quantum]) 6 (by simp [lengthDim, quantum]), small_table3]
    simp only [Finset.coe_insert, Finset.coe_singleton]
  · rw [finiteForbidden_eq _ (by simp [Valid, quantum]) 6 (by simp [lengthDim, quantum]), small_table4]
    simp only [Finset.coe_insert, Finset.coe_singleton]

#print axioms solution
