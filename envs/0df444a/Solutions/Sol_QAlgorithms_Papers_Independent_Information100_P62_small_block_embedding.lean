-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.small_block_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:00:52.493432+00:00
-- url     : https://prove2.me/submissions/0b922b20-5ac6-46f4-8f5d-d59fe587893f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P62
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.38, Lemma 4.13: blocks of size at most three. -/
theorem h62_trace_idem {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (h : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  have := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [← Matrix.trace_toLin_eq P (Pi.basisFun ℂ n), Matrix.toLin_eq_toLin', this, Matrix.rank]
  rfl

theorem h62_rank_pos {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (h : P * P = P)
    (h0 : P ≠ 0) : 1 ≤ P.rank := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, h]
  by_contra hc
  have h1 : P.trace = 0 := by rw [h62_trace_idem P h]; simp; omega
  rw [← Matrix.trace_toLin_eq P (Pi.basisFun ℂ n), Matrix.toLin_eq_toLin', LinearMap.IsIdempotentElem.trace_eq_zero_iff hi] at h1
  exact h0 (Matrix.toLin'.injective (by rw [h1, map_zero]))

theorem h62_pos (A : Shape) (hA : ∀ d ∈ A, 0 < d) (k : Block A) : 0 < blockSize A k :=
  hA _ (Multiset.mem_toList.mp (List.get_mem _ _))

theorem h62_one (A : Shape) :
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

theorem h62_E_MP (A B : Shape) (hA : ∀ d ∈ A, 0 < d) (h : Embeds A B) : MultiplicityPacking A B := by
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

theorem h62_P_E (A B : Shape) (h : Packs A B) : Embeds A B := by
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

theorem h62_MP_P (A B : Shape) (h : MultiplicityPacking A B) : Packs A B := by
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

theorem h62_P_MP (A B : Shape) (h : Packs A B) : MultiplicityPacking A B := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun k j => if f k = j then 1 else 0, fun j => ?_, fun k => ?_⟩
  · refine le_trans (le_of_eq ?_) (hf j)
    simp [ite_mul, Finset.sum_ite]
  · rw [Finset.sum_eq_single (f k)] <;> simp; exact fun b hb h => hb h.symm

theorem h62_embeds_iff_packs (A B : Shape) (hA : Valid A) : Embeds A B ↔ Packs A B :=
  ⟨fun h => h62_MP_P A B (h62_E_MP A B hA.2 h), h62_P_E A B⟩

theorem h62_embeds_iff_mp (A B : Shape) (hA : Valid A) : Embeds A B ↔ MultiplicityPacking A B :=
  ⟨h62_E_MP A B hA.2, fun h => h62_P_E A B (h62_MP_P A B h)⟩

theorem h62_sum_blocks (A : Shape) : ∑ k : Block A, blockSize A k = lengthDim A := by
  unfold blockSize lengthDim
  rw [← List.sum_ofFn, List.ofFn_get, Multiset.sum_toList]

theorem h62_quantum_blockSize (D : ℕ) (j : Block (quantum D)) : blockSize (quantum D) j = D := by
  have : (quantum D).toList = [D] := by simp [quantum]
  unfold blockSize
  have hj : j.val = 0 := by
    have h2 := j.2
    have : (quantum D).toList.length = 1 := by rw [this]; rfl
    omega
  simp only [List.get_eq_getElem]
  simp [this, hj]

theorem h62_packs_quantum (A : Shape) (D : ℕ) : Packs A (quantum D) ↔ lengthDim A ≤ D := by
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

theorem h62_finite (D : ℕ) : {B : Shape | Valid B ∧ lengthDim B ≤ D}.Finite := by
  have hmem : ∀ B : Shape, Valid B ∧ lengthDim B ≤ D → ∀ d ∈ B, d ≤ D := fun B hB d hd =>
    le_trans (Multiset.le_sum_of_mem hd) hB.2
  have hcnt : ∀ B : Shape, Valid B ∧ lengthDim B ≤ D → ∀ d, Multiset.count d B ≤ D := by
    intro B hB d
    refine le_trans (Multiset.count_le_card _ _) (le_trans ?_ hB.2)
    have := Multiset.card_nsmul_le_sum (s := B) (a := 1) (fun x hx => hB.1.2 x hx)
    simpa [lengthDim] using this
  let φ : Shape → (Fin (D+1) → Fin (D+1)) := fun B d => ⟨min (Multiset.count d.val B) D, by omega⟩
  apply Set.Finite.of_finite_image (f := φ) (Set.toFinite _)
  intro B hB B' hB' h
  ext a
  by_cases ha : a ≤ D
  · have := congrFun h ⟨a, by omega⟩
    simp only [φ, Fin.mk.injEq] at this
    rwa [min_eq_left (hcnt B hB a), min_eq_left (hcnt B' hB' a)] at this
  · rw [Multiset.count_eq_zero.mpr (fun h' => ha (hmem B hB a h')),
      Multiset.count_eq_zero.mpr (fun h' => ha (hmem B' hB' a h'))]

theorem h62_sum_blocks_map (A : Shape) (g : ℕ → ℕ) :
    ∑ k : Block A, g (blockSize A k) = (A.map g).sum := by
  have : A.map g = ((A.toList.map g : List ℕ) : Multiset ℕ) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  rw [this, Multiset.sum_coe, ← List.sum_ofFn]
  unfold blockSize
  congr 1
  apply List.ext_get <;> simp

theorem h62_eq_blockSize (d c : ℕ) (k : Block (equalBlocks d c)) : blockSize (equalBlocks d c) k = d :=
  Multiset.eq_of_mem_replicate (Multiset.mem_toList.mp (List.get_mem _ _))

theorem h62_packs_equal (d c : ℕ) (hd : 0 < d) (B : Shape) :
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
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk
        simp only [Finset.coe_map, Finset.coe_univ, Set.image_univ, Function.Embedding.coeFn_mk,
          Set.mem_range]
        generalize emb k = x at *
        obtain ⟨j', i⟩ := x
        simp only at hk
        subst hk
        exact ⟨i, rfl⟩
    calc (univ.filter (fun k => (emb k).1 = j)).card * d ≤ m j * d := Nat.mul_le_mul_right _ this
      _ ≤ blockSize B j := Nat.div_mul_le_self _ _

theorem h62_embeds_equal_iff (d c : ℕ) (hd : 0 < d) (B : Shape) :
    Embeds (equalBlocks d c) B ↔ c ≤ (B.map (fun n => n / d)).sum := by
  rw [← h62_packs_equal d c hd B]
  refine ⟨fun h => h62_MP_P _ _ (h62_E_MP _ _ ?_ h), h62_P_E _ _⟩
  intro x hx
  rw [Multiset.eq_of_mem_replicate hx]; exact hd

theorem h62_packingNumber (d : ℕ) (hd : 0 < d) (B : Shape) :
    packingNumber d B = (B.map (fun n => n / d)).sum := by
  unfold packingNumber
  rw [if_neg (by omega)]
  have hN : (B.map (fun n => n / d)).sum ≤ lengthDim B := by
    unfold lengthDim
    have := Multiset.sum_map_le_sum_map (s := B) (fun n => n / d) (fun n => n) (fun n _ => Nat.div_le_self n d)
    simpa using this
  apply le_antisymm
  · apply Finset.sup_le
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact (h62_embeds_equal_iff d c hd B).1 hc
  · have hm : (⟨(B.map (fun n => n / d)).sum, by omega⟩ : Fin (lengthDim B + 1)) ∈
        univ.filter (fun c : Fin (lengthDim B + 1) => Embeds (equalBlocks d c.val) B) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (h62_embeds_equal_iff d _ hd B).2 le_rfl
    exact Finset.le_sup (f := Fin.val) hm

theorem h62_foldl_sum (g : ℕ → ℕ) (l : List Shape) (s : Shape) :
    ((l.foldl (· + ·) s).map g).sum = (s.map g).sum + (l.map (fun t => (t.map g).sum)).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp [List.foldl, ih, Multiset.map_add, add_assoc]

theorem h62_shape_eq (A : Shape) : (univ : Finset (Block A)).val.map (blockSize A) = A := by
  conv_rhs => rw [← Multiset.coe_toList A]
  rw [Fin.univ_val_map]
  congr 1
  unfold blockSize
  exact List.ofFn_get _

theorem h62_packs_trans (A B C : Shape) (h1 : Packs A B) (h2 : Packs B C) : Packs A C := by
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

theorem h62_packs_lengthDim (A B : Shape) (h : Packs A B) : lengthDim A ≤ lengthDim B := by
  obtain ⟨f, hf⟩ := h
  rw [← h62_sum_blocks, ← h62_sum_blocks, ← Finset.sum_fiberwise_of_maps_to (g := f) (t := univ)
    (fun _ _ => Finset.mem_univ _)]
  exact Finset.sum_le_sum (fun j _ => hf j)

theorem h62_sq_le {ι : Type} (s : Finset ι) (c : ι → ℕ) :
    ∑ k ∈ s, c k * c k ≤ ∑ k ∈ s, c k * (∑ i ∈ s, c i) :=
  Finset.sum_le_sum (fun k hk => Nat.mul_le_mul_left _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk))

theorem h62_packs_eq (C B : Shape) (hC : ∀ d ∈ C, 0 < d) (hB : ∀ d ∈ B, 0 < d) (h : Packs C B)
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

theorem h62_packs_sq (C B : Shape) (h : Packs C B) :
    ∑ k : Block C, blockSize C k * blockSize C k ≤ ∑ j : Block B, blockSize B j * blockSize B j := by
  obtain ⟨f, hf⟩ := h
  rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_le_sum
  intro j _
  refine le_trans (h62_sq_le _ _) ?_
  rw [← Finset.sum_mul]
  exact Nat.mul_le_mul (hf j) (hf j)

theorem h62_packs_refl (A : Shape) : Packs A A :=
  ⟨id, fun j => by simp [Finset.filter_eq']⟩

theorem h62_embeds_trans (A B C : Shape) (hA : Valid A) (hB : Valid B) (h1 : Embeds A B)
    (h2 : Embeds B C) : Embeds A C :=
  h62_P_E _ _ (h62_packs_trans A B C ((h62_embeds_iff_packs A B hA).1 h1)
    ((h62_embeds_iff_packs B C hB).1 h2))

theorem h62_classical_valid (m : ℕ) (hm : 1 ≤ m) : Valid (classical m) := by
  refine ⟨?_, fun d hd => ?_⟩
  · unfold classical equalBlocks
    intro h
    have := congrArg Multiset.card h
    simp at this; omega
  · unfold classical equalBlocks at hd
    rw [Multiset.eq_of_mem_replicate hd]; exact Nat.one_pos

theorem h62_classical_len (m : ℕ) : lengthDim (classical m) = m := by
  simp [lengthDim, classical, equalBlocks]

theorem h62_classical_embeds (m : ℕ) (B : Shape) : Embeds (classical m) B ↔ m ≤ lengthDim B := by
  unfold classical
  rw [h62_embeds_equal_iff 1 m Nat.one_pos B]
  simp [lengthDim]

theorem h62_strict (C' C : Shape) (hC' : Valid C') (hC : Valid C) (h : Embeds C' C) (hne : C' ≠ C) :
    ∑ k : Block C', blockSize C' k * blockSize C' k < ∑ j : Block C, blockSize C j * blockSize C j := by
  have hp := (h62_embeds_iff_packs C' C hC').1 h
  rcases lt_or_eq_of_le (h62_packs_sq C' C hp) with h1 | h1
  · exact h1
  · exact absurd (h62_packs_eq C' C hC'.2 hC.2 hp h1.ge) hne

theorem h41_sum_upd {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ℕ) (i0 : ι) (v : ℕ) (φ : ℕ → ℕ) :
    ∑ k, φ (Function.update g i0 v k) + φ (g i0) = ∑ k, φ (g k) + φ v := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
  rw [Function.update_self]
  have : ∑ k ∈ univ.erase i0, φ (Function.update g i0 v k) = ∑ k ∈ univ.erase i0, φ (g k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [this]; ring

theorem h41_exists_pos {κ : Type} [Fintype κ] (g : κ → ℕ) (h : 1 ≤ ∑ j, g j) : ∃ j, 1 ≤ g j := by
  by_contra hc
  push Not at hc
  rw [Finset.sum_eq_zero (fun j _ => by have := hc j; omega)] at h
  omega

theorem h41_greedy {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty κ] :
    ∀ n, ∀ s : ι → ℕ, ∀ t : κ → ℕ, ∑ k, s k = n → (∀ k, s k ≤ 3) → (∀ j, t j ≤ 3) →
    ∑ k, s k ≤ ∑ j, t j → ∑ k, s k / 2 ≤ ∑ j, t j / 2 → ∑ k, s k / 3 ≤ ∑ j, t j / 3 →
    ∃ f : ι → κ, ∀ j, ∑ k ∈ univ.filter (fun k => f k = j), s k ≤ t j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s t hn hs ht H1 H2 H3
  by_cases h0 : n = 0
  · obtain ⟨j0⟩ := (inferInstance : Nonempty κ)
    refine ⟨fun _ => j0, fun j => ?_⟩
    have hz : ∀ k, s k = 0 := fun k => by
      have := Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k); omega
    simp [hz]
  have hne : (univ : Finset ι).Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc, Finset.sum_empty] at hn; omega
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image univ s hne
  set b := s i0 with hb
  have hbpos : 1 ≤ b := by
    by_contra hc
    have hz : ∀ k, s k = 0 := fun k => by have := hmax k (Finset.mem_univ k); omega
    rw [Finset.sum_eq_zero (fun k _ => hz k)] at hn; omega
  let s' := Function.update s i0 0
  have hs'le : ∀ k, s' k ≤ s k := fun k => by
    by_cases hk : k = i0
    · subst hk; simp [s']
    · simp [s', Function.update_of_ne hk]
  have hS : ∀ φ : ℕ → ℕ, ∑ k, φ (s' k) + φ b = ∑ k, φ (s k) + φ 0 := fun φ => h41_sum_upd s i0 0 φ
  have hT : ∀ (j : κ) (v : ℕ) (φ : ℕ → ℕ), ∑ k, φ (Function.update t j v k) + φ (t j) = ∑ k, φ (t k) + φ v :=
    fun j v φ => h41_sum_upd t j v φ
  have hzero : ∀ d, b < d → ∑ k, s' k / d = 0 := fun d hd =>
    Finset.sum_eq_zero (fun k _ => Nat.div_eq_of_lt (lt_of_le_of_lt (hs'le k) (lt_of_le_of_lt (hmax k (Finset.mem_univ k)) hd)))
  -- choose j
  obtain ⟨j, hj, K1, K2, K3⟩ : ∃ j, b ≤ t j ∧ ∑ k, s' k ≤ ∑ k, Function.update t j (t j - b) k ∧
      ∑ k, s' k / 2 ≤ ∑ k, Function.update t j (t j - b) k / 2 ∧
      ∑ k, s' k / 3 ≤ ∑ k, Function.update t j (t j - b) k / 3 := by
    have S1 := hS id; have S2 := hS (· / 2); have S3 := hS (· / 3)
    simp only [id] at S1 S2 S3
    have hb3 : b ≤ 3 := hs i0
    have hsb : ∀ d, b / d ≤ ∑ k, s k / d := fun d =>
      Finset.single_le_sum (f := fun k => s k / d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
    have hs1 := hsb 1; have hs2 := hsb 2; have hs3 := hsb 3
    simp only [Nat.div_one] at hs1
    rcases (show b = 1 ∨ b = 2 ∨ b = 3 by omega) with hb1 | hb2 | hb3'
    · obtain ⟨j, hj⟩ := h41_exists_pos t (by omega)
      have T1 := hT j (t j - b) id; simp only [id] at T1
      refine ⟨j, by omega, by omega, ?_, ?_⟩
      · rw [hzero 2 (by omega)]; exact Nat.zero_le _
      · rw [hzero 3 (by omega)]; exact Nat.zero_le _
    · by_cases h2 : ∃ j, t j = 2
      · obtain ⟨j, hj⟩ := h2
        have T1 := hT j (t j - b) id; simp only [id] at T1
        have T2 := hT j (t j - b) (· / 2); have T3 := hT j (t j - b) (· / 3)
        refine ⟨j, by omega, by omega, ?_, ?_⟩
        · omega
        · rw [hzero 3 (by omega)]; exact Nat.zero_le _
      · push Not at h2
        obtain ⟨j, hj⟩ := h41_exists_pos (fun j => t j / 2) (by rw [hb2] at hs2; omega)
        have hj3 : t j = 3 := by have := ht j; have := h2 j; omega
        have T1 := hT j (t j - b) id; simp only [id] at T1
        have T2 := hT j (t j - b) (· / 2)
        refine ⟨j, by omega, by omega, ?_, ?_⟩
        · omega
        · rw [hzero 3 (by omega)]; exact Nat.zero_le _
    · obtain ⟨j, hj⟩ := h41_exists_pos (fun j => t j / 3) (by rw [hb3'] at hs3; omega)
      have hj3 : t j = 3 := by have := ht j; omega
      have T1 := hT j (t j - b) id; simp only [id] at T1
      have T2 := hT j (t j - b) (· / 2); have T3 := hT j (t j - b) (· / 3)
      refine ⟨j, by omega, by omega, ?_, ?_⟩
      · omega
      · omega
  set t' := Function.update t j (t j - b) with ht'
  have hlt : ∑ k, s' k < n := by
    have : ∑ k, s' k + b = ∑ k, s k := by simpa using hS id
    omega
  obtain ⟨f', hf'⟩ := ih _ hlt s' t' rfl (fun k => le_trans (hs'le k) (hs k))
    (fun k => by
      by_cases hk : k = j
      · subst hk; simp [t']; have := ht k; omega
      · simp [t', Function.update_of_ne hk, ht k]) K1 K2 K3
  refine ⟨Function.update f' i0 j, fun J => ?_⟩
  rw [Finset.sum_filter]
  have hpt : ∀ k, (if Function.update f' i0 j k = J then s k else 0) ≤
      (if f' k = J then s' k else 0) + (if k = i0 then (if J = j then b else 0) else 0) := by
    intro k
    by_cases hk : k = i0
    · rw [hk]; simp only [s', Function.update_self, if_true]
      by_cases hJ : J = j
      · rw [if_pos hJ.symm, if_pos hJ]; omega
      · rw [if_neg (fun h => hJ h.symm), if_neg hJ]; omega
    · simp only [s', Function.update_of_ne hk, hk, if_false, add_zero]; exact le_rfl
  refine le_trans (Finset.sum_le_sum (fun k _ => hpt k)) ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_ite_eq' univ i0]
  have := hf' J
  simp only [Finset.mem_univ, if_true]
  by_cases hJ : J = j
  · subst hJ; simp [t'] at this; rw [if_pos rfl]; omega
  · simp [t', Function.update_of_ne hJ] at this; rw [if_neg hJ]; omega

theorem solution (A B : Shape) (hA : Valid A) (hB : Valid B)
    (ha : ∀ d ∈ A, d ≤ 3) (hb : ∀ d ∈ B, d ≤ 3) :
    Embeds B A ↔ ∀ d ∈ Icc 1 3, packingNumber d B ≤ packingNumber d A := by
  have hPN : ∀ d ∈ Icc 1 3, ∀ X : Shape, packingNumber d X = (X.map (fun n => n / d)).sum :=
    fun d hd X => h62_packingNumber d (by simp at hd; omega) X
  constructor
  · intro h d hd
    have hd0 : 0 < d := by simp at hd; omega
    rw [hPN d hd, hPN d hd]
    have hp := (h62_embeds_iff_packs B A hB).1 h
    have h1 := (h62_packs_equal d ((B.map (fun n => n / d)).sum) hd0 B).2 le_rfl
    exact (h62_packs_equal d _ hd0 A).1 (h62_packs_trans _ _ _ h1 hp)
  · intro h
    have H : ∀ d ∈ Icc 1 3, ∑ k : Block B, blockSize B k / d ≤ ∑ j : Block A, blockSize A j / d := by
      intro d hd
      rw [h62_sum_blocks_map B (fun n => n / d), h62_sum_blocks_map A (fun n => n / d), ← hPN d hd, ← hPN d hd]
      exact h d hd
    have H1 := H 1 (by simp); have H2 := H 2 (by simp); have H3 := H 3 (by simp)
    simp only [Nat.div_one] at H1
    haveI : Nonempty (Block A) := by
      have : 0 < A.toList.length := by
        rw [Multiset.length_toList, Multiset.card_pos]; exact hA.1
      exact ⟨⟨0, this⟩⟩
    obtain ⟨f, hf⟩ := h41_greedy _ (blockSize B) (blockSize A) rfl
      (fun k => hb _ (Multiset.mem_toList.mp (List.get_mem _ _)))
      (fun k => ha _ (Multiset.mem_toList.mp (List.get_mem _ _))) H1 H2 H3
    apply h62_P_E
    refine ⟨f, fun j => ?_⟩
    convert hf j


end

