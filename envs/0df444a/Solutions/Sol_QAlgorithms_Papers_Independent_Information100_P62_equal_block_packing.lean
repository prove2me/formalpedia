-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.equal_block_packing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:23:49.671878+00:00
-- url     : https://prove2.me/submissions/886bf77f-5b94-43d1-bfe3-930493db0c70

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P62
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.33, 34, Lemma 4.5: packing equal matrix blocks. -/
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

theorem solution (B : Shape) (hB : Valid B) (d : ℕ) (hd : 0 < d) :
    packingNumber d B = (B.map (fun n => n / d)).sum ∧
    ∀ (R : ℕ) (N : Fin R → ℕ),
      B = (List.ofFn (fun m => equalBlocks (m.val + 1) (N m))).foldl (· + ·) 0 →
      packingNumber d B = ∑ m, N m * ((m.val + 1) / d) := by
  refine ⟨h62_packingNumber d hd B, fun R N hBe => ?_⟩
  rw [h62_packingNumber d hd B, hBe, h62_foldl_sum, List.map_ofFn, List.sum_ofFn]
  simp [equalBlocks, Multiset.map_replicate, Multiset.sum_replicate]


end

