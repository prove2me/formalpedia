-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.faithful_dimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:20:53.276647+00:00
-- url     : https://prove2.me/submissions/1d852d68-a7ef-4051-9b7d-c6a36fa67639

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P62
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.12, Lemma 2.2: faithful representation dimension. -/
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

theorem h62_pos (A : Shape) (hA : Valid A) (k : Block A) : 0 < blockSize A k :=
  hA.2 _ (Multiset.mem_toList.mp (List.get_mem _ _))

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

theorem h62_E_MP (A B : Shape) (hA : Valid A) (h : Embeds A B) : MultiplicityPacking A B := by
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
  ⟨fun h => h62_MP_P A B (h62_E_MP A B hA h), h62_P_E A B⟩

theorem h62_embeds_iff_mp (A B : Shape) (hA : Valid A) : Embeds A B ↔ MultiplicityPacking A B :=
  ⟨h62_E_MP A B hA, fun h => h62_P_E A B (h62_MP_P A B h)⟩

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

theorem solution (A : Shape) (hA : Valid A) (D : ℕ) (hD : 0 < D) :
    (Embeds A (quantum D) ↔ lengthDim A ≤ D) ∧
    {B : Shape | Valid B ∧ Embeds B (quantum D)}.Finite := by
  have key : ∀ B : Shape, Valid B → (Embeds B (quantum D) ↔ lengthDim B ≤ D) := fun B hB =>
    (h62_embeds_iff_packs B (quantum D) hB).trans (h62_packs_quantum B D)
  refine ⟨key A hA, (h62_finite D).subset ?_⟩
  rintro B ⟨hB, he⟩
  exact ⟨hB, (key B hB).1 he⟩


end

