-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.small_quantum_capacity_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:03:38.380994+00:00
-- url     : https://prove2.me/submissions/fcb628c5-7dd6-493e-86c5-585ac64292c3

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_capacity_necessity_and_maximality
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_small_block_embedding
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_equal_block_packing
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_embedding_packing
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_transmission_lower

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
noncomputable section
open scoped ComplexConjugate Matrix ComplexOrder
open Finset
attribute [local instance] Classical.propDecidable
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

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

private theorem valid_equal (d c : ℕ) (hd : 0 < d) (hc : 0 < c) : Valid (equalBlocks d c) := by
  constructor
  · intro h; have := congrArg Multiset.card h; simp [equalBlocks] at this; omega
  · intro a ha; rw [Multiset.eq_of_mem_replicate ha]; exact hd

private theorem eq_embed (d c : ℕ) (hd : 0 < d) (B : Shape) (hB : Valid B) (hc : 0 < c) :
    Embeds (equalBlocks d c) B ↔ c ≤ (B.map (fun n => n / d)).sum := by
  rw [(embedding_packing _ _ (valid_equal d c hd hc) hB).1]
  exact h62_packs_equal d c hd B

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

private theorem floor_sum_le (A : Shape) (d : ℕ) :
    (A.map (fun n => n / d)).sum ≤ lengthDim A := by
  induction A using Multiset.induction_on with
  | empty => simp [lengthDim]
  | @cons a A ih => simpa [lengthDim] using Nat.add_le_add (Nat.div_le_self a d) ih

private theorem sum_floor_pos (A : Shape) (d : ℕ) (hd : 0 < d) (hm : d ∈ A) :
    1 ≤ (A.map (fun n => n / d)).sum := by
  obtain ⟨B, rfl⟩ := Multiset.exists_cons_of_mem hm
  simp [Nat.div_self hd]

private theorem block_le_dmax [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Transmits F A) :
    ∀ d ∈ A, d ≤ dmax F := by
  intro d hdA
  have hd := hA.1.2 d hdA
  have hE : Embeds (quantum d) A := by
    change Embeds (equalBlocks d 1) A
    exact (eq_embed d 1 hd A hA.1 (by omega)).2 (sum_floor_pos A d hd hdA)
  have ht := transmission_lower F hF _ A (valid_equal d 1 hd (by omega)) hA hE
  have hbound : d ≤ Fintype.card I := by simpa [lengthDim, equalBlocks] using transmits_bound F _ ht
  unfold dmax
  have hm : (⟨d, by omega⟩ : Fin (Fintype.card I + 1)) ∈
      univ.filter (fun d : Fin (Fintype.card I + 1) => Transmits F (quantum d.val)) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  exact Finset.le_sup (f := Fin.val) hm

private theorem recon_equations (c : ℕ → ℕ) (D : ℕ) :
    ∀ t, t ≤ D → ∀ d, D - t < d → d ≤ D →
      reconstruction c D t d + ∑ m ∈ Icc (d + 1) D, reconstruction c D t m * (m / d : ℕ) = (c d : ℤ) := by
  intro t
  induction t with
  | zero => intro _ d h _; omega
  | succ t ih =>
    intro ht d hdt hdD
    by_cases he : d = D - t
    · subst d
      have hsum : (∑ m ∈ Icc (D - t + 1) D, reconstruction c D (t + 1) m * (m / (D - t) : ℕ)) =
          ∑ m ∈ Icc (D - t + 1) D, reconstruction c D t m * (m / (D - t) : ℕ) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm' := (Finset.mem_Icc.mp hm).1
        simp only [reconstruction]
        rw [if_neg (by omega)]
      rw [hsum]
      simp [reconstruction]
    · have hprev := ih (by omega) d (by omega) hdD
      have hsame : reconstruction c D (t + 1) d = reconstruction c D t d := by
        simp [reconstruction, he]
      have hsum : (∑ m ∈ Icc (d + 1) D, reconstruction c D (t + 1) m * (m / d : ℕ)) =
          ∑ m ∈ Icc (d + 1) D, reconstruction c D t m * (m / d : ℕ) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm' := (Finset.mem_Icc.mp hm).1
        simp only [reconstruction]
        rw [if_neg (by omega)]
      rw [hsame, hsum]
      exact hprev

private theorem candidate_floor (c : ℕ → ℕ) (D : ℕ)
    (hn : ∀ d ∈ Icc 1 D, 0 ≤ reconstruction c D D d) (d : ℕ) (hd : 0 < d) (hdD : d ≤ D) :
    let A : Shape := ↑((List.range D).flatMap (fun t => List.replicate (reconstruction c D D (t + 1)).toNat (t + 1)))
    (A.map (fun n => n / d)).sum = c d := by
  dsimp only
  have hflat : ∀ N, ((↑((List.range N).flatMap (fun t => List.replicate (reconstruction c D D (t + 1)).toNat (t + 1))) : Shape).map (fun n => n / d)).sum =
      ∑ t ∈ Finset.range N, (reconstruction c D D (t + 1)).toNat * ((t + 1) / d) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← Multiset.coe_add,
        Multiset.map_add, Multiset.sum_add, ih, Multiset.coe_replicate, Multiset.map_replicate,
        Multiset.sum_replicate, smul_eq_mul, Finset.sum_range_succ]
  rw [hflat]
  have hshift : (∑ t ∈ Finset.range D, (reconstruction c D D (t + 1)).toNat * ((t + 1) / d)) =
      ∑ m ∈ Icc 1 D, (reconstruction c D D m).toNat * (m / d) := by
    have hh := Finset.sum_Ico_add' (fun m => (reconstruction c D D m).toNat * (m / d)) 0 D 1
    simpa only [Nat.zero_add, Nat.Ico_zero_eq_range, Finset.Ico_add_one_right_eq_Icc] using hh
  rw [hshift]
  have hcut : (∑ m ∈ Icc d D, (reconstruction c D D m).toNat * (m / d)) =
      ∑ m ∈ Icc 1 D, (reconstruction c D D m).toNat * (m / d) := by
    apply Finset.sum_subset
    · intro m hm; have := Finset.mem_Icc.mp hm; exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
    · intro m hm hm'
      have hmD := (Finset.mem_Icc.mp hm).2
      have hmd : m < d := by simpa [Finset.mem_Icc, hmD] using hm'
      rw [Nat.div_eq_of_lt hmd, mul_zero]
  rw [← hcut, ← Finset.insert_Icc_succ_left_eq_Icc hdD, Finset.sum_insert (by simp), Nat.div_self hd, mul_one]
  simp only [Order.succ_eq_add_one]
  apply Nat.cast_injective (R := ℤ)
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul]
  rw [Int.toNat_of_nonneg (hn d (Finset.mem_Icc.mpr ⟨hd, hdD⟩))]
  have hs : (∑ m ∈ Icc (d + 1) D, ((reconstruction c D D m).toNat : ℤ) * (m / d : ℕ)) =
      ∑ m ∈ Icc (d + 1) D, reconstruction c D D m * (m / d : ℕ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Int.toNat_of_nonneg (hn m (by have := Finset.mem_Icc.mp hm; exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩))]
  rw [hs]
  exact recon_equations c D D le_rfl d (by omega) hdD

private theorem floor_le_hybrid [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (B : Shape) (hB : Transmits F B)
    (d : ℕ) (hd : 0 < d) : (B.map (fun n => n / d)).sum ≤ hybrid F d := by
  set c := (B.map (fun n => n / d)).sum with hc
  by_cases h : c = 0
  · omega
  have hcpos : 0 < c := Nat.pos_of_ne_zero h
  have hE : Embeds (equalBlocks d c) B := (eq_embed d c hd B hB.1 hcpos).2 (le_refl _)
  have ht := transmission_lower F hF _ B (valid_equal d c hd hcpos) hB hE
  have hb : c ≤ Fintype.card I := (floor_sum_le B d).trans (transmits_bound F B hB)
  unfold hybrid
  rw [if_neg hd.ne']
  have hm : (⟨c, by omega⟩ : Fin (Fintype.card I + 1)) ∈
      univ.filter (fun c : Fin (Fintype.card I + 1) => Transmits F (equalBlocks d c.val)) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  exact Finset.le_sup (f := Fin.val) hm

omit [DecidableEq O] in
private theorem cap_floor (F : Superop I O) (A : Shape) (hcap : capacityAlgebra F = some A)
    (d : ℕ) (hd : 0 < d) (hdD : d ≤ dmax F) :
    (A.map (fun n => n / d)).sum = hybrid F d := by
  unfold capacityAlgebra at hcap
  split_ifs at hcap with hn
  have he := Option.some.inj hcap
  rw [← he]
  exact candidate_floor (hybrid F) (dmax F) hn d hd hdD

private theorem floor_zero_above (B : Shape) (d D : ℕ) (hb : ∀ n ∈ B, n ≤ D) (hd : D < d) :
    (B.map (fun n => n / d)).sum = 0 := by
  induction B using Multiset.induction_on with
  | empty => simp
  | @cons n B ih =>
    have hn := hb n (by simp)
    have hb' : ∀ n ∈ B, n ≤ D := fun n hn => hb n (by simp [hn])
    simp [Nat.div_eq_of_lt (show n < d by omega), ih hb']

theorem solution [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (hsmall : dmax F ≤ 3) :
    HasDominating F ↔ ∃ A, capacityAlgebra F = some A ∧ Transmits F A := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, ((capacity_necessity_and_maximality F hF).1 A hA).2, hA.1⟩
  · rintro ⟨A, hcap, hA⟩
    refine ⟨A, hA, ?_⟩
    intro B hB
    have hba := block_le_dmax F hF A hA
    have hbb := block_le_dmax F hF B hB
    apply (small_block_embedding A B hA.1 hB.1
      (fun d hd => (hba d hd).trans hsmall) (fun d hd => (hbb d hd).trans hsmall)).2
    intro d hd
    have hdpos := (Finset.mem_Icc.mp hd).1
    rw [(equal_block_packing B hB.1 d hdpos).1, (equal_block_packing A hA.1 d hdpos).1]
    by_cases hdD : d ≤ dmax F
    · rw [cap_floor F A hcap d hdpos hdD]
      exact floor_le_hybrid F hF B hB d hdpos
    · rw [floor_zero_above B d (dmax F) hbb (by omega)]
      exact Nat.zero_le _

#print axioms solution
