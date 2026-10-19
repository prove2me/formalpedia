-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.capacity_necessity_and_maximality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:50:08.793956+00:00
-- url     : https://prove2.me/submissions/8b2b739d-e11d-4c2b-b996-007d8517990c

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_embedding_packing
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_unique_capacity_reconstruction

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
noncomputable section
open scoped ComplexConjugate Matrix ComplexOrder
open Finset
attribute [local instance] Classical.propDecidable
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

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

private theorem empty_embed (A : Shape) : Embeds 0 A := by
  refine ⟨0, ?_, ?_, ?_⟩
  · intro x y _
    funext k
    have h : k.val < 0 := by simpa [Block] using k.isLt
    omega
  · simp
  · simp

private theorem embeds_trans {A B C : Shape} (hab : Embeds A B) (hbc : Embeds B C) : Embeds A C := by
  obtain ⟨f, hf⟩ := hab
  obtain ⟨g, hg⟩ := hbc
  refine ⟨g.comp f, hg.1.comp hf.1, ?_, ?_⟩
  · intro x y
    change g (f (x * y)) = g (f x) * g (f y)
    rw [hf.2.1, hg.2.1]
  · intro x
    change g (f (star x)) = star (g (f x))
    rw [hf.2.2, hg.2.2]

omit [DecidableEq O] in
private theorem hybrid_attained (F : Superop I O) (d : ℕ) (hd : 0 < d)
    (hc : hybrid F d ≠ 0) : Transmits F (equalBlocks d (hybrid F d)) := by
  let s := univ.filter (fun c : Fin (Fintype.card I + 1) => Transmits F (equalBlocks d c.val))
  have hs : s.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : hybrid F d = 0 := by
      unfold hybrid
      rw [if_neg hd.ne']
      change s.sup Fin.val = 0
      simp [he]
    exact hc hz
  obtain ⟨c, hc', he⟩ := Finset.exists_mem_eq_sup s hs Fin.val
  have ht := (Finset.mem_filter.mp hc').2
  have hh : hybrid F d = c.val := by
    unfold hybrid
    rw [if_neg hd.ne']
    exact he
  rw [hh]
  exact ht

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

omit [DecidableEq O] in
private theorem candidate_embeds (F : Superop I O) (A : Shape) (hcap : capacityAlgebra F = some A)
    (hA : Valid A) (d : ℕ) (hd : d ∈ Icc 1 (dmax F)) : Embeds (equalBlocks d (hybrid F d)) A := by
  have hdpos := (Finset.mem_Icc.mp hd).1
  by_cases hc : hybrid F d = 0
  · simpa [hc, equalBlocks] using empty_embed A
  apply (eq_embed d _ hdpos A hA (Nat.pos_of_ne_zero hc)).2
  unfold capacityAlgebra at hcap
  split_ifs at hcap with hn
  · have he := Option.some.inj hcap
    rw [← he]
    have hh := candidate_floor (hybrid F) (dmax F) hn d hdpos (Finset.mem_Icc.mp hd).2
    exact le_of_eq hh.symm

theorem solution [Nonempty I] [Nonempty O] (F : Superop I O) (hF : IsChannel F) :
    (∀ A, Dominating F A → (∀ d ∈ Icc 1 (dmax F), 0 ≤ QAlgorithms.Papers.Independent.Information100.P62.multiplicity F d) ∧ capacityAlgebra F = some A) ∧
    (∀ A, capacityAlgebra F = some A → Transmits F A → Maximal F A) := by
  constructor
  · intro A hA
    apply unique_capacity_reconstruction F hF A hA.1
    intro d hd
    by_cases hc : hybrid F d = 0
    · simpa [hc, equalBlocks] using empty_embed A
    exact hA.2 _ (hybrid_attained F d (Finset.mem_Icc.mp hd).1 hc)
  · intro A hcap hA
    refine ⟨hA, ?_⟩
    intro B hB hAB
    have hrec := unique_capacity_reconstruction F hF B hB (fun d hd =>
      embeds_trans (candidate_embeds F A hcap hA.1 d hd) hAB)
    exact Option.some.inj (hcap.symm.trans hrec.2)

#print axioms solution
