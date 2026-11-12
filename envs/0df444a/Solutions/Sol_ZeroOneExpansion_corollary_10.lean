-- Prove2me | solution 1 for ZeroOneExpansion.corollary_10
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:54:16.138066+00:00
-- url     : https://prove2.me/submissions/c8142f54-528b-4b22-bcb6-5d38392c503c

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_compatR
import Theorems.Thm_ZeroOneExpansion_fact_6
import Theorems.Thm_ZeroOneExpansion_lemma_9

set_option autoImplicit false

namespace Aux_ZOE_cor10

open ZeroOneExpansion Matrix

def cMap : Fin 4 → (Fin 2 → ℝ)
  | 0 => ![0, 0]
  | 1 => ![0, 1]
  | 2 => ![1, 0]
  | 3 => ![1, 1]

def dMap : Fin 3 → (Fin 2 → ℝ)
  | 0 => ![0, 0]
  | 1 => ![1, 0]
  | 2 => ![0, 1]

lemma range_cMap : Set.range cMap = C := by
  ext x
  simp only [Set.mem_range, C, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩; fin_cases a <;> simp [cMap]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

lemma range_dMap : Set.range dMap = D := by
  ext x
  simp only [Set.mem_range, D, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩; fin_cases a <;> simp [dMap]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

def unBlockIdx (n : ℕ) (k : Fin (4 * n)) : (Fin n ⊕ Fin n) × Fin 2 :=
  if hk : k.val < 2 * n then
    (Sum.inl ⟨k.val / 2, by omega⟩, ⟨k.val % 2, by omega⟩)
  else
    (Sum.inr ⟨(k.val - 2 * n) / 2, by omega⟩, ⟨(k.val - 2 * n) % 2, by omega⟩)

lemma unBlockIdx_blockIdx (n : ℕ) (b : Fin n ⊕ Fin n) (j : Fin 2) :
    unBlockIdx n (blockIdx n b j) = (b, j) := by
  rcases b with i | i
  · have hlt : (blockIdx n (Sum.inl i) j).val < 2 * n := by
      simp [blockIdx]; have := i.isLt; have := j.isLt; omega
    simp only [unBlockIdx, hlt, ↓reduceDIte, Prod.mk.injEq, Sum.inl.injEq]
    have hi := i.isLt; have hj := j.isLt
    exact ⟨Fin.ext (by simp [blockIdx]; omega), Fin.ext (by simp [blockIdx]; omega)⟩
  · have hge : ¬ (blockIdx n (Sum.inr i) j).val < 2 * n := by
      simp [blockIdx]; omega
    simp only [unBlockIdx, hge, ↓reduceDIte, Prod.mk.injEq, Sum.inr.injEq]
    have hi := i.isLt; have hj := j.isLt
    exact ⟨Fin.ext (by simp [blockIdx]; omega), Fin.ext (by simp [blockIdx]; omega)⟩

lemma blockIdx_unBlockIdx (n : ℕ) (k : Fin (4 * n)) :
    blockIdx n (unBlockIdx n k).1 (unBlockIdx n k).2 = k := by
  by_cases hk : k.val < 2 * n
  · simp only [unBlockIdx, hk, ↓reduceDIte]
    ext; simp [blockIdx]; omega
  · simp only [unBlockIdx, hk, ↓reduceDIte]
    ext; simp [blockIdx]; omega

def blockEquiv (n : ℕ) : (Fin n ⊕ Fin n) × Fin 2 ≃ Fin (4 * n) where
  toFun p := blockIdx n p.1 p.2
  invFun := unBlockIdx n
  left_inv p := by rcases p with ⟨b, j⟩; exact unBlockIdx_blockIdx n b j
  right_inv := blockIdx_unBlockIdx n

def mkBlocks (n : ℕ) (f : Fin n ⊕ Fin n → Fin 2 → ℝ) : Fin (4 * n) → ℝ :=
  fun k => f (unBlockIdx n k).1 (unBlockIdx n k).2

lemma blk_mkBlocks (n : ℕ) (f : Fin n ⊕ Fin n → Fin 2 → ℝ) (b : Fin n ⊕ Fin n) :
    blk n (mkBlocks n f) b = f b := by
  ext j
  simp [blk, mkBlocks, unBlockIdx_blockIdx]

lemma mkBlocks_blk (n : ℕ) (x : Fin (4 * n) → ℝ) :
    mkBlocks n (blk n x) = x := by
  ext k
  simp [mkBlocks, blk, blockIdx_unBlockIdx]

lemma dot_eq_sum_blk (n : ℕ) (w x : Fin (4 * n) → ℝ) :
    w ⬝ᵥ x = ∑ b : Fin n ⊕ Fin n, blk n w b ⬝ᵥ blk n x b := by
  calc w ⬝ᵥ x = ∑ k : Fin (4 * n), w k * x k := rfl
    _ = ∑ p : (Fin n ⊕ Fin n) × Fin 2, w (blockEquiv n p) * x (blockEquiv n p) := by
          rw [← (blockEquiv n).sum_comp]
    _ = ∑ b : Fin n ⊕ Fin n, ∑ j : Fin 2, w (blockIdx n b j) * x (blockIdx n b j) := by
          rw [Fintype.sum_prod_type]; rfl
    _ = ∑ b : Fin n ⊕ Fin n, blk n w b ⬝ᵥ blk n x b := rfl

noncomputable def Xn_fin (n : ℕ) : Finset (Fin (4 * n) → ℝ) :=
  open Classical in
  Finset.univ.image (fun p : (Fin n → Fin 4) × (Fin n → Fin 3) =>
    mkBlocks n (Sum.elim (fun i => cMap (p.1 i)) (fun j => dMap (p.2 j))))

noncomputable def Yn_fin (n : ℕ) : Finset (Fin (4 * n) → ℝ) :=
  open Classical in
  Finset.univ.image (fun p : (Fin n → Fin 3) × (Fin n → Fin 4) =>
    mkBlocks n (Sum.elim (fun i => dMap (p.1 i)) (fun j => cMap (p.2 j))))

lemma coe_Xn_fin (n : ℕ) : (Xn_fin n : Set (Fin (4 * n) → ℝ)) = Xn n := by
  classical
  ext x
  simp only [Xn_fin, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range, Xn]
  change (∃ p : (Fin n → Fin 4) × (Fin n → Fin 3), _) ↔ ∀ i, blk n x (Sum.inl i) ∈ C ∧ blk n x (Sum.inr i) ∈ D
  constructor
  · rintro ⟨⟨fc, fd⟩, rfl⟩ i
    simp only [blk_mkBlocks, Sum.elim_inl, Sum.elim_inr, ← range_cMap, ← range_dMap]
    exact ⟨⟨fc i, rfl⟩, ⟨fd i, rfl⟩⟩
  · intro hx
    have hxc : ∀ i, ∃ a, cMap a = blk n x (Sum.inl i) := fun i => by
      rw [← Set.mem_range, range_cMap]; exact (hx i).1
    have hxd : ∀ j, ∃ b, dMap b = blk n x (Sum.inr j) := fun j => by
      rw [← Set.mem_range, range_dMap]; exact (hx j).2
    choose fc hfc using hxc
    choose fd hfd using hxd
    refine ⟨(fc, fd), ?_⟩
    have hblk : Sum.elim (fun i => cMap (fc i)) (fun j => dMap (fd j)) = blk n x := by
      ext b j; rcases b with i | i <;> simp [hfc, hfd]
    rw [hblk, mkBlocks_blk]

lemma coe_Yn_fin (n : ℕ) : (Yn_fin n : Set (Fin (4 * n) → ℝ)) = Yn n := by
  classical
  ext y
  simp only [Yn_fin, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range, Yn]
  change (∃ p : (Fin n → Fin 3) × (Fin n → Fin 4), _) ↔ ∀ i, blk n y (Sum.inl i) ∈ D ∧ blk n y (Sum.inr i) ∈ C
  constructor
  · rintro ⟨⟨fd, fc⟩, rfl⟩ i
    simp only [blk_mkBlocks, Sum.elim_inl, Sum.elim_inr, ← range_cMap, ← range_dMap]
    exact ⟨⟨fd i, rfl⟩, ⟨fc i, rfl⟩⟩
  · intro hy
    have hyd : ∀ i, ∃ b, dMap b = blk n y (Sum.inl i) := fun i => by
      rw [← Set.mem_range, range_dMap]; exact (hy i).1
    have hyc : ∀ j, ∃ a, cMap a = blk n y (Sum.inr j) := fun j => by
      rw [← Set.mem_range, range_cMap]; exact (hy j).2
    choose fd hfd using hyd
    choose fc hfc using hyc
    refine ⟨(fd, fc), ?_⟩
    have hblk : Sum.elim (fun i => dMap (fd i)) (fun j => cMap (fc j)) = blk n y := by
      ext b j; rcases b with i | i <;> simp [hfc, hfd]
    rw [hblk, mkBlocks_blk]

lemma dot_update_blk_lt {n : ℕ} (w u : Fin (4 * n) → ℝ) (b₀ : Fin n ⊕ Fin n) (p : Fin 2 → ℝ)
    (hlt : w ⬝ᵥ mkBlocks n (Function.update (blk n u) b₀ p) < w ⬝ᵥ u) :
    blk n w b₀ ⬝ᵥ p < blk n w b₀ ⬝ᵥ blk n u b₀ := by
  let a := mkBlocks n (Function.update (blk n u) b₀ p)
  change w ⬝ᵥ a < w ⬝ᵥ u at hlt
  rw [dot_eq_sum_blk n w a, dot_eq_sum_blk n w u] at hlt
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀),
      ← Finset.add_sum_erase _ (fun b => blk n w b ⬝ᵥ blk n u b) (Finset.mem_univ b₀)] at hlt
  have hrest :
      ∑ b ∈ Finset.univ.erase b₀, blk n w b ⬝ᵥ blk n a b =
        ∑ b ∈ Finset.univ.erase b₀, blk n w b ⬝ᵥ blk n u b := by
    apply Finset.sum_congr rfl
    intro b hb
    have hne : b ≠ b₀ := (Finset.mem_erase.mp hb).1
    simp [a, blk_mkBlocks, hne]
  have hb₀ : blk n a b₀ = p := by simp [a, blk_mkBlocks]
  rw [hb₀, hrest] at hlt
  linarith

end Aux_ZOE_cor10

open ZeroOneExpansion Matrix Aux_ZOE_cor10

theorem solution (n : ℕ) (hn : 1 ≤ n) (u v : Fin (4 * n) → ℝ) (hu : u ∈ Xn n)
    (hv : v ∈ Yn n) :
    IsExposed ℝ (Pn n) (segment ℝ (withLast u 0) (withLast v 1)) ↔
      ∀ i : Fin n, (blk n u (Sum.inl i), blk n v (Sum.inl i)) ∈ compatR ∧
        (blk n v (Sum.inr i), blk n u (Sum.inr i)) ∈ compatR := by
  let _ := hn
  have hu_fin : u ∈ Xn_fin n := by rw [← Finset.mem_coe, coe_Xn_fin]; exact hu
  have hv_fin : v ∈ Yn_fin n := by rw [← Finset.mem_coe, coe_Yn_fin]; exact hv
  have hPn : Pn n = cayleySum (Xn_fin n : Set (Fin (4 * n) → ℝ)) (Yn_fin n : Set (Fin (4 * n) → ℝ)) := by
    rw [Pn, coe_Xn_fin, coe_Yn_fin]
  rw [hPn, ZeroOneExpansion.fact_6 (Xn_fin n) (Yn_fin n) ⟨u, hu_fin⟩ ⟨v, hv_fin⟩ u v hu_fin hv_fin]
  constructor
  · rintro ⟨w, hwX, hwY⟩ i
    have hwX' : ∀ a ∈ Xn n, a ≠ u → w ⬝ᵥ a < w ⬝ᵥ u := by
      intro a ha hne
      exact hwX a (by rw [← Finset.mem_coe, coe_Xn_fin]; exact ha) hne
    have hwY' : ∀ b ∈ Yn n, b ≠ v → w ⬝ᵥ b < w ⬝ᵥ v := by
      intro b hb hne
      exact hwY b (by rw [← Finset.mem_coe, coe_Yn_fin]; exact hb) hne
    constructor
    · rw [← ZeroOneExpansion.lemma_9 (blk n u (Sum.inl i)) (blk n v (Sum.inl i)) (hu i).1 (hv i).1]
      refine ⟨blk n w (Sum.inl i), fun c hc hne => ?_, fun d hd hne => ?_⟩
      · let a := mkBlocks n (Function.update (blk n u) (Sum.inl i) c)
        have haX : a ∈ Xn n := by
          intro k
          constructor
          · by_cases hk : k = i
            · subst hk; simpa [a, blk_mkBlocks] using hc
            · have hne_b : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inl i := by simp [hk]
              simpa [a, blk_mkBlocks, hne_b] using (hu k).1
          · have hne_b : (Sum.inr k : Fin n ⊕ Fin n) ≠ Sum.inl i := by simp
            simpa [a, blk_mkBlocks, hne_b] using (hu k).2
        have ha_ne : a ≠ u := by
          intro heq
          apply hne
          have := congr_arg (fun z => blk n z (Sum.inl i)) heq
          simpa [a, blk_mkBlocks] using this
        exact dot_update_blk_lt w u (Sum.inl i) c (hwX' a haX ha_ne)
      · let b := mkBlocks n (Function.update (blk n v) (Sum.inl i) d)
        have hbY : b ∈ Yn n := by
          intro k
          constructor
          · by_cases hk : k = i
            · subst hk; simpa [b, blk_mkBlocks] using hd
            · have hne_b : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inl i := by simp [hk]
              simpa [b, blk_mkBlocks, hne_b] using (hv k).1
          · have hne_b : (Sum.inr k : Fin n ⊕ Fin n) ≠ Sum.inl i := by simp
            simpa [b, blk_mkBlocks, hne_b] using (hv k).2
        have hb_ne : b ≠ v := by
          intro heq
          apply hne
          have := congr_arg (fun z => blk n z (Sum.inl i)) heq
          simpa [b, blk_mkBlocks] using this
        exact dot_update_blk_lt w v (Sum.inl i) d (hwY' b hbY hb_ne)
    · rw [← ZeroOneExpansion.lemma_9 (blk n v (Sum.inr i)) (blk n u (Sum.inr i)) (hv i).2 (hu i).2]
      refine ⟨blk n w (Sum.inr i), fun c hc hne => ?_, fun d hd hne => ?_⟩
      · let b := mkBlocks n (Function.update (blk n v) (Sum.inr i) c)
        have hbY : b ∈ Yn n := by
          intro k
          constructor
          · have hne_b : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr i := by simp
            simpa [b, blk_mkBlocks, hne_b] using (hv k).1
          · by_cases hk : k = i
            · subst hk; simpa [b, blk_mkBlocks] using hc
            · have hne_b : (Sum.inr k : Fin n ⊕ Fin n) ≠ Sum.inr i := by simp [hk]
              simpa [b, blk_mkBlocks, hne_b] using (hv k).2
        have hb_ne : b ≠ v := by
          intro heq
          apply hne
          have := congr_arg (fun z => blk n z (Sum.inr i)) heq
          simpa [b, blk_mkBlocks] using this
        exact dot_update_blk_lt w v (Sum.inr i) c (hwY' b hbY hb_ne)
      · let a := mkBlocks n (Function.update (blk n u) (Sum.inr i) d)
        have haX : a ∈ Xn n := by
          intro k
          constructor
          · have hne_b : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr i := by simp
            simpa [a, blk_mkBlocks, hne_b] using (hu k).1
          · by_cases hk : k = i
            · subst hk; simpa [a, blk_mkBlocks] using hd
            · have hne_b : (Sum.inr k : Fin n ⊕ Fin n) ≠ Sum.inr i := by simp [hk]
              simpa [a, blk_mkBlocks, hne_b] using (hu k).2
        have ha_ne : a ≠ u := by
          intro heq
          apply hne
          have := congr_arg (fun z => blk n z (Sum.inr i)) heq
          simpa [a, blk_mkBlocks] using this
        exact dot_update_blk_lt w u (Sum.inr i) d (hwX' a haX ha_ne)
  · intro hcompat
    have hex1 : ∀ i : Fin n, ∃ wi : Fin 2 → ℝ,
        (∀ x ∈ C, x ≠ blk n u (Sum.inl i) → wi ⬝ᵥ x < wi ⬝ᵥ blk n u (Sum.inl i)) ∧
        (∀ x ∈ D, x ≠ blk n v (Sum.inl i) → wi ⬝ᵥ x < wi ⬝ᵥ blk n v (Sum.inl i)) :=
      fun i => (ZeroOneExpansion.lemma_9 _ _ (hu i).1 (hv i).1).mpr (hcompat i).1
    have hex2 : ∀ i : Fin n, ∃ wi : Fin 2 → ℝ,
        (∀ x ∈ C, x ≠ blk n v (Sum.inr i) → wi ⬝ᵥ x < wi ⬝ᵥ blk n v (Sum.inr i)) ∧
        (∀ x ∈ D, x ≠ blk n u (Sum.inr i) → wi ⬝ᵥ x < wi ⬝ᵥ blk n u (Sum.inr i)) :=
      fun i => (ZeroOneExpansion.lemma_9 _ _ (hv i).2 (hu i).2).mpr (hcompat i).2
    choose w1 hw1 using hex1
    choose w2 hw2 using hex2
    let w := mkBlocks n (Sum.elim w1 w2)
    refine ⟨w, fun a ha_fin hne => ?_, fun b hb_fin hne => ?_⟩
    · have ha : a ∈ Xn n := by rw [← coe_Xn_fin]; exact ha_fin
      rw [dot_eq_sum_blk n w a, dot_eq_sum_blk n w u]
      have hle_all : ∀ k : Fin n ⊕ Fin n, blk n w k ⬝ᵥ blk n a k ≤ blk n w k ⬝ᵥ blk n u k := by
        rintro (i | i)
        · simp only [w, blk_mkBlocks, Sum.elim_inl]
          by_cases h : blk n a (Sum.inl i) = blk n u (Sum.inl i)
          · rw [h]
          · exact ((hw1 i).1 _ (ha i).1 h).le
        · simp only [w, blk_mkBlocks, Sum.elim_inr]
          by_cases h : blk n a (Sum.inr i) = blk n u (Sum.inr i)
          · rw [h]
          · exact ((hw2 i).2 _ (ha i).2 h).le
      have hex_ne : ∃ k : Fin n ⊕ Fin n, blk n a k ≠ blk n u k := by
        by_contra hall
        push_neg at hall
        apply hne
        rw [← mkBlocks_blk n a, ← mkBlocks_blk n u, funext hall]
      obtain ⟨k₀, hk₀⟩ := hex_ne
      refine Finset.sum_lt_sum (fun k _ => hle_all k) ⟨k₀, Finset.mem_univ k₀, ?_⟩
      rcases k₀ with i | i
      · simp only [w, blk_mkBlocks, Sum.elim_inl]
        exact (hw1 i).1 _ (ha i).1 hk₀
      · simp only [w, blk_mkBlocks, Sum.elim_inr]
        exact (hw2 i).2 _ (ha i).2 hk₀
    · have hb : b ∈ Yn n := by rw [← coe_Yn_fin]; exact hb_fin
      rw [dot_eq_sum_blk n w b, dot_eq_sum_blk n w v]
      have hle_all : ∀ k : Fin n ⊕ Fin n, blk n w k ⬝ᵥ blk n b k ≤ blk n w k ⬝ᵥ blk n v k := by
        rintro (i | i)
        · simp only [w, blk_mkBlocks, Sum.elim_inl]
          by_cases h : blk n b (Sum.inl i) = blk n v (Sum.inl i)
          · rw [h]
          · exact ((hw1 i).2 _ (hb i).1 h).le
        · simp only [w, blk_mkBlocks, Sum.elim_inr]
          by_cases h : blk n b (Sum.inr i) = blk n v (Sum.inr i)
          · rw [h]
          · exact ((hw2 i).1 _ (hb i).2 h).le
      have hex_ne : ∃ k : Fin n ⊕ Fin n, blk n b k ≠ blk n v k := by
        by_contra hall
        push_neg at hall
        apply hne
        rw [← mkBlocks_blk n b, ← mkBlocks_blk n v, funext hall]
      obtain ⟨k₀, hk₀⟩ := hex_ne
      refine Finset.sum_lt_sum (fun k _ => hle_all k) ⟨k₀, Finset.mem_univ k₀, ?_⟩
      rcases k₀ with i | i
      · simp only [w, blk_mkBlocks, Sum.elim_inl]
        exact (hw1 i).2 _ (hb i).1 hk₀
      · simp only [w, blk_mkBlocks, Sum.elim_inr]
        exact (hw2 i).1 _ (hb i).2 hk₀
