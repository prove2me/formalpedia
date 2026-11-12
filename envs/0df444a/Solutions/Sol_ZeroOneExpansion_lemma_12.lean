-- Prove2me | solution 1 for ZeroOneExpansion.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:38:26.693434+00:00
-- url     : https://prove2.me/submissions/4f7db412-3890-4d04-ac7a-554226784a90

import Mathlib
import Definitions.Def_ZeroOneExpansion_Sn
import Theorems.Thm_ZeroOneExpansion_fact_3

set_option autoImplicit false

namespace Aux_ZOE_lemma12

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

lemma cMap_injective : Function.Injective cMap := by
  intro a b h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  fin_cases a <;> fin_cases b <;> simp [cMap] at h0 h1 ⊢

lemma dMap_injective : Function.Injective dMap := by
  intro a b h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  fin_cases a <;> fin_cases b <;> simp [dMap] at h0 h1 ⊢

lemma range_cMap : Set.range cMap = C := by
  ext x
  simp only [Set.mem_range, C, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp [cMap]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

lemma range_dMap : Set.range dMap = D := by
  ext x
  simp only [Set.mem_range, D, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp [dMap]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

lemma cMap_eq_zero_iff (a : Fin 4) : cMap a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    fin_cases a <;> simp [cMap] at h0 h1 ⊢
  · rintro rfl
    ext j; fin_cases j <;> rfl

lemma dMap_eq_zero_iff (a : Fin 3) : dMap a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    fin_cases a <;> simp [dMap] at h0 h1 ⊢
  · rintro rfl
    ext j; fin_cases j <;> rfl

lemma cMap_bit (a : Fin 4) (j : Fin 2) : cMap a j = 0 ∨ cMap a j = 1 := by
  fin_cases a <;> fin_cases j <;> simp [cMap]

lemma dMap_bit (a : Fin 3) (j : Fin 2) : dMap a j = 0 ∨ dMap a j = 1 := by
  fin_cases a <;> fin_cases j <;> simp [dMap]

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

abbrev W (n : ℕ) :=
  ((Fin n → Fin 4) × (Fin n → Fin 3)) ⊕ ((Fin n → Fin 3) × (Fin n → Fin 4))

def wToVec (n : ℕ) : W n → (Fin (4 * n + 1) → ℝ)
  | Sum.inl (fc, fd) =>
      withLast (mkBlocks n (Sum.elim (fun i => cMap (fc i)) (fun j => dMap (fd j)))) 0
  | Sum.inr (fd, fc) =>
      withLast (mkBlocks n (Sum.elim (fun i => dMap (fd i)) (fun j => cMap (fc j)))) 1

lemma wToVec_injective (n : ℕ) : Function.Injective (wToVec n) := by
  intro w₁ w₂ h
  have hlast : wToVec n w₁ (Fin.last (4 * n)) = wToVec n w₂ (Fin.last (4 * n)) :=
    congr_fun h (Fin.last (4 * n))
  have hinit : Fin.init (wToVec n w₁) = Fin.init (wToVec n w₂) := by
    ext k; exact congr_fun h k.castSucc
  rcases w₁ with ⟨fc₁, fd₁⟩ | ⟨fd₁, fc₁⟩ <;> rcases w₂ with ⟨fc₂, fd₂⟩ | ⟨fd₂, fc₂⟩
  · simp only [wToVec, withLast, Fin.init_snoc] at hinit
    congr 1
    apply Prod.ext
    · funext i
      apply cMap_injective
      have := congr_arg (fun x => blk n x (Sum.inl i)) hinit
      simpa [blk_mkBlocks] using this
    · funext j
      apply dMap_injective
      have := congr_arg (fun x => blk n x (Sum.inr j)) hinit
      simpa [blk_mkBlocks] using this
  · simp [wToVec, withLast] at hlast
  · simp [wToVec, withLast] at hlast
  · simp only [wToVec, withLast, Fin.init_snoc] at hinit
    congr 1
    apply Prod.ext
    · funext i
      apply dMap_injective
      have := congr_arg (fun x => blk n x (Sum.inl i)) hinit
      simpa [blk_mkBlocks] using this
    · funext j
      apply cMap_injective
      have := congr_arg (fun x => blk n x (Sum.inr j)) hinit
      simpa [blk_mkBlocks] using this

lemma range_wToVec (n : ℕ) : Set.range (wToVec n) = Vn n := by
  ext v
  simp only [Set.mem_range, Vn, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨⟨fc, fd⟩ | ⟨fd, fc⟩, rfl⟩
    · left
      refine ⟨mkBlocks n (Sum.elim (fun i => cMap (fc i)) (fun j => dMap (fd j))), ?_, rfl⟩
      intro i
      simp only [blk_mkBlocks, Sum.elim_inl, Sum.elim_inr, ← range_cMap, ← range_dMap]
      exact ⟨⟨fc i, rfl⟩, ⟨fd i, rfl⟩⟩
    · right
      refine ⟨mkBlocks n (Sum.elim (fun i => dMap (fd i)) (fun j => cMap (fc j))), ?_, rfl⟩
      intro i
      simp only [blk_mkBlocks, Sum.elim_inl, Sum.elim_inr, ← range_cMap, ← range_dMap]
      exact ⟨⟨fd i, rfl⟩, ⟨fc i, rfl⟩⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · have hxc : ∀ i, ∃ a, cMap a = blk n x (Sum.inl i) := fun i => by
        rw [← Set.mem_range, range_cMap]; exact (hx i).1
      have hxd : ∀ j, ∃ b, dMap b = blk n x (Sum.inr j) := fun j => by
        rw [← Set.mem_range, range_dMap]; exact (hx j).2
      choose fc hfc using hxc
      choose fd hfd using hxd
      refine ⟨Sum.inl (fc, fd), ?_⟩
      simp only [wToVec]
      congr 1
      have hblk : Sum.elim (fun i => cMap (fc i)) (fun j => dMap (fd j)) = blk n x := by
        ext b j
        rcases b with i | i
        · simp [hfc i]
        · simp [hfd i]
      rw [hblk, mkBlocks_blk]
    · have hyd : ∀ i, ∃ b, dMap b = blk n y (Sum.inl i) := fun i => by
        rw [← Set.mem_range, range_dMap]; exact (hy i).1
      have hyc : ∀ j, ∃ a, cMap a = blk n y (Sum.inr j) := fun j => by
        rw [← Set.mem_range, range_cMap]; exact (hy j).2
      choose fd hfd using hyd
      choose fc hfc using hyc
      refine ⟨Sum.inr (fd, fc), ?_⟩
      simp only [wToVec]
      congr 1
      have hblk : Sum.elim (fun i => dMap (fd i)) (fun j => cMap (fc j)) = blk n y := by
        ext b j
        rcases b with i | i
        · simp [hfd i]
        · simp [hfc i]
      rw [hblk, mkBlocks_blk]

lemma wToVec_zeroOne (n : ℕ) (w : W n) (k : Fin (4 * n + 1)) :
    wToVec n w k = 0 ∨ wToVec n w k = 1 := by
  refine Fin.lastCases ?_ (fun m => ?_) k
  · rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩ <;> simp [wToVec, withLast]
  · rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩
    · simp only [wToVec, withLast, Fin.snoc_castSucc, mkBlocks]
      rcases h : (unBlockIdx n m).1 with i | j
      · exact cMap_bit (fc i) _
      · exact dMap_bit (fd j) _
    · simp only [wToVec, withLast, Fin.snoc_castSucc, mkBlocks]
      rcases h : (unBlockIdx n m).1 with i | j
      · exact dMap_bit (fd i) _
      · exact cMap_bit (fc j) _

lemma vertices_Pn_eq_Vn (n : ℕ) :
    {v : Fin (4 * n + 1) → ℝ | IsExposed ℝ (Pn n) {v}} = Vn n := by
  classical
  let X : Finset (Fin (4 * n + 1) → ℝ) := Finset.univ.image (wToVec n)
  have hX_coe : (X : Set (Fin (4 * n + 1) → ℝ)) = Vn n := by
    simp [X, Finset.coe_image, range_wToVec]
  have hX_ne : X.Nonempty := by
    refine ⟨wToVec n (Sum.inl (fun _ => 0, fun _ => 0)), ?_⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hPn : Pn n = convexHull ℝ (X : Set (Fin (4 * n + 1) → ℝ)) := by
    rw [Pn, cayleySum, ← Vn, hX_coe]
  have h01 : ∀ v ∈ X, ∀ k, v k = 0 ∨ v k = 1 := by
    intro v hv k
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact wToVec_zeroOne n w k
  have hfact3 := ZeroOneExpansion.fact_3 X hX_ne h01
  rw [hPn]
  simpa [IsVertexOf, hX_coe] using hfact3

noncomputable def wEquivVertex (n : ℕ) : W n ≃ Grunbaum2003.PolytopeVertex (Pn n) :=
  (Equiv.ofInjective (wToVec n) (wToVec_injective n)).trans
    (Equiv.setCongr (by rw [range_wToVec, ← vertices_Pn_eq_Vn]; rfl))

@[simp]
lemma wEquivVertex_val (n : ℕ) (w : W n) : (wEquivVertex n w).val = wToVec n w := rfl

lemma card_W (n : ℕ) : Fintype.card (W n) = 2 * 12 ^ n := by
  simp only [W, Fintype.card_sum, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  have h12 : 4 ^ n * 3 ^ n = 12 ^ n := by
    rw [← Nat.mul_pow]
  have h12' : 3 ^ n * 4 ^ n = 12 ^ n := by
    rw [← Nat.mul_pow]
  omega

def suppFin {n m : ℕ} (f : Fin n → Fin (m + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i ≠ 0

lemma iset_wToVec_inl (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) :
    Iset n (wToVec n (Sum.inl (fc, fd))) = suppFin fc := by
  ext i
  simp [Iset, suppFin, ublk, wToVec, withLast, Fin.init_snoc, blk_mkBlocks, cMap_eq_zero_iff]

lemma jset_wToVec_inl (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) :
    Jset n (wToVec n (Sum.inl (fc, fd))) = suppFin fd := by
  ext j
  simp [Jset, suppFin, ublk, wToVec, withLast, Fin.init_snoc, blk_mkBlocks, dMap_eq_zero_iff]

lemma iset_wToVec_inr (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) :
    Iset n (wToVec n (Sum.inr (fd, fc))) = suppFin fd := by
  ext i
  simp [Iset, suppFin, ublk, wToVec, withLast, Fin.init_snoc, blk_mkBlocks, dMap_eq_zero_iff]

lemma jset_wToVec_inr (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) :
    Jset n (wToVec n (Sum.inr (fd, fc))) = suppFin fc := by
  ext j
  simp [Jset, suppFin, ublk, wToVec, withLast, Fin.init_snoc, blk_mkBlocks, cMap_eq_zero_iff]

def icardW (n : ℕ) : W n → ℕ
  | Sum.inl (fc, _) => (suppFin fc).card
  | Sum.inr (fd, _) => (suppFin fd).card

def jcardW (n : ℕ) : W n → ℕ
  | Sum.inl (_, fd) => (suppFin fd).card
  | Sum.inr (_, fc) => (suppFin fc).card

lemma icard_wEquiv (n : ℕ) (w : W n) :
    (Iset n (wEquivVertex n w).val).card = icardW n w := by
  rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩
  · simp [icardW, iset_wToVec_inl]
  · simp [icardW, iset_wToVec_inr]

lemma jcard_wEquiv (n : ℕ) (w : W n) :
    (Jset n (wEquivVertex n w).val).card = jcardW n w := by
  rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩
  · simp [jcardW, jset_wToVec_inl]
  · simp [jcardW, jset_wToVec_inr]

def swapW (n : ℕ) : W n ≃ W n where
  toFun
    | Sum.inl (fc, fd) => Sum.inr (fd, fc)
    | Sum.inr (fd, fc) => Sum.inl (fc, fd)
  invFun
    | Sum.inl (fc, fd) => Sum.inr (fd, fc)
    | Sum.inr (fd, fc) => Sum.inl (fc, fd)
  left_inv w := by rcases w with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl
  right_inv w := by rcases w with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

lemma icardW_swap (n : ℕ) (w : W n) : icardW n (swapW n w) = jcardW n w := by
  rcases w with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

lemma jcardW_swap (n : ℕ) (w : W n) : jcardW n (swapW n w) = icardW n w := by
  rcases w with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

def suppEquiv (n m : ℕ) (K : Finset (Fin n)) :
    (K → Fin m) ≃ {f : Fin n → Fin (m + 1) // suppFin f = K} where
  toFun g :=
    ⟨fun i => if hi : i ∈ K then (g ⟨i, hi⟩).succ else 0, by
      ext i
      simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi : i ∈ K
      · simp [hi, Fin.succ_ne_zero]
      · simp [hi]⟩
  invFun f i :=
    (f.1 i.1).pred (by
      have hmem : i.1 ∈ suppFin f.1 := by rw [f.2]; exact i.2
      exact (Finset.mem_filter.mp hmem).2)
  left_inv g := by
    ext ⟨i, hi⟩
    simp [hi, Fin.pred_succ]
  right_inv f := by
    ext i
    simp only
    by_cases hi : i ∈ K
    · simp [hi, Fin.succ_pred]
    · have h0 : f.1 i = 0 := by
        by_contra hne
        have hmem : i ∈ suppFin f.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
        rw [f.2] at hmem
        exact hi hmem
      simp [hi, h0]

lemma card_suppFin_eq (n m : ℕ) (K : Finset (Fin n)) :
    (Finset.univ.filter (fun f : Fin n → Fin (m + 1) => suppFin f = K)).card = m ^ K.card := by
  have hcard : Fintype.card {f : Fin n → Fin (m + 1) // suppFin f = K} = m ^ K.card := by
    rw [← Fintype.card_congr (suppEquiv n m K)]
    simp [Fintype.card_fin]
  simpa [Fintype.card_subtype] using hcard

lemma card_suppFin_card_eq (n m r : ℕ) :
    (Finset.univ.filter (fun f : Fin n → Fin (m + 1) => (suppFin f).card = r)).card =
      n.choose r * m ^ r := by
  have hpart :
      Finset.univ.filter (fun f : Fin n → Fin (m + 1) => (suppFin f).card = r) =
        ((Finset.univ : Finset (Fin n)).powersetCard r).biUnion
          (fun K => Finset.univ.filter (fun f : Fin n → Fin (m + 1) => suppFin f = K)) := by
    ext f
    simp [Finset.mem_powersetCard]
  rw [hpart, Finset.card_biUnion]
  · have hsum :
        ∑ K ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          (Finset.univ.filter (fun f : Fin n → Fin (m + 1) => suppFin f = K)).card =
        ∑ K ∈ (Finset.univ : Finset (Fin n)).powersetCard r, m ^ r := by
      apply Finset.sum_congr rfl
      intro K hK
      rw [card_suppFin_eq, (Finset.mem_powersetCard.mp hK).2]
    rw [hsum, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
  · intro K₁ _ K₂ _ hne
    exact Finset.disjoint_left.mpr fun f hf₁ hf₂ =>
      hne ((Finset.mem_filter.mp hf₁).2.symm.trans (Finset.mem_filter.mp hf₂).2)

lemma card_diag_low (n : ℕ) :
    (Finset.univ.filter (fun p : (Fin n → Fin 4) × (Fin n → Fin 3) =>
      (suppFin p.1).card = (suppFin p.2).card)).card =
      ∑ r ∈ Finset.range (n + 1), Acount n r r := by
  have hpart :
      Finset.univ.filter (fun p : (Fin n → Fin 4) × (Fin n → Fin 3) =>
        (suppFin p.1).card = (suppFin p.2).card) =
      (Finset.range (n + 1)).biUnion (fun r =>
        (Finset.univ.filter (fun fc : Fin n → Fin 4 => (suppFin fc).card = r)) ×ˢ
        (Finset.univ.filter (fun fd : Fin n → Fin 3 => (suppFin fd).card = r))) := by
    ext ⟨fc, fd⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_product]
    constructor
    · intro h
      refine ⟨(suppFin fc).card, ?_, rfl, h.symm⟩
      have hle : (suppFin fc).card ≤ n := by
        calc (suppFin fc).card ≤ (Finset.univ : Finset (Fin n)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
      omega
    · rintro ⟨r, _, rfl, h⟩
      exact h.symm
  rw [hpart, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.card_product, card_suppFin_card_eq n 3 r, card_suppFin_card_eq n 2 r, Acount]
    ring
  · intro r₁ _ r₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨fc, fd⟩ h₁ h₂
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact hne (h₁.1.symm.trans h₂.1)

lemma card_diag_W (n : ℕ) :
    (Finset.univ.filter (fun w : W n => icardW n w = jcardW n w)).card =
      2 * ∑ r ∈ Finset.range (n + 1), Acount n r r := by
  let Slow := Finset.univ.filter (fun p : (Fin n → Fin 4) × (Fin n → Fin 3) =>
    (suppFin p.1).card = (suppFin p.2).card)
  let Shigh := Finset.univ.filter (fun p : (Fin n → Fin 3) × (Fin n → Fin 4) =>
    (suppFin p.1).card = (suppFin p.2).card)
  have hbij_high : Shigh.card = Slow.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Shigh, Slow, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.symm
    · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      cases h; rfl
    · rintro ⟨fc, fd⟩ hp
      refine ⟨(fd, fc), ?_, rfl⟩
      simp only [Shigh, Slow, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.symm
  have hsplit :
      Finset.univ.filter (fun w : W n => icardW n w = jcardW n w) =
        Slow.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Shigh.map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩
    · constructor
      · intro h
        exact Or.inl ⟨(fc, fd), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
      · rintro (⟨⟨fc', fd'⟩, hp, hinj⟩ | ⟨⟨fd', fc'⟩, _, hinj⟩)
        · cases hinj
          exact (Finset.mem_filter.mp hp).2
        · cases hinj
    · constructor
      · intro h
        exact Or.inr ⟨(fd, fc), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
      · rintro (⟨⟨fc', fd'⟩, _, hinj⟩ | ⟨⟨fd', fc'⟩, hp, hinj⟩)
        · cases hinj
        · cases hinj
          exact (Finset.mem_filter.mp hp).2
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map, hbij_high,
      card_diag_low]
  · ring
  · refine Finset.disjoint_left.mpr ?_
    intro w hw₁ hw₂
    rcases Finset.mem_map.mp hw₁ with ⟨p₁, _, rfl⟩
    rcases Finset.mem_map.mp hw₂ with ⟨p₂, _, h⟩
    cases h

lemma ncard_Sn_eq_card_Slt (n : ℕ) :
    (Sn n).ncard =
      (Finset.univ.filter (fun w : W n => icardW n w < jcardW n w)).card := by
  let Slt := Finset.univ.filter (fun w : W n => icardW n w < jcardW n w)
  have hSn : Sn n = (wEquivVertex n) '' (Slt : Set (W n)) := by
    ext v
    simp only [Sn, Set.mem_image, Finset.mem_coe, Slt, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change (Iset n v.val).card < (Jset n v.val).card ↔ _
    constructor
    · intro hv
      refine ⟨(wEquivVertex n).symm v, ?_, (wEquivVertex n).apply_symm_apply v⟩
      have h1 := icard_wEquiv n ((wEquivVertex n).symm v)
      have h2 := jcard_wEquiv n ((wEquivVertex n).symm v)
      rw [(wEquivVertex n).apply_symm_apply] at h1 h2
      rw [← h1, ← h2]
      exact hv
    · rintro ⟨w, hw, rfl⟩
      rw [icard_wEquiv, jcard_wEquiv]
      exact hw
  rw [hSn, Set.ncard_image_of_injective _ (wEquivVertex n).injective, Set.ncard_coe_finset]

lemma sum_Sn_and_diag (n : ℕ) :
    (Sn n).ncard + ∑ r ∈ Finset.range (n + 1), Acount n r r = 12 ^ n := by
  let Slt := Finset.univ.filter (fun w : W n => icardW n w < jcardW n w)
  let Sgt := Finset.univ.filter (fun w : W n => jcardW n w < icardW n w)
  let Seq := Finset.univ.filter (fun w : W n => icardW n w = jcardW n w)
  have hgt_eq_lt : Sgt.card = Slt.card := by
    refine Finset.card_bij (fun w _ => swapW n w) ?_ ?_ ?_
    · intro w hw
      simp only [Sgt, Slt, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rwa [icardW_swap, jcardW_swap]
    · intro w₁ _ w₂ _ h
      exact (swapW n).injective h
    · intro w hw
      refine ⟨swapW n w, ?_, ?_⟩
      · simp only [Sgt, Slt, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rwa [icardW_swap, jcardW_swap]
      · rcases w with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl
  have huniv : (Finset.univ : Finset (W n)) = (Slt ∪ Sgt) ∪ Seq := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_union, Slt, Sgt, Seq, Finset.mem_filter, true_and,
      true_iff]
    omega
  have hdisj1 : Disjoint Slt Sgt := by
    refine Finset.disjoint_left.mpr ?_
    intro w h1 h2
    simp only [Slt, Sgt, Finset.mem_filter] at h1 h2
    omega
  have hdisj2 : Disjoint (Slt ∪ Sgt) Seq := by
    refine Finset.disjoint_left.mpr ?_
    intro w h1 h2
    simp only [Finset.mem_union, Slt, Sgt, Seq, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1 <;> omega
  have htot : Fintype.card (W n) = Slt.card + Sgt.card + Seq.card := by
    rw [← Finset.card_univ, huniv, Finset.card_union_of_disjoint hdisj2,
        Finset.card_union_of_disjoint hdisj1]
  rw [card_W, hgt_eq_lt] at htot
  dsimp only [Seq] at htot
  rw [card_diag_W] at htot
  rw [ncard_Sn_eq_card_Slt]
  dsimp only [Slt] at htot
  omega

end Aux_ZOE_lemma12

open ZeroOneExpansion Aux_ZOE_lemma12

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    0 < (Sn n).ncard ∧
    ((Sn n).ncard : ℤ) = 12 ^ n - ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℤ) ∧
    (Sn n).ncard < 12 ^ n ∧
    Nat.card (Grunbaum2003.PolytopeVertex (Pn n)) = 2 * 12 ^ n := by
  have hmain := sum_Sn_and_diag n
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ncard_Sn_eq_card_Slt, Finset.card_pos]
    let i0 : Fin n := ⟨0, by omega⟩
    let w0 : W n := Sum.inl (fun _ => 0, fun j => if j = i0 then 1 else 0)
    refine ⟨w0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have hI : suppFin (fun _ : Fin n => (0 : Fin 4)) = ∅ := by
      ext i; simp [suppFin]
    have hJ : suppFin (fun j : Fin n => if j = i0 then (1 : Fin 3) else 0) = {i0} := by
      ext j
      by_cases hj : j = i0 <;> simp [suppFin, hj]
    simp [w0, icardW, jcardW, hI, hJ]
  · have hcast : (((Sn n).ncard : ℤ) + ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℤ)) = 12 ^ n := by
      exact_mod_cast hmain
    linarith
  · have hA0 : 1 ≤ ∑ r ∈ Finset.range (n + 1), Acount n r r := by
      have hle := Finset.single_le_sum (f := fun r => Acount n r r)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos n))
      simpa [Acount] using hle
    omega
  · rw [← Nat.card_congr (wEquivVertex n), Nat.card_eq_fintype_card, card_W]
