-- Prove2me | solution 1 for ZeroOneExpansion.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:10:18.252549+00:00
-- url     : https://prove2.me/submissions/b017a068-60bf-463f-bfa3-ba3452cf40b2

import Mathlib
import Definitions.Def_Grunbaum2003_polytopeGraph
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_ZeroOneExpansion_IsZeroOnePolytope
import Definitions.Def_ZeroOneExpansion_polyDim
import Definitions.Def_ZeroOneExpansion_edgeExpansion
import Definitions.Def_ZeroOneExpansion_Pn
import Theorems.Thm_ZeroOneExpansion_lemma_7
import Theorems.Thm_ZeroOneExpansion_theorem_14

set_option autoImplicit false

namespace Aux_ZOE_thm1

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
  ext j; simp [blk, mkBlocks, unBlockIdx_blockIdx]

lemma mkBlocks_blk (n : ℕ) (x : Fin (4 * n) → ℝ) :
    mkBlocks n (blk n x) = x := by
  ext k; simp [mkBlocks, blk, blockIdx_unBlockIdx]

abbrev W (n : ℕ) :=
  ((Fin n → Fin 4) × (Fin n → Fin 3)) ⊕ ((Fin n → Fin 3) × (Fin n → Fin 4))

def wToVec (n : ℕ) : W n → (Fin (4 * n + 1) → ℝ)
  | Sum.inl (fc, fd) =>
      withLast (mkBlocks n (Sum.elim (fun i => cMap (fc i)) (fun j => dMap (fd j)))) 0
  | Sum.inr (fd, fc) =>
      withLast (mkBlocks n (Sum.elim (fun i => dMap (fd i)) (fun j => cMap (fc j)))) 1

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
      choose fc hfc using hxc; choose fd hfd using hxd
      refine ⟨Sum.inl (fc, fd), ?_⟩
      simp only [wToVec]; congr 1
      have hblk : Sum.elim (fun i => cMap (fc i)) (fun j => dMap (fd j)) = blk n x := by
        ext b j; rcases b with i | i <;> simp [hfc, hfd]
      rw [hblk, mkBlocks_blk]
    · have hyd : ∀ i, ∃ b, dMap b = blk n y (Sum.inl i) := fun i => by
        rw [← Set.mem_range, range_dMap]; exact (hy i).1
      have hyc : ∀ j, ∃ a, cMap a = blk n y (Sum.inr j) := fun j => by
        rw [← Set.mem_range, range_cMap]; exact (hy j).2
      choose fd hfd using hyd; choose fc hfc using hyc
      refine ⟨Sum.inr (fd, fc), ?_⟩
      simp only [wToVec]; congr 1
      have hblk : Sum.elim (fun i => dMap (fd i)) (fun j => cMap (fc j)) = blk n y := by
        ext b j; rcases b with i | i <;> simp [hfc, hfd]
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

lemma isZeroOne_and_isDPolytope_Pn (n : ℕ) (hn : 1 ≤ n) :
    IsZeroOnePolytope (Pn n) ∧ Grunbaum2003.IsDPolytope (Pn n) := by
  classical
  let X : Finset (Fin (4 * n + 1) → ℝ) := Finset.univ.image (wToVec n)
  have hX_coe : (X : Set (Fin (4 * n + 1) → ℝ)) = Vn n := by
    simp [X, Finset.coe_image, range_wToVec]
  let x₀ := wToVec n (Sum.inl (fun _ => 0, fun _ => 0))
  have hx₀X : x₀ ∈ X := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hX_ne : X.Nonempty := ⟨x₀, hx₀X⟩
  have hPn : Pn n = convexHull ℝ (X : Set (Fin (4 * n + 1) → ℝ)) := by
    rw [Pn, cayleySum, ← Vn, hX_coe]
  have h01 : ∀ v ∈ X, ∀ k, v k = 0 ∨ v k = 1 := by
    intro v hv k
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact wToVec_zeroOne n w k
  refine ⟨⟨X, hX_ne, h01, hPn⟩, ⟨(X : Set _), X.finite_toSet, ⟨x₀, hx₀X⟩, hPn⟩, ?_⟩
  have hdim : Module.finrank ℝ (affineSpan ℝ (Pn n)).direction = 4 * n + 1 :=
    ZeroOneExpansion.lemma_7 n hn
  have htop_dim : Module.finrank ℝ (⊤ : Submodule ℝ (Fin (4 * n + 1) → ℝ)) = 4 * n + 1 := by
    rw [finrank_top, Module.finrank_fin_fun]
  have hdir_top : (affineSpan ℝ (Pn n)).direction = ⊤ :=
    Submodule.eq_of_le_of_finrank_eq le_top (by rw [hdim, htop_dim])
  have hx₀P : x₀ ∈ Pn n := by
    rw [hPn]
    exact subset_convexHull ℝ _ hx₀X
  have hx₀_aff : x₀ ∈ affineSpan ℝ (Pn n) := subset_affineSpan ℝ _ hx₀P
  ext p
  simp only [AffineSubspace.mem_top, iff_true]
  have hv : p -ᵥ x₀ ∈ (affineSpan ℝ (Pn n)).direction := by
    rw [hdir_top]; trivial
  simpa using AffineSubspace.vadd_mem_of_mem_direction hv hx₀_aff

end Aux_ZOE_thm1

open ZeroOneExpansion Aux_ZOE_thm1

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ (d : ℕ → ℕ) (P : (n : ℕ) → Set (Fin (d n) → ℝ)),
      (∀ n, 1 ≤ n → IsZeroOnePolytope (P n) ∧ Grunbaum2003.IsDPolytope (P n)) ∧
      Filter.Tendsto (fun n => polyDim (P n)) Filter.atTop Filter.atTop ∧
      (∀ᶠ n in Filter.atTop, edgeExpansion (Grunbaum2003.polytopeGraph (P n)) ≤
        ((Real.exp (-c * (polyDim (P n) : ℝ)) : ℝ) : EReal)) ∧
      (∀ᶠ n in Filter.atTop, edgeExpansion (Grunbaum2003.polytopeGraph (P n)) < 1) := by
  obtain ⟨_, _, hlt1, ⟨c, hc_pos, hexp⟩⟩ := ZeroOneExpansion.theorem_14
  refine ⟨c, hc_pos, fun n => 4 * n + 1, Pn, isZeroOne_and_isDPolytope_Pn, ?_, hexp, hlt1⟩
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨max b 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right b 1) hn
  have hb : b ≤ n := le_trans (le_max_left b 1) hn
  rw [ZeroOneExpansion.lemma_7 n hn1]
  omega
