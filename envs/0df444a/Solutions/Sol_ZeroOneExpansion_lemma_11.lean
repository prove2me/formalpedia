-- Prove2me | solution 1 for ZeroOneExpansion.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:02:17.527695+00:00
-- url     : https://prove2.me/submissions/351ad786-e05a-4cff-87ca-5c242971c8b4

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_crossGraph
import Definitions.Def_ZeroOneExpansion_IsAdj
import Theorems.Thm_ZeroOneExpansion_fact_3
import Theorems.Thm_ZeroOneExpansion_corollary_10

set_option autoImplicit false

namespace Aux_ZOE_lemma11

open ZeroOneExpansion Matrix

lemma isExposed_segment_iff_isAdj {m : ℕ} {P : Set (Fin m → ℝ)} (hP : Convex ℝ P)
    {x y : Fin m → ℝ} (hx : IsVertexOf P x) (hy : IsVertexOf P y) (hxy : x ≠ y) :
    IsExposed ℝ P (segment ℝ x y) ↔ IsAdj P x y := by
  constructor
  · intro hseg
    refine ⟨hxy, hx, hy, segment ℝ x y, hseg, ?_, left_mem_segment ℝ x y, right_mem_segment ℝ x y⟩
    rw [← convexHull_pair, affineSpan_convexHull, direction_affineSpan, vectorSpan_pair]
    exact finrank_span_singleton (vsub_ne_zero.mpr hxy)
  · rintro ⟨_, _, _, F, hFexp, hFdim, hxF, hyF⟩
    suffices hFeq : F = segment ℝ x y by rwa [← hFeq]
    apply Set.Subset.antisymm
    · intro z hzF
      have hspan_le : (ℝ ∙ (y -ᵥ x)) ≤ (affineSpan ℝ F).direction := by
        rw [Submodule.span_singleton_le_iff_mem, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ hyF hxF
      have hspan_dim : Module.finrank ℝ (ℝ ∙ (y -ᵥ x)) = 1 :=
        finrank_span_singleton (vsub_ne_zero.mpr hxy.symm)
      have hspan_eq : (ℝ ∙ (y -ᵥ x)) = (affineSpan ℝ F).direction :=
        Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hspan_dim, hFdim])
      have hzx_mem : z -ᵥ x ∈ (ℝ ∙ (y -ᵥ x)) := by
        rw [hspan_eq, direction_affineSpan]
        exact vsub_mem_vectorSpan ℝ hzF hxF
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hzx_mem
      have hz_eq : z = (1 - t) • x + t • y := by
        simp only [vsub_eq_sub] at ht
        ext k
        have htk := congr_fun ht k
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at htk ⊢
        linarith
      have hyP : y ∈ P := hFexp.subset hyF
      have hxP : x ∈ P := hFexp.subset hxF
      have hzP : z ∈ P := hFexp.subset hzF
      have ht_nonneg : 0 ≤ t := by
        by_contra ht_neg
        have ht_lt : t < 0 := lt_of_not_ge ht_neg
        obtain ⟨lx, hlx⟩ := hx (Set.singleton_nonempty x)
        have hx_max : x ∈ {w ∈ P | ∀ u ∈ P, lx u ≤ lx w} := hlx ▸ Set.mem_singleton x
        have hlz_le : lx z ≤ lx x := hx_max.2 z hzP
        have hly_lt : lx y < lx x := by
          rcases (hx_max.2 y hyP).lt_or_eq with hlt | heq
          · exact hlt
          · exfalso
            have hy_mem : y ∈ ({x} : Set (Fin m → ℝ)) := by
              rw [hlx]
              exact ⟨hyP, fun u hu => (hx_max.2 u hu).trans heq.symm.le⟩
            exact hxy.symm (Set.mem_singleton_iff.mp hy_mem)
        have hlz_val : lx z = (1 - t) * lx x + t * lx y := by
          rw [hz_eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        nlinarith
      have ht_le_one : t ≤ 1 := by
        by_contra ht_gt
        have ht_gt1 : 1 < t := lt_of_not_ge ht_gt
        obtain ⟨ly, hly⟩ := hy (Set.singleton_nonempty y)
        have hy_max : y ∈ {w ∈ P | ∀ u ∈ P, ly u ≤ ly w} := hly ▸ Set.mem_singleton y
        have hlz_le : ly z ≤ ly y := hy_max.2 z hzP
        have hlx_lt : ly x < ly y := by
          rcases (hy_max.2 x hxP).lt_or_eq with hlt | heq
          · exact hlt
          · exfalso
            have hx_mem : x ∈ ({y} : Set (Fin m → ℝ)) := by
              rw [hly]
              exact ⟨hxP, fun u hu => (hy_max.2 u hu).trans heq.symm.le⟩
            exact hxy (Set.mem_singleton_iff.mp hx_mem)
        have hlz_val : ly z = (1 - t) * ly x + t * ly y := by
          rw [hz_eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        nlinarith
      exact ⟨1 - t, t, by linarith, ht_nonneg, by ring, hz_eq.symm⟩
    · exact (hFexp.convex hP).segment_subset hxF hyF

lemma gn_adj_iff (n : ℕ) (u v : Grunbaum2003.PolytopeVertex (Pn n)) :
    (Gn n).Adj u v ↔ u ≠ v ∧ IsExposed ℝ (Pn n) (segment ℝ u.val v.val) := by
  have hconv : Convex ℝ (Pn n) := convex_convexHull ℝ _
  simp only [Gn, Grunbaum2003.polytopeGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hF | hF⟩
    · have huv_val : u.val ≠ v.val := fun h => hne (Subtype.ext h)
      have hadj : IsAdj (Pn n) u.val v.val := ⟨huv_val, u.2, v.2, hF⟩
      exact ⟨hne, (isExposed_segment_iff_isAdj hconv u.2 v.2 huv_val).mpr hadj⟩
    · rcases hF with ⟨F, hFexp, hFdim, hvF, huF⟩
      have huv_val : u.val ≠ v.val := fun h => hne (Subtype.ext h)
      have hadj : IsAdj (Pn n) u.val v.val := ⟨huv_val, u.2, v.2, F, hFexp, hFdim, huF, hvF⟩
      exact ⟨hne, (isExposed_segment_iff_isAdj hconv u.2 v.2 huv_val).mpr hadj⟩
  · rintro ⟨hne, hseg⟩
    have huv_val : u.val ≠ v.val := fun h => hne (Subtype.ext h)
    have hadj := (isExposed_segment_iff_isAdj hconv u.2 v.2 huv_val).mp hseg
    exact ⟨hne, Or.inl hadj.2.2.2⟩

lemma crossGraph_adj_iff (n : ℕ) (u v : Grunbaum2003.PolytopeVertex (Pn n)) :
    (crossGraph n).Adj u v ↔ (Gn n).Adj u v ∧ layer n u.val ≠ layer n v.val := by
  simp only [crossGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, ⟨hadj, hlay⟩ | ⟨hadj, hlay⟩⟩
    · exact ⟨hadj, hlay⟩
    · exact ⟨hadj.symm, hlay.symm⟩
  · rintro ⟨hadj, hlay⟩
    exact ⟨hadj.ne, Or.inl ⟨hadj, hlay⟩⟩

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
  have h0 := congr_fun h 0; have h1 := congr_fun h 1
  fin_cases a <;> fin_cases b <;> simp [cMap] at h0 h1 ⊢

lemma dMap_injective : Function.Injective dMap := by
  intro a b h
  have h0 := congr_fun h 0; have h1 := congr_fun h 1
  fin_cases a <;> fin_cases b <;> simp [dMap] at h0 h1 ⊢

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

lemma cMap_eq_zero_iff (a : Fin 4) : cMap a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 := congr_fun h 0; have h1 := congr_fun h 1
    fin_cases a <;> simp [cMap] at h0 h1 ⊢
  · rintro rfl; ext j; fin_cases j <;> rfl

lemma dMap_eq_zero_iff (a : Fin 3) : dMap a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 := congr_fun h 0; have h1 := congr_fun h 1
    fin_cases a <;> simp [dMap] at h0 h1 ⊢
  · rintro rfl; ext j; fin_cases j <;> rfl

lemma cMap_bit (a : Fin 4) (j : Fin 2) : cMap a j = 0 ∨ cMap a j = 1 := by
  fin_cases a <;> fin_cases j <;> simp [cMap]

lemma dMap_bit (a : Fin 3) (j : Fin 2) : dMap a j = 0 ∨ dMap a j = 1 := by
  fin_cases a <;> fin_cases j <;> simp [dMap]

def compatIdx (a : Fin 4) (b : Fin 3) : Prop := (cMap a, dMap b) ∈ compatR

lemma compatIdx_zero_iff {a : Fin 4} {b : Fin 3} (h : compatIdx a b) : a = 0 ↔ b = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [compatIdx, cMap, dMap, compatR, Matrix.vecCons_inj] at h ⊢

lemma compatIdx_zero_zero : compatIdx 0 0 := by
  simp [compatIdx, cMap, dMap, compatR]

lemma compatIdx_three_one : compatIdx 3 1 := by
  simp [compatIdx, cMap, dMap, compatR]

lemma compatIdx_three_of_ne_zero {b : Fin 3} (hb : b ≠ 0) : compatIdx 3 b := by
  fin_cases b
  · exact absurd rfl hb
  · simp [compatIdx, cMap, dMap, compatR]
  · simp [compatIdx, cMap, dMap, compatR]

def matchC : Fin 4 → Fin 3
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 1

lemma compatIdx_matchC (a : Fin 4) : compatIdx a (matchC a) := by
  fin_cases a <;> simp [matchC, compatIdx, cMap, dMap, compatR]

lemma matchC_eq_zero_iff (a : Fin 4) : matchC a = 0 ↔ a = 0 := by
  fin_cases a <;> simp [matchC]

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

def lowVec (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) : Fin (4 * n) → ℝ :=
  mkBlocks n (Sum.elim (fun i => cMap (fc i)) (fun j => dMap (fd j)))

def highVec (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) : Fin (4 * n) → ℝ :=
  mkBlocks n (Sum.elim (fun i => dMap (fd i)) (fun j => cMap (fc j)))

lemma lowVec_mem_Xn (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) :
    lowVec n fc fd ∈ Xn n := by
  intro i
  simp only [lowVec, blk_mkBlocks, Sum.elim_inl, Sum.elim_inr, ← range_cMap, ← range_dMap]
  exact ⟨⟨fc i, rfl⟩, ⟨fd i, rfl⟩⟩

lemma highVec_mem_Yn (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) :
    highVec n fd fc ∈ Yn n := by
  intro i
  simp only [highVec, blk_mkBlocks, Sum.elim_inl, Sum.elim_inr, ← range_cMap, ← range_dMap]
  exact ⟨⟨fd i, rfl⟩, ⟨fc i, rfl⟩⟩

def wToVec (n : ℕ) : W n → (Fin (4 * n + 1) → ℝ)
  | Sum.inl (fc, fd) => withLast (lowVec n fc fd) 0
  | Sum.inr (fd, fc) => withLast (highVec n fd fc) 1

lemma wToVec_injective (n : ℕ) : Function.Injective (wToVec n) := by
  intro w₁ w₂ h
  have hlast : wToVec n w₁ (Fin.last (4 * n)) = wToVec n w₂ (Fin.last (4 * n)) :=
    congr_fun h (Fin.last (4 * n))
  have hinit : Fin.init (wToVec n w₁) = Fin.init (wToVec n w₂) := by
    ext k; exact congr_fun h k.castSucc
  rcases w₁ with ⟨fc₁, fd₁⟩ | ⟨fd₁, fc₁⟩ <;> rcases w₂ with ⟨fc₂, fd₂⟩ | ⟨fd₂, fc₂⟩
  · simp only [wToVec, lowVec, withLast, Fin.init_snoc] at hinit
    congr 1; apply Prod.ext
    · funext i; apply cMap_injective
      simpa [blk_mkBlocks] using congr_arg (fun x => blk n x (Sum.inl i)) hinit
    · funext j; apply dMap_injective
      simpa [blk_mkBlocks] using congr_arg (fun x => blk n x (Sum.inr j)) hinit
  · simp [wToVec, withLast] at hlast
  · simp [wToVec, withLast] at hlast
  · simp only [wToVec, highVec, withLast, Fin.init_snoc] at hinit
    congr 1; apply Prod.ext
    · funext i; apply dMap_injective
      simpa [blk_mkBlocks] using congr_arg (fun x => blk n x (Sum.inl i)) hinit
    · funext j; apply cMap_injective
      simpa [blk_mkBlocks] using congr_arg (fun x => blk n x (Sum.inr j)) hinit

lemma range_wToVec (n : ℕ) : Set.range (wToVec n) = Vn n := by
  ext v
  simp only [Set.mem_range, Vn, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨⟨fc, fd⟩ | ⟨fd, fc⟩, rfl⟩
    · exact Or.inl ⟨lowVec n fc fd, lowVec_mem_Xn n fc fd, rfl⟩
    · exact Or.inr ⟨highVec n fd fc, highVec_mem_Yn n fd fc, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · have hxc : ∀ i, ∃ a, cMap a = blk n x (Sum.inl i) := fun i => by
        rw [← Set.mem_range, range_cMap]; exact (hx i).1
      have hxd : ∀ j, ∃ b, dMap b = blk n x (Sum.inr j) := fun j => by
        rw [← Set.mem_range, range_dMap]; exact (hx j).2
      choose fc hfc using hxc; choose fd hfd using hxd
      refine ⟨Sum.inl (fc, fd), ?_⟩
      simp only [wToVec, lowVec]; congr 1
      have hblk : Sum.elim (fun i => cMap (fc i)) (fun j => dMap (fd j)) = blk n x := by
        ext b j; rcases b with i | i <;> simp [hfc, hfd]
      rw [hblk, mkBlocks_blk]
    · have hyd : ∀ i, ∃ b, dMap b = blk n y (Sum.inl i) := fun i => by
        rw [← Set.mem_range, range_dMap]; exact (hy i).1
      have hyc : ∀ j, ∃ a, cMap a = blk n y (Sum.inr j) := fun j => by
        rw [← Set.mem_range, range_cMap]; exact (hy j).2
      choose fd hfd using hyd; choose fc hfc using hyc
      refine ⟨Sum.inr (fd, fc), ?_⟩
      simp only [wToVec, highVec]; congr 1
      have hblk : Sum.elim (fun i => dMap (fd i)) (fun j => cMap (fc j)) = blk n y := by
        ext b j; rcases b with i | i <;> simp [hfc, hfd]
      rw [hblk, mkBlocks_blk]

lemma wToVec_zeroOne (n : ℕ) (w : W n) (k : Fin (4 * n + 1)) :
    wToVec n w k = 0 ∨ wToVec n w k = 1 := by
  refine Fin.lastCases ?_ (fun m => ?_) k
  · rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩ <;> simp [wToVec, withLast]
  · rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩
    · simp only [wToVec, lowVec, withLast, Fin.snoc_castSucc, mkBlocks]
      rcases h : (unBlockIdx n m).1 with i | j
      · exact cMap_bit (fc i) _
      · exact dMap_bit (fd j) _
    · simp only [wToVec, highVec, withLast, Fin.snoc_castSucc, mkBlocks]
      rcases h : (unBlockIdx n m).1 with i | j
      · exact dMap_bit (fd i) _
      · exact cMap_bit (fc j) _

lemma vertices_Pn_eq_Vn (n : ℕ) :
    {v : Fin (4 * n + 1) → ℝ | IsExposed ℝ (Pn n) {v}} = Vn n := by
  classical
  let X : Finset (Fin (4 * n + 1) → ℝ) := Finset.univ.image (wToVec n)
  have hX_coe : (X : Set (Fin (4 * n + 1) → ℝ)) = Vn n := by
    simp [X, Finset.coe_image, range_wToVec]
  have hX_ne : X.Nonempty :=
    ⟨wToVec n (Sum.inl (fun _ => 0, fun _ => 0)), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hPn : Pn n = convexHull ℝ (X : Set (Fin (4 * n + 1) → ℝ)) := by
    rw [Pn, cayleySum, ← Vn, hX_coe]
  have h01 : ∀ v ∈ X, ∀ k, v k = 0 ∨ v k = 1 := by
    intro v hv k
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact wToVec_zeroOne n w k
  have hfact3 := ZeroOneExpansion.fact_3 X hX_ne h01
  rw [hPn]; simpa [IsVertexOf, hX_coe] using hfact3

noncomputable def wEquivVertex (n : ℕ) : W n ≃ Grunbaum2003.PolytopeVertex (Pn n) :=
  (Equiv.ofInjective (wToVec n) (wToVec_injective n)).trans
    (Equiv.setCongr (by rw [range_wToVec, ← vertices_Pn_eq_Vn]; rfl))

@[simp]
lemma wEquivVertex_val (n : ℕ) (w : W n) : (wEquivVertex n w).val = wToVec n w := rfl

lemma layer_wToVec_inl (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) :
    layer n (wToVec n (Sum.inl (fc, fd))) = 0 := by
  simp [layer, wToVec, withLast]

lemma layer_wToVec_inr (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) :
    layer n (wToVec n (Sum.inr (fd, fc))) = 1 := by
  simp [layer, wToVec, withLast]

def suppFin {n m : ℕ} (f : Fin n → Fin (m + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i ≠ 0

lemma iset_wToVec_inl (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) :
    Iset n (wToVec n (Sum.inl (fc, fd))) = suppFin fc := by
  ext i; simp [Iset, suppFin, ublk, wToVec, lowVec, withLast, Fin.init_snoc, blk_mkBlocks, cMap_eq_zero_iff]

lemma jset_wToVec_inl (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) :
    Jset n (wToVec n (Sum.inl (fc, fd))) = suppFin fd := by
  ext j; simp [Jset, suppFin, ublk, wToVec, lowVec, withLast, Fin.init_snoc, blk_mkBlocks, dMap_eq_zero_iff]

lemma iset_wToVec_inr (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) :
    Iset n (wToVec n (Sum.inr (fd, fc))) = suppFin fd := by
  ext i; simp [Iset, suppFin, ublk, wToVec, highVec, withLast, Fin.init_snoc, blk_mkBlocks, dMap_eq_zero_iff]

lemma jset_wToVec_inr (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) :
    Jset n (wToVec n (Sum.inr (fd, fc))) = suppFin fc := by
  ext j; simp [Jset, suppFin, ublk, wToVec, highVec, withLast, Fin.init_snoc, blk_mkBlocks, cMap_eq_zero_iff]

lemma crossAdj_low_high_iff (n : ℕ) (hn : 1 ≤ n)
    (fc : Fin n → Fin 4) (fd : Fin n → Fin 3)
    (fd' : Fin n → Fin 3) (fc' : Fin n → Fin 4) :
    (crossGraph n).Adj (wEquivVertex n (Sum.inl (fc, fd)))
        (wEquivVertex n (Sum.inr (fd', fc'))) ↔
      ∀ i : Fin n, compatIdx (fc i) (fd' i) ∧ compatIdx (fc' i) (fd i) := by
  rw [crossGraph_adj_iff, gn_adj_iff]
  have hlay : layer n (wToVec n (Sum.inl (fc, fd))) ≠ layer n (wToVec n (Sum.inr (fd', fc'))) := by
    rw [layer_wToVec_inl, layer_wToVec_inr]; norm_num
  have hne : wEquivVertex n (Sum.inl (fc, fd)) ≠ wEquivVertex n (Sum.inr (fd', fc')) :=
    fun h => hlay (congr_arg (layer n) (congr_arg Subtype.val h))
  rw [wEquivVertex_val, wEquivVertex_val, and_iff_left hlay, and_iff_right hne]
  change IsExposed ℝ (Pn n) (segment ℝ (withLast (lowVec n fc fd) 0) (withLast (highVec n fd' fc') 1)) ↔ _
  rw [ZeroOneExpansion.corollary_10 n hn (lowVec n fc fd) (highVec n fd' fc')
      (lowVec_mem_Xn n fc fd) (highVec_mem_Yn n fd' fc')]
  simp [lowVec, highVec, blk_mkBlocks, compatIdx]

lemma crossAdj_preserves_IJ (n : ℕ) (hn : 1 ≤ n)
    (u v : Grunbaum2003.PolytopeVertex (Pn n)) (hadj : (crossGraph n).Adj u v) :
    Iset n u.val = Iset n v.val ∧ Jset n u.val = Jset n v.val := by
  obtain ⟨w₁, rfl⟩ := (wEquivVertex n).surjective u
  obtain ⟨w₂, rfl⟩ := (wEquivVertex n).surjective v
  rcases w₁ with ⟨fc₁, fd₁⟩ | ⟨fd₁, fc₁⟩ <;> rcases w₂ with ⟨fc₂, fd₂⟩ | ⟨fd₂, fc₂⟩
  · have hlay := (crossGraph_adj_iff n _ _).mp hadj |>.2
    simp [layer_wToVec_inl] at hlay
  · have hc := (crossAdj_low_high_iff n hn fc₁ fd₁ fd₂ fc₂).mp hadj
    rw [wEquivVertex_val, wEquivVertex_val, iset_wToVec_inl, iset_wToVec_inr,
        jset_wToVec_inl, jset_wToVec_inr]
    constructor
    · ext i; simp [suppFin, (compatIdx_zero_iff (hc i).1)]
    · ext j; simp [suppFin, (compatIdx_zero_iff (hc j).2)]
  · have hc := (crossAdj_low_high_iff n hn fc₂ fd₂ fd₁ fc₁).mp hadj.symm
    rw [wEquivVertex_val, wEquivVertex_val, iset_wToVec_inr, iset_wToVec_inl,
        jset_wToVec_inr, jset_wToVec_inl]
    constructor
    · ext i; simp [suppFin, (compatIdx_zero_iff (hc i).1)]
    · ext j; simp [suppFin, (compatIdx_zero_iff (hc j).2)]
  · have hlay := (crossGraph_adj_iff n _ _).mp hadj |>.2
    simp [layer_wToVec_inr] at hlay

lemma walk_preserves_IJ (n : ℕ) (hn : 1 ≤ n)
    {u v : Grunbaum2003.PolytopeVertex (Pn n)} (p : (crossGraph n).Walk u v) :
    Iset n u.val = Iset n v.val ∧ Jset n u.val = Jset n v.val := by
  induction p with
  | nil => exact ⟨rfl, rfl⟩
  | cons hadj _ ih =>
    have hstep := crossAdj_preserves_IJ n hn _ _ hadj
    exact ⟨hstep.1.trans ih.1, hstep.2.trans ih.2⟩

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
  left_inv g := by ext ⟨i, hi⟩; simp [hi, Fin.pred_succ]
  right_inv f := by
    ext i; simp only
    by_cases hi : i ∈ K
    · simp [hi, Fin.succ_pred]
    · have h0 : f.1 i = 0 := by
        by_contra hne
        have hmem : i ∈ suppFin f.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
        rw [f.2] at hmem; exact hi hmem
      simp [hi, h0]

lemma card_suppFin_eq (n m : ℕ) (K : Finset (Fin n)) :
    (Finset.univ.filter (fun f : Fin n → Fin (m + 1) => suppFin f = K)).card = m ^ K.card := by
  have hcard : Fintype.card {f : Fin n → Fin (m + 1) // suppFin f = K} = m ^ K.card := by
    rw [← Fintype.card_congr (suppEquiv n m K)]
    simp [Fintype.card_fin]
  simpa [Fintype.card_subtype] using hcard

end Aux_ZOE_lemma11

open ZeroOneExpansion Aux_ZOE_lemma11

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ u v : Grunbaum2003.PolytopeVertex (Pn n), (crossGraph n).Adj u v →
        Iset n u.val = Iset n v.val ∧ Jset n u.val = Jset n v.val) ∧
    ∀ K L : Finset (Fin n),
      (∃ CC : (crossGraph n).ConnectedComponent,
          CC.supp = {u | Iset n u.val = K ∧ Jset n u.val = L}) ∧
      {u : Grunbaum2003.PolytopeVertex (Pn n) |
          Iset n u.val = K ∧ Jset n u.val = L ∧ layer n u.val = 0}.ncard =
        3 ^ K.card * 2 ^ L.card ∧
      {u : Grunbaum2003.PolytopeVertex (Pn n) |
          Iset n u.val = K ∧ Jset n u.val = L ∧ layer n u.val = 1}.ncard =
        2 ^ K.card * 3 ^ L.card := by
  refine ⟨crossAdj_preserves_IJ n hn, fun K L => ⟨?_, ?_, ?_⟩⟩
  · let fc₀ : Fin n → Fin 4 := fun i => if i ∈ K then 3 else 0
    let fd₀ : Fin n → Fin 3 := fun j => if j ∈ L then 1 else 0
    let fd₁ : Fin n → Fin 3 := fun i => if i ∈ K then 1 else 0
    let fc₁ : Fin n → Fin 4 := fun j => if j ∈ L then 3 else 0
    let u₀ := wEquivVertex n (Sum.inl (fc₀, fd₀))
    let v₀ := wEquivVertex n (Sum.inr (fd₁, fc₁))
    have hsupp_fc₀ : suppFin fc₀ = K := by
      ext i; by_cases hi : i ∈ K <;> simp [suppFin, fc₀, hi]
    have hsupp_fd₀ : suppFin fd₀ = L := by
      ext j; by_cases hj : j ∈ L <;> simp [suppFin, fd₀, hj]
    have hadj_hub : (crossGraph n).Adj u₀ v₀ := by
      rw [crossAdj_low_high_iff n hn]
      intro i
      constructor
      · by_cases hi : i ∈ K <;> simp [fc₀, fd₁, hi, compatIdx_three_one, compatIdx_zero_zero]
      · by_cases hi : i ∈ L <;> simp [fc₁, fd₀, hi, compatIdx_three_one, compatIdx_zero_zero]
    refine ⟨(crossGraph n).connectedComponentMk u₀, ?_⟩
    ext u
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    change (crossGraph n).connectedComponentMk u = (crossGraph n).connectedComponentMk u₀ ↔
      Iset n u.val = K ∧ Jset n u.val = L
    constructor
    · intro heq
      obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact heq
      have hp := walk_preserves_IJ n hn p
      rw [hp.1, hp.2]
      simp [u₀, iset_wToVec_inl, jset_wToVec_inl, hsupp_fc₀, hsupp_fd₀]
    · rintro ⟨hI, hJ⟩
      obtain ⟨w, rfl⟩ := (wEquivVertex n).surjective u
      rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩
      · rw [wEquivVertex_val, iset_wToVec_inl] at hI
        rw [wEquivVertex_val, jset_wToVec_inl] at hJ
        let v_mid := wEquivVertex n (Sum.inr (fun i => matchC (fc i), fc₁))
        have hadj1 : (crossGraph n).Adj (wEquivVertex n (Sum.inl (fc, fd))) v_mid := by
          rw [crossAdj_low_high_iff n hn]
          intro i
          refine ⟨compatIdx_matchC (fc i), ?_⟩
          by_cases hi : i ∈ L
          · have hne : fd i ≠ 0 := by
              have : i ∈ suppFin fd := hJ ▸ hi
              exact (Finset.mem_filter.mp this).2
            simpa [fc₁, hi] using compatIdx_three_of_ne_zero hne
          · have h0 : fd i = 0 := by
              by_contra hne
              exact hi (hJ ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
            simp [fc₁, hi, h0, compatIdx_zero_zero]
        have hadj2 : (crossGraph n).Adj u₀ v_mid := by
          rw [crossAdj_low_high_iff n hn]
          intro i
          refine ⟨?_, ?_⟩
          · by_cases hi : i ∈ K
            · have hfc_ne : fc i ≠ 0 := by
                have : i ∈ suppFin fc := hI ▸ hi
                exact (Finset.mem_filter.mp this).2
              have hm_ne : matchC (fc i) ≠ 0 := fun hm0 => hfc_ne ((matchC_eq_zero_iff (fc i)).mp hm0)
              simpa [fc₀, hi] using compatIdx_three_of_ne_zero hm_ne
            · have hfc0 : fc i = 0 := by
                by_contra hne
                exact hi (hI ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
              simp [fc₀, hi, hfc0, matchC, compatIdx_zero_zero]
          · by_cases hi : i ∈ L <;> simp [fc₁, fd₀, hi, compatIdx_three_one, compatIdx_zero_zero]
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj1).trans
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj2.symm)
      · rw [wEquivVertex_val, iset_wToVec_inr] at hI
        rw [wEquivVertex_val, jset_wToVec_inr] at hJ
        let u_mid := wEquivVertex n (Sum.inl (fc₀, fun j => matchC (fc j)))
        have hadj1 : (crossGraph n).Adj u_mid (wEquivVertex n (Sum.inr (fd, fc))) := by
          rw [crossAdj_low_high_iff n hn]
          intro i
          refine ⟨?_, compatIdx_matchC (fc i)⟩
          by_cases hi : i ∈ K
          · have hne : fd i ≠ 0 := by
              have : i ∈ suppFin fd := hI ▸ hi
              exact (Finset.mem_filter.mp this).2
            simpa [fc₀, hi] using compatIdx_three_of_ne_zero hne
          · have h0 : fd i = 0 := by
              by_contra hne
              exact hi (hI ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
            simp [fc₀, hi, h0, compatIdx_zero_zero]
        have hadj2 : (crossGraph n).Adj u_mid v₀ := by
          rw [crossAdj_low_high_iff n hn]
          intro i
          refine ⟨?_, ?_⟩
          · by_cases hi : i ∈ K <;> simp [fc₀, fd₁, hi, compatIdx_three_one, compatIdx_zero_zero]
          · by_cases hi : i ∈ L
            · have hfc_ne : fc i ≠ 0 := by
                have : i ∈ suppFin fc := hJ ▸ hi
                exact (Finset.mem_filter.mp this).2
              have hm_ne : matchC (fc i) ≠ 0 := fun hm0 => hfc_ne ((matchC_eq_zero_iff (fc i)).mp hm0)
              simpa [fc₁, hi] using compatIdx_three_of_ne_zero hm_ne
            · have hfc0 : fc i = 0 := by
                by_contra hne
                exact hi (hJ ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
              simp [fc₁, hi, hfc0, matchC, compatIdx_zero_zero]
        exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj1.symm).trans
          ((SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj2).trans
            (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj_hub.symm))
  · let Flow : Finset (W n) :=
      ((Finset.univ.filter fun fc : Fin n → Fin 4 => suppFin fc = K) ×ˢ
        (Finset.univ.filter fun fd : Fin n → Fin 3 => suppFin fd = L)).map
        ⟨Sum.inl, Sum.inl_injective⟩
    have hset : {u : Grunbaum2003.PolytopeVertex (Pn n) |
        Iset n u.val = K ∧ Jset n u.val = L ∧ layer n u.val = 0} =
        (wEquivVertex n) '' (Flow : Set (W n)) := by
      ext u
      simp only [Set.mem_image, Finset.mem_coe]
      change (Iset n u.val = K ∧ Jset n u.val = L ∧ layer n u.val = 0) ↔ _
      constructor
      · rintro ⟨hI, hJ, hlay⟩
        obtain ⟨w, rfl⟩ := (wEquivVertex n).surjective u
        rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩
        · rw [wEquivVertex_val, iset_wToVec_inl] at hI
          rw [wEquivVertex_val, jset_wToVec_inl] at hJ
          refine ⟨Sum.inl (fc, fd), ?_, rfl⟩
          simp [Flow, hI, hJ]
        · rw [wEquivVertex_val, layer_wToVec_inr] at hlay
          norm_num at hlay
      · rintro ⟨w, hw, rfl⟩
        rcases Finset.mem_map.mp hw with ⟨⟨fc, fd⟩, hp, rfl⟩
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        change Iset n (wToVec n (Sum.inl (fc, fd))) = K ∧
          Jset n (wToVec n (Sum.inl (fc, fd))) = L ∧
          layer n (wToVec n (Sum.inl (fc, fd))) = 0
        rw [iset_wToVec_inl, jset_wToVec_inl, layer_wToVec_inl]
        exact ⟨hp.1, hp.2, rfl⟩
    rw [hset, Set.ncard_image_of_injective _ (wEquivVertex n).injective, Set.ncard_coe_finset]
    simp only [Flow, Finset.card_map, Finset.card_product, card_suppFin_eq]
  · let Fhigh : Finset (W n) :=
      ((Finset.univ.filter fun fd : Fin n → Fin 3 => suppFin fd = K) ×ˢ
        (Finset.univ.filter fun fc : Fin n → Fin 4 => suppFin fc = L)).map
        ⟨Sum.inr, Sum.inr_injective⟩
    have hset : {u : Grunbaum2003.PolytopeVertex (Pn n) |
        Iset n u.val = K ∧ Jset n u.val = L ∧ layer n u.val = 1} =
        (wEquivVertex n) '' (Fhigh : Set (W n)) := by
      ext u
      simp only [Set.mem_image, Finset.mem_coe]
      change (Iset n u.val = K ∧ Jset n u.val = L ∧ layer n u.val = 1) ↔ _
      constructor
      · rintro ⟨hI, hJ, hlay⟩
        obtain ⟨w, rfl⟩ := (wEquivVertex n).surjective u
        rcases w with ⟨fc, fd⟩ | ⟨fd, fc⟩
        · rw [wEquivVertex_val, layer_wToVec_inl] at hlay
          norm_num at hlay
        · rw [wEquivVertex_val, iset_wToVec_inr] at hI
          rw [wEquivVertex_val, jset_wToVec_inr] at hJ
          refine ⟨Sum.inr (fd, fc), ?_, rfl⟩
          simp [Fhigh, hI, hJ]
      · rintro ⟨w, hw, rfl⟩
        rcases Finset.mem_map.mp hw with ⟨⟨fd, fc⟩, hp, rfl⟩
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        change Iset n (wToVec n (Sum.inr (fd, fc))) = K ∧
          Jset n (wToVec n (Sum.inr (fd, fc))) = L ∧
          layer n (wToVec n (Sum.inr (fd, fc))) = 1
        rw [iset_wToVec_inr, jset_wToVec_inr, layer_wToVec_inr]
        exact ⟨hp.1, hp.2, rfl⟩
    rw [hset, Set.ncard_image_of_injective _ (wEquivVertex n).injective, Set.ncard_coe_finset]
    simp only [Fhigh, Finset.card_map, Finset.card_product, card_suppFin_eq]
