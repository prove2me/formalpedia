-- Prove2me | solution 1 for ZeroOneExpansion.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:04:50.292219+00:00
-- url     : https://prove2.me/submissions/189592fc-517e-41c9-996d-f64841c7061c

import Mathlib
import Definitions.Def_ZeroOneExpansion_Sn
import Definitions.Def_ZeroOneExpansion_edgeExpansion
import Definitions.Def_ZeroOneExpansion_IsAdj
import Definitions.Def_ZeroOneExpansion_compatR
import Theorems.Thm_ZeroOneExpansion_fact_3
import Theorems.Thm_ZeroOneExpansion_lemma_8
import Theorems.Thm_ZeroOneExpansion_corollary_10

set_option autoImplicit false

namespace Aux_ZOE_lemma13

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

lemma isAdj_symm {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {P : Set E} {x y : E} : IsAdj P x y ↔ IsAdj P y x := by
  constructor <;> rintro ⟨hne, hx, hy, F, hF, hdim, hxF, hyF⟩ <;>
    exact ⟨hne.symm, hy, hx, F, hF, hdim, hyF, hxF⟩

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

lemma cMap_mem_Qsq (a : Fin 4) : cMap a ∈ Qsq :=
  subset_convexHull ℝ C (by rw [← range_cMap]; exact ⟨a, rfl⟩)

lemma dMap_mem_Delta (b : Fin 3) : dMap b ∈ Delta :=
  subset_convexHull ℝ D (by rw [← range_dMap]; exact ⟨b, rfl⟩)

lemma isVertex_cMap (a : Fin 4) : IsVertexOf Qsq (cMap a) := by
  classical
  let XC : Finset (Fin 2 → ℝ) := Finset.univ.image cMap
  have hXC : (XC : Set (Fin 2 → ℝ)) = C := by simp [XC, Finset.coe_image, range_cMap]
  have hne : XC.Nonempty := ⟨cMap 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have h01 : ∀ v ∈ XC, ∀ k, v k = 0 ∨ v k = 1 := by
    intro v hv k; obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv; exact cMap_bit b k
  have hf3 := ZeroOneExpansion.fact_3 XC hne h01
  have hQ : Qsq = convexHull ℝ (XC : Set (Fin 2 → ℝ)) := by rw [Qsq, hXC]
  have hmem : cMap a ∈ {v : Fin 2 → ℝ | IsVertexOf (convexHull ℝ (XC : Set (Fin 2 → ℝ))) v} := by
    rw [hf3, hXC, ← range_cMap]; exact ⟨a, rfl⟩
  rwa [← hQ] at hmem

lemma isVertex_dMap (b : Fin 3) : IsVertexOf Delta (dMap b) := by
  classical
  let XD : Finset (Fin 2 → ℝ) := Finset.univ.image dMap
  have hXD : (XD : Set (Fin 2 → ℝ)) = D := by simp [XD, Finset.coe_image, range_dMap]
  have hne : XD.Nonempty := ⟨dMap 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have h01 : ∀ v ∈ XD, ∀ k, v k = 0 ∨ v k = 1 := by
    intro v hv k; obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hv; exact dMap_bit c k
  have hf3 := ZeroOneExpansion.fact_3 XD hne h01
  have hD : Delta = convexHull ℝ (XD : Set (Fin 2 → ℝ)) := by rw [Delta, hXD]
  have hmem : dMap b ∈ {v : Fin 2 → ℝ | IsVertexOf (convexHull ℝ (XD : Set (Fin 2 → ℝ))) v} := by
    rw [hf3, hXD, ← range_dMap]; exact ⟨b, rfl⟩
  rwa [← hD] at hmem

def lin2 (α β : ℝ) : StrongDual ℝ (Fin 2 → ℝ) :=
  α • ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2) +
  β • ContinuousLinearMap.proj (R := ℝ) (1 : Fin 2)

@[simp]
lemma lin2_apply (α β : ℝ) (z : Fin 2 → ℝ) : lin2 α β z = α * z 0 + β * z 1 := by
  simp [lin2]

lemma mem_Qsq_bounds {z : Fin 2 → ℝ} (hz : z ∈ Qsq) :
    0 ≤ z 0 ∧ z 0 ≤ 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
  let S : Set (Fin 2 → ℝ) := {w | 0 ≤ w 0 ∧ w 0 ≤ 1 ∧ 0 ≤ w 1 ∧ w 1 ≤ 1}
  have hCS : C ⊆ S := by
    rintro w (rfl | rfl | rfl | rfl) <;> simp [S]
  have hSconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    simp only [S, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  exact convexHull_min hCS hSconv hz

lemma mem_Delta_bounds {z : Fin 2 → ℝ} (hz : z ∈ Delta) :
    0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 0 + z 1 ≤ 1 := by
  let S : Set (Fin 2 → ℝ) := {w | 0 ≤ w 0 ∧ 0 ≤ w 1 ∧ w 0 + w 1 ≤ 1}
  have hDS : D ⊆ S := by
    rintro w (rfl | rfl | rfl) <;> simp [S]
  have hSconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    simp only [S, Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  exact convexHull_min hDS hSconv hz

lemma isAdj_Delta_01 : IsAdj Delta (dMap 0) (dMap 1) := by
  have hconvD : Convex ℝ Delta := convex_convexHull ℝ D
  have hne : dMap 0 ≠ dMap 1 := fun h => absurd (dMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvD (isVertex_dMap 0) (isVertex_dMap 1) hne]
  intro _
  refine ⟨lin2 0 (-1), Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hconvD.segment_subset (dMap_mem_Delta 0) (dMap_mem_Delta 1) hz, ?_⟩
    rcases hz with ⟨a, b, _, _, _, rfl⟩
    intro y hy
    have hyb := mem_Delta_bounds hy
    simp [lin2_apply, dMap]
    linarith [hyb.2.1]
  · rintro z ⟨hzD, hmax⟩
    have hbnd := mem_Delta_bounds hzD
    have h0 := hmax (dMap 0) (dMap_mem_Delta 0)
    simp [lin2_apply, dMap] at h0
    have hz1 : z 1 = 0 := by linarith [hbnd.2.1]
    refine ⟨1 - z 0, z 0, by linarith [hbnd.2.2, hbnd.2.1], hbnd.1, by ring, ?_⟩
    ext k; fin_cases k <;> simp [dMap, hz1]

lemma isAdj_Delta_02 : IsAdj Delta (dMap 0) (dMap 2) := by
  have hconvD : Convex ℝ Delta := convex_convexHull ℝ D
  have hne : dMap 0 ≠ dMap 2 := fun h => absurd (dMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvD (isVertex_dMap 0) (isVertex_dMap 2) hne]
  intro _
  refine ⟨lin2 (-1) 0, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hconvD.segment_subset (dMap_mem_Delta 0) (dMap_mem_Delta 2) hz, ?_⟩
    rcases hz with ⟨a, b, _, _, _, rfl⟩
    intro y hy
    have hyb := mem_Delta_bounds hy
    simp [lin2_apply, dMap]
    linarith [hyb.1]
  · rintro z ⟨hzD, hmax⟩
    have hbnd := mem_Delta_bounds hzD
    have h0 := hmax (dMap 0) (dMap_mem_Delta 0)
    simp [lin2_apply, dMap] at h0
    have hz0 : z 0 = 0 := by linarith [hbnd.1]
    refine ⟨1 - z 1, z 1, by linarith [hbnd.2.2, hbnd.1], hbnd.2.1, by ring, ?_⟩
    ext k; fin_cases k <;> simp [dMap, hz0]

lemma isAdj_Delta_12 : IsAdj Delta (dMap 1) (dMap 2) := by
  have hconvD : Convex ℝ Delta := convex_convexHull ℝ D
  have hne : dMap 1 ≠ dMap 2 := fun h => absurd (dMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvD (isVertex_dMap 1) (isVertex_dMap 2) hne]
  intro _
  refine ⟨lin2 1 1, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hconvD.segment_subset (dMap_mem_Delta 1) (dMap_mem_Delta 2) hz, ?_⟩
    rcases hz with ⟨a, b, _, _, hab, rfl⟩
    intro y hy
    have hyb := mem_Delta_bounds hy
    simp [lin2_apply, dMap]
    linarith [hyb.2.2]
  · rintro z ⟨hzD, hmax⟩
    have hbnd := mem_Delta_bounds hzD
    have h1 := hmax (dMap 1) (dMap_mem_Delta 1)
    simp [lin2_apply, dMap] at h1
    have hsum : z 0 + z 1 = 1 := by linarith [hbnd.2.2]
    refine ⟨z 0, z 1, hbnd.1, hbnd.2.1, hsum, ?_⟩
    ext k; fin_cases k <;> simp [dMap]

lemma isAdj_Delta_iff (b₁ b₂ : Fin 3) : IsAdj Delta (dMap b₁) (dMap b₂) ↔ b₁ ≠ b₂ := by
  fin_cases b₁ <;> fin_cases b₂
  · exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_Delta_01⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_Delta_02⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_symm.mp isAdj_Delta_01⟩
  · exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_Delta_12⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_symm.mp isAdj_Delta_02⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_symm.mp isAdj_Delta_12⟩
  · exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h⟩

def adjC (a₁ a₂ : Fin 4) : Prop := a₁ ≠ a₂ ∧ a₁.val + a₂.val ≠ 3

instance instDecidableAdjC (a₁ a₂ : Fin 4) : Decidable (adjC a₁ a₂) :=
  inferInstanceAs (Decidable (a₁ ≠ a₂ ∧ a₁.val + a₂.val ≠ 3))

lemma isAdj_Qsq_01 : IsAdj Qsq (cMap 0) (cMap 1) := by
  have hconvQ : Convex ℝ Qsq := convex_convexHull ℝ C
  have hne : cMap 0 ≠ cMap 1 := fun h => absurd (cMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvQ (isVertex_cMap 0) (isVertex_cMap 1) hne]
  intro _
  refine ⟨lin2 (-1) 0, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hconvQ.segment_subset (cMap_mem_Qsq 0) (cMap_mem_Qsq 1) hz, ?_⟩
    rcases hz with ⟨a, b, _, _, _, rfl⟩
    intro y hy
    have hyb := mem_Qsq_bounds hy
    simp [lin2_apply, cMap]
    linarith [hyb.1]
  · rintro z ⟨hzQ, hmax⟩
    have hbnd := mem_Qsq_bounds hzQ
    have h0 := hmax (cMap 0) (cMap_mem_Qsq 0)
    simp [lin2_apply, cMap] at h0
    have hz0 : z 0 = 0 := by linarith [hbnd.1]
    refine ⟨1 - z 1, z 1, by linarith [hbnd.2.2.2], hbnd.2.2.1, by ring, ?_⟩
    ext k; fin_cases k <;> simp [cMap, hz0]

lemma isAdj_Qsq_02 : IsAdj Qsq (cMap 0) (cMap 2) := by
  have hconvQ : Convex ℝ Qsq := convex_convexHull ℝ C
  have hne : cMap 0 ≠ cMap 2 := fun h => absurd (cMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvQ (isVertex_cMap 0) (isVertex_cMap 2) hne]
  intro _
  refine ⟨lin2 0 (-1), Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hconvQ.segment_subset (cMap_mem_Qsq 0) (cMap_mem_Qsq 2) hz, ?_⟩
    rcases hz with ⟨a, b, _, _, _, rfl⟩
    intro y hy
    have hyb := mem_Qsq_bounds hy
    simp [lin2_apply, cMap]
    linarith [hyb.2.2.1]
  · rintro z ⟨hzQ, hmax⟩
    have hbnd := mem_Qsq_bounds hzQ
    have h0 := hmax (cMap 0) (cMap_mem_Qsq 0)
    simp [lin2_apply, cMap] at h0
    have hz1 : z 1 = 0 := by linarith [hbnd.2.2.1]
    refine ⟨1 - z 0, z 0, by linarith [hbnd.2.1], hbnd.1, by ring, ?_⟩
    ext k; fin_cases k <;> simp [cMap, hz1]

lemma isAdj_Qsq_13 : IsAdj Qsq (cMap 1) (cMap 3) := by
  have hconvQ : Convex ℝ Qsq := convex_convexHull ℝ C
  have hne : cMap 1 ≠ cMap 3 := fun h => absurd (cMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvQ (isVertex_cMap 1) (isVertex_cMap 3) hne]
  intro _
  refine ⟨lin2 0 1, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hconvQ.segment_subset (cMap_mem_Qsq 1) (cMap_mem_Qsq 3) hz, ?_⟩
    rcases hz with ⟨a, b, _, _, hab, rfl⟩
    intro y hy
    have hyb := mem_Qsq_bounds hy
    simp [lin2_apply, cMap]
    linarith [hyb.2.2.2]
  · rintro z ⟨hzQ, hmax⟩
    have hbnd := mem_Qsq_bounds hzQ
    have h1 := hmax (cMap 1) (cMap_mem_Qsq 1)
    simp [lin2_apply, cMap] at h1
    have hz1 : z 1 = 1 := by linarith [hbnd.2.2.2]
    refine ⟨1 - z 0, z 0, by linarith [hbnd.2.1], hbnd.1, by ring, ?_⟩
    ext k; fin_cases k <;> simp [cMap, hz1] <;> ring

lemma isAdj_Qsq_23 : IsAdj Qsq (cMap 2) (cMap 3) := by
  have hconvQ : Convex ℝ Qsq := convex_convexHull ℝ C
  have hne : cMap 2 ≠ cMap 3 := fun h => absurd (cMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvQ (isVertex_cMap 2) (isVertex_cMap 3) hne]
  intro _
  refine ⟨lin2 1 0, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hconvQ.segment_subset (cMap_mem_Qsq 2) (cMap_mem_Qsq 3) hz, ?_⟩
    rcases hz with ⟨a, b, _, _, hab, rfl⟩
    intro y hy
    have hyb := mem_Qsq_bounds hy
    simp [lin2_apply, cMap]
    linarith [hyb.2.1]
  · rintro z ⟨hzQ, hmax⟩
    have hbnd := mem_Qsq_bounds hzQ
    have h2 := hmax (cMap 2) (cMap_mem_Qsq 2)
    simp [lin2_apply, cMap] at h2
    have hz0 : z 0 = 1 := by linarith [hbnd.2.1]
    refine ⟨1 - z 1, z 1, by linarith [hbnd.2.2.2], hbnd.2.2.1, by ring, ?_⟩
    ext k; fin_cases k <;> simp [cMap, hz0] <;> ring

lemma not_isAdj_Qsq_03 : ¬ IsAdj Qsq (cMap 0) (cMap 3) := by
  have hconvQ : Convex ℝ Qsq := convex_convexHull ℝ C
  have hne : cMap 0 ≠ cMap 3 := fun h => absurd (cMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvQ (isVertex_cMap 0) (isVertex_cMap 3) hne]
  intro hseg
  obtain ⟨l, hl⟩ := hseg ⟨cMap 0, left_mem_segment ℝ _ _⟩
  have hm0 : cMap 0 ∈ {x ∈ Qsq | ∀ y ∈ Qsq, l y ≤ l x} := hl ▸ left_mem_segment ℝ (cMap 0) (cMap 3)
  have hm3 : cMap 3 ∈ {x ∈ Qsq | ∀ y ∈ Qsq, l y ≤ l x} := hl ▸ right_mem_segment ℝ (cMap 0) (cMap 3)
  have h1le0 : l (cMap 1) ≤ l (cMap 0) := hm0.2 (cMap 1) (cMap_mem_Qsq 1)
  have h2le3 : l (cMap 2) ≤ l (cMap 3) := hm3.2 (cMap 2) (cMap_mem_Qsq 2)
  have hvec : cMap 0 + cMap 3 = cMap 1 + cMap 2 := by ext k; fin_cases k <;> simp [cMap]
  have hlin : l (cMap 0) + l (cMap 3) = l (cMap 1) + l (cMap 2) := by
    simpa [map_add] using congr_arg l hvec
  have hl1 : l (cMap 1) = l (cMap 0) := by linarith
  have hc1_mem : cMap 1 ∈ segment ℝ (cMap 0) (cMap 3) := by
    rw [hl]
    exact ⟨cMap_mem_Qsq 1, fun y hy => (hm0.2 y hy).trans hl1.symm.le⟩
  rcases hc1_mem with ⟨a, b, _, _, _, hab_eq⟩
  have h0 := congr_fun hab_eq 0
  have h1 := congr_fun hab_eq 1
  simp [cMap] at h0 h1
  linarith

lemma not_isAdj_Qsq_12 : ¬ IsAdj Qsq (cMap 1) (cMap 2) := by
  have hconvQ : Convex ℝ Qsq := convex_convexHull ℝ C
  have hne : cMap 1 ≠ cMap 2 := fun h => absurd (cMap_injective h) (by decide)
  rw [← isExposed_segment_iff_isAdj hconvQ (isVertex_cMap 1) (isVertex_cMap 2) hne]
  intro hseg
  obtain ⟨l, hl⟩ := hseg ⟨cMap 1, left_mem_segment ℝ _ _⟩
  have hm1 : cMap 1 ∈ {x ∈ Qsq | ∀ y ∈ Qsq, l y ≤ l x} := hl ▸ left_mem_segment ℝ (cMap 1) (cMap 2)
  have hm2 : cMap 2 ∈ {x ∈ Qsq | ∀ y ∈ Qsq, l y ≤ l x} := hl ▸ right_mem_segment ℝ (cMap 1) (cMap 2)
  have h0le1 : l (cMap 0) ≤ l (cMap 1) := hm1.2 (cMap 0) (cMap_mem_Qsq 0)
  have h3le2 : l (cMap 3) ≤ l (cMap 2) := hm2.2 (cMap 3) (cMap_mem_Qsq 3)
  have hvec : cMap 1 + cMap 2 = cMap 0 + cMap 3 := by ext k; fin_cases k <;> simp [cMap]
  have hlin : l (cMap 1) + l (cMap 2) = l (cMap 0) + l (cMap 3) := by
    simpa [map_add] using congr_arg l hvec
  have hl0 : l (cMap 0) = l (cMap 1) := by linarith
  have hc0_mem : cMap 0 ∈ segment ℝ (cMap 1) (cMap 2) := by
    rw [hl]
    exact ⟨cMap_mem_Qsq 0, fun y hy => (hm1.2 y hy).trans hl0.symm.le⟩
  rcases hc0_mem with ⟨a, b, _, _, hab1, hab_eq⟩
  have h0 := congr_fun hab_eq 0
  have h1 := congr_fun hab_eq 1
  simp [cMap] at h0 h1
  linarith

lemma isAdj_Qsq_iff (a₁ a₂ : Fin 4) : IsAdj Qsq (cMap a₁) (cMap a₂) ↔ adjC a₁ a₂ := by
  fin_cases a₁ <;> fin_cases a₂
  · exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h.1⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_Qsq_01⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_Qsq_02⟩
  · exact ⟨fun h => absurd h not_isAdj_Qsq_03, fun h => by simp [adjC] at h⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_symm.mp isAdj_Qsq_01⟩
  · exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h.1⟩
  · exact ⟨fun h => absurd h not_isAdj_Qsq_12, fun h => by simp [adjC] at h⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_Qsq_13⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_symm.mp isAdj_Qsq_02⟩
  · exact ⟨fun h => absurd (isAdj_symm.mp h) not_isAdj_Qsq_12, fun h => by simp [adjC] at h⟩
  · exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h.1⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_Qsq_23⟩
  · exact ⟨fun h => absurd (isAdj_symm.mp h) not_isAdj_Qsq_03, fun h => by simp [adjC] at h⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_symm.mp isAdj_Qsq_13⟩
  · exact ⟨fun _ => by decide, fun _ => isAdj_symm.mp isAdj_Qsq_23⟩
  · exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h.1⟩

lemma adjC_zero_left_iff (a : Fin 4) : adjC 0 a ↔ (a = 1 ∨ a = 2) := by
  fin_cases a <;> simp [adjC]

lemma adjC_zero_right_iff (a : Fin 4) : adjC a 0 ↔ (a = 1 ∨ a = 2) := by
  fin_cases a <;> simp [adjC]

def compatIdx (a : Fin 4) (b : Fin 3) : Prop := (cMap a, dMap b) ∈ compatR

lemma compatIdx_zero_iff {a : Fin 4} {b : Fin 3} (h : compatIdx a b) : a = 0 ↔ b = 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [compatIdx, cMap, dMap, compatR, Matrix.vecCons_inj] at h ⊢

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

abbrev LowP (n : ℕ) := (Fin n → Fin 4) × (Fin n → Fin 3)
abbrev HighP (n : ℕ) := (Fin n → Fin 3) × (Fin n → Fin 4)
abbrev W (n : ℕ) := LowP n ⊕ HighP n

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

lemma layer_wToVec_inl (n : ℕ) (p : LowP n) : layer n (wToVec n (Sum.inl p)) = 0 := by
  rcases p with ⟨fc, fd⟩; simp [layer, wToVec, withLast]

lemma layer_wToVec_inr (n : ℕ) (q : HighP n) : layer n (wToVec n (Sum.inr q)) = 1 := by
  rcases q with ⟨fd, fc⟩; simp [layer, wToVec, withLast]

lemma ublk_wToVec_inl_inl (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) (i : Fin n) :
    ublk n (wToVec n (Sum.inl (fc, fd))) (Sum.inl i) = cMap (fc i) := by
  simp [ublk, wToVec, lowVec, withLast, Fin.init_snoc, blk_mkBlocks]

lemma ublk_wToVec_inl_inr (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) (j : Fin n) :
    ublk n (wToVec n (Sum.inl (fc, fd))) (Sum.inr j) = dMap (fd j) := by
  simp [ublk, wToVec, lowVec, withLast, Fin.init_snoc, blk_mkBlocks]

lemma ublk_wToVec_inr_inl (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) (i : Fin n) :
    ublk n (wToVec n (Sum.inr (fd, fc))) (Sum.inl i) = dMap (fd i) := by
  simp [ublk, wToVec, highVec, withLast, Fin.init_snoc, blk_mkBlocks]

lemma ublk_wToVec_inr_inr (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) (j : Fin n) :
    ublk n (wToVec n (Sum.inr (fd, fc))) (Sum.inr j) = cMap (fc j) := by
  simp [ublk, wToVec, highVec, withLast, Fin.init_snoc, blk_mkBlocks]

def suppFin {n m : ℕ} (f : Fin n → Fin (m + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i => f i ≠ 0

lemma iset_wToVec_inl (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) :
    Iset n (wToVec n (Sum.inl (fc, fd))) = suppFin fc := by
  ext i; simp [Iset, suppFin, ublk_wToVec_inl_inl, cMap_eq_zero_iff]

lemma jset_wToVec_inl (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3) :
    Jset n (wToVec n (Sum.inl (fc, fd))) = suppFin fd := by
  ext j; simp [Jset, suppFin, ublk_wToVec_inl_inr, dMap_eq_zero_iff]

lemma iset_wToVec_inr (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) :
    Iset n (wToVec n (Sum.inr (fd, fc))) = suppFin fd := by
  ext i; simp [Iset, suppFin, ublk_wToVec_inr_inl, dMap_eq_zero_iff]

lemma jset_wToVec_inr (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4) :
    Jset n (wToVec n (Sum.inr (fd, fc))) = suppFin fc := by
  ext j; simp [Jset, suppFin, ublk_wToVec_inr_inr, cMap_eq_zero_iff]

lemma mem_Sn_inl_iff (n : ℕ) (p : LowP n) :
    wEquivVertex n (Sum.inl p) ∈ Sn n ↔ (suppFin p.1).card < (suppFin p.2).card := by
  rcases p with ⟨fc, fd⟩
  change (Iset n (wToVec n (Sum.inl (fc, fd)))).card <
    (Jset n (wToVec n (Sum.inl (fc, fd)))).card ↔ _
  rw [iset_wToVec_inl, jset_wToVec_inl]

lemma mem_Sn_inr_iff (n : ℕ) (q : HighP n) :
    wEquivVertex n (Sum.inr q) ∈ Sn n ↔ (suppFin q.1).card < (suppFin q.2).card := by
  rcases q with ⟨fd, fc⟩
  change (Iset n (wToVec n (Sum.inr (fd, fc)))).card <
    (Jset n (wToVec n (Sum.inr (fd, fc)))).card ↔ _
  rw [iset_wToVec_inr, jset_wToVec_inr]

lemma cross_adj_preserves_IJ_low_high (n : ℕ) (hn : 1 ≤ n) (p : LowP n) (q : HighP n)
    (hadj : (Gn n).Adj (wEquivVertex n (Sum.inl p)) (wEquivVertex n (Sum.inr q))) :
    suppFin p.1 = suppFin q.1 ∧ suppFin p.2 = suppFin q.2 := by
  rcases p with ⟨fc, fd⟩; rcases q with ⟨fd', fc'⟩
  have hseg := ((gn_adj_iff n _ _).mp hadj).2
  change IsExposed ℝ (Pn n) (segment ℝ (withLast (lowVec n fc fd) 0) (withLast (highVec n fd' fc') 1)) at hseg
  have hc := (ZeroOneExpansion.corollary_10 n hn (lowVec n fc fd) (highVec n fd' fc')
    (lowVec_mem_Xn n fc fd) (highVec_mem_Yn n fd' fc')).mp hseg
  constructor
  · ext i
    have hci : compatIdx (fc i) (fd' i) := by
      simpa [lowVec, highVec, blk_mkBlocks, compatIdx] using (hc i).1
    simp [suppFin, compatIdx_zero_iff hci]
  · ext j
    have hcj : compatIdx (fc' j) (fd j) := by
      simpa [lowVec, highVec, blk_mkBlocks, compatIdx] using (hc j).2
    simp [suppFin, compatIdx_zero_iff hcj]

def adjLow {n : ℕ} (p₁ p₂ : LowP n) : Prop :=
  (∃ i : Fin n, p₁.2 = p₂.2 ∧ (∀ i', i' ≠ i → p₁.1 i' = p₂.1 i') ∧ adjC (p₁.1 i) (p₂.1 i)) ∨
  (∃ j : Fin n, p₁.1 = p₂.1 ∧ (∀ j', j' ≠ j → p₁.2 j' = p₂.2 j') ∧ p₁.2 j ≠ p₂.2 j)

def adjHigh {n : ℕ} (q₁ q₂ : HighP n) : Prop :=
  (∃ i : Fin n, q₁.2 = q₂.2 ∧ (∀ i', i' ≠ i → q₁.1 i' = q₂.1 i') ∧ q₁.1 i ≠ q₂.1 i) ∨
  (∃ j : Fin n, q₁.1 = q₂.1 ∧ (∀ j', j' ≠ j → q₁.2 j' = q₂.2 j') ∧ adjC (q₁.2 j) (q₂.2 j))

lemma adjLow_ne {n : ℕ} {p₁ p₂ : LowP n} (h : adjLow p₁ p₂) : p₁ ≠ p₂ := by
  rintro rfl
  rcases h with ⟨i, _, _, hadj⟩ | ⟨j, _, _, hne⟩
  · exact hadj.1 rfl
  · exact hne rfl

lemma adjHigh_ne {n : ℕ} {q₁ q₂ : HighP n} (h : adjHigh q₁ q₂) : q₁ ≠ q₂ := by
  rintro rfl
  rcases h with ⟨i, _, _, hne⟩ | ⟨j, _, _, hadj⟩
  · exact hne rfl
  · exact hadj.1 rfl

lemma gn_adj_inl_iff (n : ℕ) (hn : 1 ≤ n) (p₁ p₂ : LowP n) :
    (Gn n).Adj (wEquivVertex n (Sum.inl p₁)) (wEquivVertex n (Sum.inl p₂)) ↔ adjLow p₁ p₂ := by
  by_cases hp : p₁ = p₂
  · subst hp
    exact ⟨fun h => absurd rfl h.ne, fun h => absurd rfl (adjLow_ne h)⟩
  · rcases p₁ with ⟨fc₁, fd₁⟩; rcases p₂ with ⟨fc₂, fd₂⟩
    let u := wEquivVertex n (Sum.inl (fc₁, fd₁))
    let v := wEquivVertex n (Sum.inl (fc₂, fd₂))
    have huv : u ≠ v := fun h => hp (Sum.inl.inj ((wEquivVertex n).injective h))
    have huv_val : u.val ≠ v.val := fun h => huv (Subtype.ext h)
    have hlay0 : layer n u.val = 0 := layer_wToVec_inl n (fc₁, fd₁)
    have hlay : layer n u.val = layer n v.val := by
      rw [hlay0, wEquivVertex_val, layer_wToVec_inl]
    rw [gn_adj_iff, and_iff_right huv,
        (ZeroOneExpansion.lemma_8 n hn u.val v.val u.2 v.2 huv_val hlay).1 hlay0]
    constructor
    · rintro ⟨i | j, hrest, hadj⟩
      · left
        refine ⟨i, ?_, ?_, ?_⟩
        · funext j
          apply dMap_injective
          simpa [u, v, ublk_wToVec_inl_inr] using hrest (Sum.inr j) (by simp)
        · intro i' hi'
          apply cMap_injective
          simpa [u, v, ublk_wToVec_inl_inl] using hrest (Sum.inl i') (by simp [hi'])
        · rw [← isAdj_Qsq_iff]
          simpa [u, v, ublk_wToVec_inl_inl] using hadj
      · right
        refine ⟨j, ?_, ?_, ?_⟩
        · funext i
          apply cMap_injective
          simpa [u, v, ublk_wToVec_inl_inl] using hrest (Sum.inl i) (by simp)
        · intro j' hj'
          apply dMap_injective
          simpa [u, v, ublk_wToVec_inl_inr] using hrest (Sum.inr j') (by simp [hj'])
        · rw [← isAdj_Delta_iff]
          simpa [u, v, ublk_wToVec_inl_inr] using hadj
    · rintro (⟨i, hfd, hfc, hadj⟩ | ⟨j, hfc, hfd, hadj⟩)
      · refine ⟨Sum.inl i, ?_, ?_⟩
        · rintro (i' | j') hk'
          · simp only [u, v, wEquivVertex_val, ublk_wToVec_inl_inl]
            exact congr_arg cMap (hfc i' (by simpa using hk'))
          · simp only [u, v, wEquivVertex_val, ublk_wToVec_inl_inr]
            exact congr_arg dMap (congr_fun hfd j')
        · simpa [u, v, ublk_wToVec_inl_inl, isAdj_Qsq_iff] using hadj
      · refine ⟨Sum.inr j, ?_, ?_⟩
        · rintro (i' | j') hk'
          · simp only [u, v, wEquivVertex_val, ublk_wToVec_inl_inl]
            exact congr_arg cMap (congr_fun hfc i')
          · simp only [u, v, wEquivVertex_val, ublk_wToVec_inl_inr]
            exact congr_arg dMap (hfd j' (by simpa using hk'))
        · simpa [u, v, ublk_wToVec_inl_inr, isAdj_Delta_iff] using hadj

lemma gn_adj_inr_iff (n : ℕ) (hn : 1 ≤ n) (q₁ q₂ : HighP n) :
    (Gn n).Adj (wEquivVertex n (Sum.inr q₁)) (wEquivVertex n (Sum.inr q₂)) ↔ adjHigh q₁ q₂ := by
  by_cases hq : q₁ = q₂
  · subst hq
    exact ⟨fun h => absurd rfl h.ne, fun h => absurd rfl (adjHigh_ne h)⟩
  · rcases q₁ with ⟨fd₁, fc₁⟩; rcases q₂ with ⟨fd₂, fc₂⟩
    let u := wEquivVertex n (Sum.inr (fd₁, fc₁))
    let v := wEquivVertex n (Sum.inr (fd₂, fc₂))
    have huv : u ≠ v := fun h => hq (Sum.inr.inj ((wEquivVertex n).injective h))
    have huv_val : u.val ≠ v.val := fun h => huv (Subtype.ext h)
    have hlay1 : layer n u.val = 1 := layer_wToVec_inr n (fd₁, fc₁)
    have hlay : layer n u.val = layer n v.val := by
      rw [hlay1, wEquivVertex_val, layer_wToVec_inr]
    rw [gn_adj_iff, and_iff_right huv,
        (ZeroOneExpansion.lemma_8 n hn u.val v.val u.2 v.2 huv_val hlay).2 hlay1]
    constructor
    · rintro ⟨i | j, hrest, hadj⟩
      · left
        refine ⟨i, ?_, ?_, ?_⟩
        · funext j
          apply cMap_injective
          simpa [u, v, ublk_wToVec_inr_inr] using hrest (Sum.inr j) (by simp)
        · intro i' hi'
          apply dMap_injective
          simpa [u, v, ublk_wToVec_inr_inl] using hrest (Sum.inl i') (by simp [hi'])
        · rw [← isAdj_Delta_iff]
          simpa [u, v, ublk_wToVec_inr_inl] using hadj
      · right
        refine ⟨j, ?_, ?_, ?_⟩
        · funext i
          apply dMap_injective
          simpa [u, v, ublk_wToVec_inr_inl] using hrest (Sum.inl i) (by simp)
        · intro j' hj'
          apply cMap_injective
          simpa [u, v, ublk_wToVec_inr_inr] using hrest (Sum.inr j') (by simp [hj'])
        · rw [← isAdj_Qsq_iff]
          simpa [u, v, ublk_wToVec_inr_inr] using hadj
    · rintro (⟨i, hfc, hfd, hadj⟩ | ⟨j, hfd, hfc, hadj⟩)
      · refine ⟨Sum.inl i, ?_, ?_⟩
        · rintro (i' | j') hk'
          · simp only [u, v, wEquivVertex_val, ublk_wToVec_inr_inl]
            exact congr_arg dMap (hfd i' (by simpa using hk'))
          · simp only [u, v, wEquivVertex_val, ublk_wToVec_inr_inr]
            exact congr_arg cMap (congr_fun hfc j')
        · simpa [u, v, ublk_wToVec_inr_inl, isAdj_Delta_iff] using hadj
      · refine ⟨Sum.inr j, ?_, ?_⟩
        · rintro (i' | j') hk'
          · simp only [u, v, wEquivVertex_val, ublk_wToVec_inr_inl]
            exact congr_arg dMap (congr_fun hfd i')
          · simp only [u, v, wEquivVertex_val, ublk_wToVec_inr_inr]
            exact congr_arg cMap (hfc j' (by simpa using hk'))
        · simpa [u, v, ublk_wToVec_inr_inr, isAdj_Qsq_iff] using hadj

open Classical in
noncomputable def Blow (n : ℕ) : Finset (LowP n × LowP n) :=
  Finset.univ.filter fun e =>
    (suppFin e.1.1).card < (suppFin e.1.2).card ∧
    ¬ (suppFin e.2.1).card < (suppFin e.2.2).card ∧
    adjLow e.1 e.2

open Classical in
noncomputable def Bhigh (n : ℕ) : Finset (HighP n × HighP n) :=
  Finset.univ.filter fun e =>
    (suppFin e.1.1).card < (suppFin e.1.2).card ∧
    ¬ (suppFin e.2.1).card < (suppFin e.2.2).card ∧
    adjHigh e.1 e.2

lemma ncard_edgeBoundary_eq (n : ℕ) (hn : 1 ≤ n) :
    (edgeBoundary (Gn n) (Sn n)).ncard = (Blow n).card + (Bhigh n).card := by
  classical
  let embLow : LowP n × LowP n ↪ Grunbaum2003.PolytopeVertex (Pn n) × Grunbaum2003.PolytopeVertex (Pn n) :=
    ⟨fun e => (wEquivVertex n (Sum.inl e.1), wEquivVertex n (Sum.inl e.2)), fun e₁ e₂ h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      exact Prod.ext (Sum.inl.inj ((wEquivVertex n).injective h1))
        (Sum.inl.inj ((wEquivVertex n).injective h2))⟩
  let embHigh : HighP n × HighP n ↪ Grunbaum2003.PolytopeVertex (Pn n) × Grunbaum2003.PolytopeVertex (Pn n) :=
    ⟨fun e => (wEquivVertex n (Sum.inr e.1), wEquivVertex n (Sum.inr e.2)), fun e₁ e₂ h => by
      rcases Prod.mk.inj h with ⟨h1, h2⟩
      exact Prod.ext (Sum.inr.inj ((wEquivVertex n).injective h1))
        (Sum.inr.inj ((wEquivVertex n).injective h2))⟩
  have hset : edgeBoundary (Gn n) (Sn n) =
      (((Blow n).map embLow ∪ (Bhigh n).map embHigh : Finset _) : Set _) := by
    ext ⟨u, v⟩
    simp only [edgeBoundary, Set.mem_setOf_eq, Finset.coe_union, Set.mem_union, Finset.mem_coe,
      Finset.mem_map, Blow, Bhigh, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hu, hv, hadj⟩
      obtain ⟨w₁, rfl⟩ := (wEquivVertex n).surjective u
      obtain ⟨w₂, rfl⟩ := (wEquivVertex n).surjective v
      rcases w₁ with p₁ | q₁ <;> rcases w₂ with p₂ | q₂
      · left
        refine ⟨(p₁, p₂), ⟨?_, ?_, ?_⟩, rfl⟩
        · exact (mem_Sn_inl_iff n p₁).mp hu
        · exact fun h => hv ((mem_Sn_inl_iff n p₂).mpr h)
        · exact (gn_adj_inl_iff n hn p₁ p₂).mp hadj
      · exfalso
        have hIJ := cross_adj_preserves_IJ_low_high n hn p₁ q₂ hadj
        have h1 := (mem_Sn_inl_iff n p₁).mp hu
        rw [hIJ.1, hIJ.2] at h1
        exact hv ((mem_Sn_inr_iff n q₂).mpr h1)
      · exfalso
        have hIJ := cross_adj_preserves_IJ_low_high n hn p₂ q₁ hadj.symm
        have h1 := (mem_Sn_inr_iff n q₁).mp hu
        rw [← hIJ.1, ← hIJ.2] at h1
        exact hv ((mem_Sn_inl_iff n p₂).mpr h1)
      · right
        refine ⟨(q₁, q₂), ⟨?_, ?_, ?_⟩, rfl⟩
        · exact (mem_Sn_inr_iff n q₁).mp hu
        · exact fun h => hv ((mem_Sn_inr_iff n q₂).mpr h)
        · exact (gn_adj_inr_iff n hn q₁ q₂).mp hadj
    · rintro (⟨⟨p₁, p₂⟩, ⟨h1, h2, hadj⟩, heq⟩ | ⟨⟨q₁, q₂⟩, ⟨h1, h2, hadj⟩, heq⟩)
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact ⟨(mem_Sn_inl_iff n p₁).mpr h1, fun h => h2 ((mem_Sn_inl_iff n p₂).mp h),
          (gn_adj_inl_iff n hn p₁ p₂).mpr hadj⟩
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact ⟨(mem_Sn_inr_iff n q₁).mpr h1, fun h => h2 ((mem_Sn_inr_iff n q₂).mp h),
          (gn_adj_inr_iff n hn q₁ q₂).mpr hadj⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  refine Finset.disjoint_left.mpr ?_
  rintro ⟨u, v⟩ h1 h2
  rcases Finset.mem_map.mp h1 with ⟨⟨p₁, p₂⟩, _, hp⟩
  rcases Finset.mem_map.mp h2 with ⟨⟨q₁, q₂⟩, _, hq⟩
  have hu1 : u = wEquivVertex n (Sum.inl p₁) := (Prod.mk.inj hp).1.symm
  have hu2 : u = wEquivVertex n (Sum.inr q₁) := (Prod.mk.inj hq).1.symm
  have := (wEquivVertex n).injective (hu1.symm.trans hu2)
  cases this

lemma suppFin_card_step {n m : ℕ} {f₁ f₂ : Fin n → Fin (m + 1)} {i : Fin n}
    (hrest : ∀ i', i' ≠ i → f₁ i' = f₂ i') :
    (f₁ i = 0 ∧ f₂ i ≠ 0 ∧ (suppFin f₂).card = (suppFin f₁).card + 1 ∧ f₁ = Function.update f₂ i 0) ∨
    (f₁ i ≠ 0 ∧ f₂ i = 0 ∧ (suppFin f₁).card = (suppFin f₂).card + 1 ∧ f₁ = Function.update f₂ i (f₁ i)) ∨
    ((suppFin f₁).card = (suppFin f₂).card) := by
  by_cases h1 : f₁ i = 0 <;> by_cases h2 : f₂ i = 0
  · right; right
    have heq : f₁ = f₂ := by
      funext i'
      by_cases hi' : i' = i
      · subst hi'; exact h1.trans h2.symm
      · exact hrest i' hi'
    rw [heq]
  · left
    refine ⟨h1, h2, ?_, ?_⟩
    · have hins : suppFin f₂ = insert i (suppFin f₁) := by
        ext i'
        simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hi' : i' = i
        · subst hi'; simp [h2]
        · simp [hi', hrest i' hi']
      have hnot : i ∉ suppFin f₁ := by simp [suppFin, h1]
      rw [hins, Finset.card_insert_of_notMem hnot]
    · funext i'
      by_cases hi' : i' = i
      · subst hi'; simp [h1]
      · simp [Function.update_of_ne hi', hrest i' hi']
  · right; left
    refine ⟨h1, h2, ?_, ?_⟩
    · have hins : suppFin f₁ = insert i (suppFin f₂) := by
        ext i'
        simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hi' : i' = i
        · subst hi'; simp [h1]
        · simp [hi', hrest i' hi']
      have hnot : i ∉ suppFin f₂ := by simp [suppFin, h2]
      rw [hins, Finset.card_insert_of_notMem hnot]
    · funext i'
      by_cases hi' : i' = i
      · subst hi'; simp
      · simp [Function.update_of_ne hi', hrest i' hi']
  · right; right
    have heq : suppFin f₁ = suppFin f₂ := by
      ext i'
      simp only [suppFin, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hi' : i' = i
      · subst hi'; simp [h1, h2]
      · simp [hrest i' hi']
    rw [heq]

lemma suppFin_update_zero {n m : ℕ} (f : Fin n → Fin (m + 1)) {i : Fin n} (hi : f i ≠ 0) :
    (suppFin (Function.update f i 0)).card + 1 = (suppFin f).card := by
  have hstep := suppFin_card_step (f₁ := Function.update f i 0) (f₂ := f) (i := i)
    (fun i' hi' => Function.update_of_ne hi' 0 f)
  have h0 : Function.update f i 0 i = 0 := Function.update_self i 0 f
  rcases hstep with ⟨_, _, hcard, _⟩ | ⟨hne, _, _, _⟩ | _
  · omega
  · exact absurd h0 hne
  · exfalso
    have hmem1 : i ∈ suppFin f := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have hmem0 : i ∉ suppFin (Function.update f i 0) := by simp [suppFin]
    have hsub : suppFin (Function.update f i 0) ⊂ suppFin f := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨fun i' hi' => ?_, fun heq => hmem0 (heq ▸ hmem1)⟩
      have hi'_ne : i' ≠ i := fun h => hmem0 (h ▸ hi')
      have hval := (Finset.mem_filter.mp hi').2
      rw [Function.update_of_ne hi'_ne] at hval
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i', hval⟩
    have hlt := Finset.card_lt_card hsub
    omega

lemma suppFin_update_nonzero {n m : ℕ} (f : Fin n → Fin (m + 1)) {i : Fin n} (hi : f i = 0)
    {b : Fin (m + 1)} (hb : b ≠ 0) :
    (suppFin (Function.update f i b)).card = (suppFin f).card + 1 := by
  have h := suppFin_update_zero (Function.update f i b) (i := i) (by simp [hb])
  have hupd : Function.update (Function.update f i b) i 0 = f := by
    funext i'
    by_cases hi' : i' = i
    · subst hi'; simp [hi]
    · simp [Function.update_of_ne hi']
  rw [hupd] at h
  omega

lemma card_filter_eq_zero {n m : ℕ} (f : Fin n → Fin (m + 1)) :
    (Finset.univ.filter fun i => f i = 0).card = n - (suppFin f).card := by
  have huniv : (Finset.univ : Finset (Fin n)) =
      (Finset.univ.filter fun i => f i = 0) ∪ suppFin f := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, suppFin, true_and, true_iff]
    exact em (f i = 0)
  have hdisj : Disjoint (Finset.univ.filter fun i => f i = 0) (suppFin f) := by
    refine Finset.disjoint_left.mpr fun i h1 h2 => ?_
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hcard : n = (Finset.univ.filter fun i => f i = 0).card + (suppFin f).card := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ = ((Finset.univ.filter fun i => f i = 0) ∪ suppFin f).card := by rw [← huniv]
      _ = (Finset.univ.filter fun i => f i = 0).card + (suppFin f).card :=
          Finset.card_union_of_disjoint hdisj
  omega

open Classical in
noncomputable def fiberLow (n : ℕ) (p₂ : LowP n) : Finset (LowP n) :=
  Finset.univ.filter fun p₁ => (p₁, p₂) ∈ Blow n

open Classical in
noncomputable def fiberHigh (n : ℕ) (q₂ : HighP n) : Finset (HighP n) :=
  Finset.univ.filter fun q₁ => (q₁, q₂) ∈ Bhigh n

lemma mem_Blow_diag {n : ℕ} {p₁ p₂ : LowP n} (h : (p₁, p₂) ∈ Blow n) :
    (suppFin p₂.1).card = (suppFin p₂.2).card := by
  classical
  simp only [Blow, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with ⟨hlt1, hge2, (⟨i, hfd, hrest, _⟩ | ⟨j, hfc, hrest, _⟩)⟩
  · rw [hfd] at hlt1
    rcases suppFin_card_step hrest with ⟨_, _, hcard, _⟩ | ⟨_, _, hcard, _⟩ | hcard <;> omega
  · rw [hfc] at hlt1
    rcases suppFin_card_step hrest with ⟨_, _, hcard, _⟩ | ⟨_, _, hcard, _⟩ | hcard <;> omega

lemma mem_Bhigh_diag {n : ℕ} {q₁ q₂ : HighP n} (h : (q₁, q₂) ∈ Bhigh n) :
    (suppFin q₂.1).card = (suppFin q₂.2).card := by
  classical
  simp only [Bhigh, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with ⟨hlt1, hge2, (⟨i, hfc, hrest, _⟩ | ⟨j, hfd, hrest, _⟩)⟩
  · rw [hfc] at hlt1
    rcases suppFin_card_step hrest with ⟨_, _, hcard, _⟩ | ⟨_, _, hcard, _⟩ | hcard <;> omega
  · rw [hfd] at hlt1
    rcases suppFin_card_step hrest with ⟨_, _, hcard, _⟩ | ⟨_, _, hcard, _⟩ | hcard <;> omega

def card12 {n : ℕ} (fc : Fin n → Fin 4) : ℕ :=
  (Finset.univ.filter fun i => fc i = 1 ∨ fc i = 2).card

lemma fin3_mem_12 {b : Fin 3} (hb : b ≠ 0) : b ∈ ({1, 2} : Finset (Fin 3)) := by
  fin_cases b
  · exact absurd rfl hb
  · decide
  · decide

lemma card_fiberLow (n : ℕ) (fc : Fin n → Fin 4) (fd : Fin n → Fin 3)
    (hdiag : (suppFin fc).card = (suppFin fd).card) :
    (fiberLow n (fc, fd)).card = card12 fc + 2 * (n - (suppFin fd).card) := by
  classical
  let s1 := Finset.univ.filter fun i : Fin n => fc i = 1 ∨ fc i = 2
  let s2 := (Finset.univ.filter fun j : Fin n => fd j = 0) ×ˢ ({1, 2} : Finset (Fin 3))
  let g1 : Finset (LowP n) := s1.image (fun i => (Function.update fc i 0, fd))
  let g2 : Finset (LowP n) := s2.image (fun jb => (fc, Function.update fd jb.1 jb.2))
  have hfib : fiberLow n (fc, fd) = g1 ∪ g2 := by
    ext p₁
    simp only [fiberLow, Blow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      g1, g2, Finset.mem_image, s1, s2, Finset.mem_product]
    constructor
    · rintro ⟨hlt1, _, (⟨i, hfd, hrest, hadj⟩ | ⟨j, hfc_eq, hrest, hne⟩)⟩
      · left
        rcases p₁ with ⟨fc₁, fd₁⟩
        dsimp only at hfd hrest hadj hlt1
        subst hfd
        rcases suppFin_card_step hrest with ⟨h0, _, _, hupd⟩ | ⟨_, _, hcard, _⟩ | hcard
        · refine ⟨i, ?_, Prod.ext hupd.symm rfl⟩
          rw [h0] at hadj
          exact (adjC_zero_left_iff (fc i)).mp hadj
        · omega
        · omega
      · right
        rcases p₁ with ⟨fc₁, fd₁⟩
        dsimp only at hfc_eq hrest hne hlt1
        subst hfc_eq
        rcases suppFin_card_step hrest with ⟨_, _, hcard, _⟩ | ⟨hne0, h0, _, hupd⟩ | hcard
        · omega
        · exact ⟨(j, fd₁ j), ⟨h0, fin3_mem_12 hne0⟩, Prod.ext rfl hupd.symm⟩
        · omega
    · rintro (⟨i, hi, rfl⟩ | ⟨⟨j, b⟩, ⟨hj, hb⟩, rfl⟩)
      · dsimp only at hi ⊢
        have hfc_ne : fc i ≠ 0 := by rcases hi with h | h <;> rw [h] <;> decide
        have hstep := suppFin_update_zero fc hfc_ne
        refine ⟨by omega, by omega, Or.inl ⟨i, rfl, fun i' hi' => Function.update_of_ne hi' 0 fc, ?_⟩⟩
        change adjC (Function.update fc i 0 i) (fc i)
        rw [Function.update_self]
        exact (adjC_zero_left_iff (fc i)).mpr hi
      · dsimp only at hj hb ⊢
        have hb_ne : b ≠ 0 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb
          rcases hb with rfl | rfl <;> decide
        have hstep := suppFin_update_nonzero fd hj hb_ne
        refine ⟨by omega, by omega, Or.inr ⟨j, rfl, fun j' hj' => Function.update_of_ne hj' b fd, ?_⟩⟩
        change Function.update fd j b j ≠ fd j
        rw [Function.update_self, hj]
        exact hb_ne
  have hdisj : Disjoint g1 g2 := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨⟨j, b⟩, _, heq⟩
    have h1 := congr_fun (Prod.mk.inj heq).1 i
    rw [Function.update_self] at h1
    simp only [s1, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with h | h <;> rw [h1] at h <;> exact absurd h (by decide)
  have hg1 : g1.card = card12 fc := by
    dsimp only [g1, card12, s1]
    apply Finset.card_image_of_injOn
    intro i₁ hi₁ i₂ hi₂ heq
    by_contra hne
    have h1 := congr_fun (Prod.mk.inj heq).1 i₁
    rw [Function.update_self, Function.update_of_ne hne] at h1
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi₁
    rcases hi₁ with h | h <;> rw [← h1] at h <;> exact absurd h (by decide)
  have hg2 : g2.card = 2 * (n - (suppFin fd).card) := by
    have hinj : Set.InjOn (fun jb : Fin n × Fin 3 => (fc, Function.update fd jb.1 jb.2)) ↑s2 := by
      rintro ⟨j₁, b₁⟩ h₁ ⟨j₂, b₂⟩ h₂ heq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp h₁) with ⟨h₁j, h₁b⟩
      dsimp only at h₁j h₁b
      have hfd₁ : fd j₁ = 0 := (Finset.mem_filter.mp h₁j).2
      have hb₁_ne : b₁ ≠ 0 := by
        rcases Finset.mem_insert.mp h₁b with rfl | hb'
        · decide
        · rw [Finset.mem_singleton.mp hb']; decide
      have hj_eq : j₁ = j₂ := by
        by_contra hj_ne
        have hval := congr_fun (Prod.mk.inj heq).2 j₁
        rw [Function.update_self, Function.update_of_ne hj_ne, hfd₁] at hval
        exact hb₁_ne hval
      subst hj_eq
      have hb_eq : b₁ = b₂ := by
        have hval := congr_fun (Prod.mk.inj heq).2 j₁
        simpa using hval
      exact Prod.ext rfl hb_eq
    rw [Finset.card_image_of_injOn hinj]
    have hc2 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
    simp only [s2, Finset.card_product, hc2, card_filter_eq_zero]
    ring
  rw [hfib, Finset.card_union_of_disjoint hdisj, hg1, hg2]

lemma card_fiberHigh (n : ℕ) (fd : Fin n → Fin 3) (fc : Fin n → Fin 4)
    (hdiag : (suppFin fd).card = (suppFin fc).card) :
    (fiberHigh n (fd, fc)).card = (suppFin fd).card + 2 * (n - (suppFin fc).card) := by
  classical
  let s1 := suppFin fd
  let s2 := (Finset.univ.filter fun j : Fin n => fc j = 0) ×ˢ ({1, 2} : Finset (Fin 4))
  let g1 : Finset (HighP n) := s1.image (fun i => (Function.update fd i 0, fc))
  let g2 : Finset (HighP n) := s2.image (fun ja => (fd, Function.update fc ja.1 ja.2))
  have hfib : fiberHigh n (fd, fc) = g1 ∪ g2 := by
    ext q₁
    simp only [fiberHigh, Bhigh, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      g1, g2, Finset.mem_image, s1, s2, Finset.mem_product]
    constructor
    · rintro ⟨hlt1, _, (⟨i, hfc_eq, hrest, hne⟩ | ⟨j, hfd_eq, hrest, hadj⟩)⟩
      · left
        rcases q₁ with ⟨fd₁, fc₁⟩
        dsimp only at hfc_eq hrest hne hlt1
        subst hfc_eq
        rcases suppFin_card_step hrest with ⟨h0, hne0, _, hupd⟩ | ⟨_, _, hcard, _⟩ | hcard
        · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne0⟩, Prod.ext hupd.symm rfl⟩
        · omega
        · omega
      · right
        rcases q₁ with ⟨fd₁, fc₁⟩
        dsimp only at hfd_eq hrest hadj hlt1
        subst hfd_eq
        rcases suppFin_card_step hrest with ⟨_, _, hcard, _⟩ | ⟨_, h0, _, hupd⟩ | hcard
        · omega
        · refine ⟨(j, fc₁ j), ⟨h0, ?_⟩, Prod.ext rfl hupd.symm⟩
          change fc₁ j ∈ ({1, 2} : Finset (Fin 4))
          rw [h0] at hadj
          rcases (adjC_zero_right_iff (fc₁ j)).mp hadj with h | h <;> rw [h] <;> decide
        · omega
    · rintro (⟨i, hi, rfl⟩ | ⟨⟨j, a⟩, ⟨hj, ha⟩, rfl⟩)
      · dsimp only at hi ⊢
        have hfd_ne : fd i ≠ 0 := (Finset.mem_filter.mp hi).2
        have hstep := suppFin_update_zero fd hfd_ne
        refine ⟨by omega, by omega, Or.inl ⟨i, rfl, fun i' hi' => Function.update_of_ne hi' 0 fd, ?_⟩⟩
        change Function.update fd i 0 i ≠ fd i
        rw [Function.update_self]
        exact hfd_ne.symm
      · dsimp only at hj ha ⊢
        have ha12 : a = 1 ∨ a = 2 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          exact ha
        have ha_ne : a ≠ 0 := by rcases ha12 with rfl | rfl <;> decide
        have hstep := suppFin_update_nonzero fc hj ha_ne
        refine ⟨by omega, by omega, Or.inr ⟨j, rfl, fun j' hj' => Function.update_of_ne hj' a fc, ?_⟩⟩
        change adjC (Function.update fc j a j) (fc j)
        rw [Function.update_self, hj]
        exact (adjC_zero_right_iff a).mpr ha12
  have hdisj : Disjoint g1 g2 := by
    refine Finset.disjoint_left.mpr ?_
    intro q hq1 hq2
    rcases Finset.mem_image.mp hq1 with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hq2 with ⟨⟨j, a⟩, _, heq⟩
    have h1 := congr_fun (Prod.mk.inj heq).1 i
    rw [Function.update_self] at h1
    exact (Finset.mem_filter.mp hi).2 h1
  have hg1 : g1.card = (suppFin fd).card := by
    dsimp only [g1, s1]
    apply Finset.card_image_of_injOn
    intro i₁ hi₁ i₂ hi₂ heq
    by_contra hne
    have h1 := congr_fun (Prod.mk.inj heq).1 i₁
    rw [Function.update_self, Function.update_of_ne hne] at h1
    exact (Finset.mem_filter.mp hi₁).2 h1.symm
  have hg2 : g2.card = 2 * (n - (suppFin fc).card) := by
    have hinj : Set.InjOn (fun ja : Fin n × Fin 4 => (fd, Function.update fc ja.1 ja.2)) ↑s2 := by
      rintro ⟨j₁, a₁⟩ h₁ ⟨j₂, a₂⟩ h₂ heq
      rcases Finset.mem_product.mp (Finset.mem_coe.mp h₁) with ⟨h₁j, h₁a⟩
      dsimp only at h₁j h₁a
      have hfc₁ : fc j₁ = 0 := (Finset.mem_filter.mp h₁j).2
      have ha₁_ne : a₁ ≠ 0 := by
        rcases Finset.mem_insert.mp h₁a with rfl | ha'
        · decide
        · rw [Finset.mem_singleton.mp ha']; decide
      have hj_eq : j₁ = j₂ := by
        by_contra hj_ne
        have hval := congr_fun (Prod.mk.inj heq).2 j₁
        rw [Function.update_self, Function.update_of_ne hj_ne, hfc₁] at hval
        exact ha₁_ne hval
      subst hj_eq
      have ha_eq : a₁ = a₂ := by
        have hval := congr_fun (Prod.mk.inj heq).2 j₁
        simpa using hval
      exact Prod.ext rfl ha_eq
    rw [Finset.card_image_of_injOn hinj]
    have hc2 : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
    simp only [s2, Finset.card_product, hc2, card_filter_eq_zero]
    ring
  rw [hfib, Finset.card_union_of_disjoint hdisj, hg1, hg2]

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

lemma card_suppFin_card_eq (n m r : ℕ) :
    (Finset.univ.filter (fun f : Fin n → Fin (m + 1) => (suppFin f).card = r)).card =
      n.choose r * m ^ r := by
  have hpart :
      Finset.univ.filter (fun f : Fin n → Fin (m + 1) => (suppFin f).card = r) =
        ((Finset.univ : Finset (Fin n)).powersetCard r).biUnion
          (fun K => Finset.univ.filter (fun f : Fin n → Fin (m + 1) => suppFin f = K)) := by
    ext f; simp [Finset.mem_powersetCard]
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

def rot4 : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 1

lemma rot4_three (a : Fin 4) : rot4 (rot4 (rot4 a)) = a := by
  fin_cases a <;> rfl

lemma rot4_eq_zero_iff (a : Fin 4) : rot4 a = 0 ↔ a = 0 := by
  fin_cases a <;> simp [rot4]

def phiRot {n : ℕ} (fc : Fin n → Fin 4) : Fin n → Fin 4 := fun i => rot4 (fc i)

lemma phiRot_three {n : ℕ} (fc : Fin n → Fin 4) : phiRot (phiRot (phiRot fc)) = fc := by
  funext i; exact rot4_three (fc i)

lemma suppFin_phiRot {n : ℕ} (fc : Fin n → Fin 4) : suppFin (phiRot fc) = suppFin fc := by
  ext i; simp [suppFin, phiRot, rot4_eq_zero_iff]

lemma is12_rot_sum (a : Fin 4) :
    (if a = 1 ∨ a = 2 then 1 else 0) +
    (if rot4 a = 1 ∨ rot4 a = 2 then 1 else 0) +
    (if rot4 (rot4 a) = 1 ∨ rot4 (rot4 a) = 2 then 1 else 0) =
    (if a ≠ 0 then 2 else 0) := by
  fin_cases a <;> decide

lemma card12_rot_sum {n : ℕ} (fc : Fin n → Fin 4) :
    card12 fc + card12 (phiRot fc) + card12 (phiRot (phiRot fc)) = 2 * (suppFin fc).card := by
  have h1 : card12 fc = ∑ i : Fin n, (if fc i = 1 ∨ fc i = 2 then 1 else 0) := by
    rw [card12, Finset.card_filter]
  have h2 : card12 (phiRot fc) = ∑ i : Fin n, (if phiRot fc i = 1 ∨ phiRot fc i = 2 then 1 else 0) := by
    rw [card12, Finset.card_filter]
  have h3 : card12 (phiRot (phiRot fc)) =
      ∑ i : Fin n, (if phiRot (phiRot fc) i = 1 ∨ phiRot (phiRot fc) i = 2 then 1 else 0) := by
    rw [card12, Finset.card_filter]
  have hs : 2 * (suppFin fc).card = ∑ i : Fin n, (if fc i ≠ 0 then 2 else 0) := by
    rw [suppFin, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : fc i ≠ 0 <;> simp [hi]
  rw [h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, hs]
  apply Finset.sum_congr rfl
  intro i _
  exact is12_rot_sum (fc i)

lemma three_mul_sum_card12 (n r : ℕ) :
    3 * ∑ fc ∈ Finset.univ.filter (fun fc : Fin n → Fin 4 => (suppFin fc).card = r), card12 fc =
      2 * r * (n.choose r * 3 ^ r) := by
  let Sr := Finset.univ.filter (fun fc : Fin n → Fin 4 => (suppFin fc).card = r)
  have hrot : ∀ g : (Fin n → Fin 4) → ℕ,
      ∑ fc ∈ Sr, g (phiRot fc) = ∑ fc ∈ Sr, g fc := by
    intro g
    refine Finset.sum_bij (fun fc _ => phiRot fc) ?_ ?_ ?_ ?_
    · intro fc hfc
      simp only [Sr, Finset.mem_filter, Finset.mem_univ, true_and] at hfc ⊢
      rwa [suppFin_phiRot]
    · intro fc₁ _ fc₂ _ heq
      have := congr_arg (fun f => phiRot (phiRot f)) heq
      simpa [phiRot_three] using this
    · intro fc hfc
      refine ⟨phiRot (phiRot fc), ?_, phiRot_three fc⟩
      simp only [Sr, Finset.mem_filter, Finset.mem_univ, true_and] at hfc ⊢
      rwa [suppFin_phiRot, suppFin_phiRot]
    · intro _ _; rfl
  have hsum1 : ∑ fc ∈ Sr, card12 (phiRot fc) = ∑ fc ∈ Sr, card12 fc := hrot card12
  have hsum2 : ∑ fc ∈ Sr, card12 (phiRot (phiRot fc)) = ∑ fc ∈ Sr, card12 fc := by
    calc ∑ fc ∈ Sr, card12 (phiRot (phiRot fc))
        = ∑ fc ∈ Sr, card12 (phiRot fc) := hrot (fun f => card12 (phiRot f))
      _ = ∑ fc ∈ Sr, card12 fc := hsum1
  have h3 : 3 * ∑ fc ∈ Sr, card12 fc =
      ∑ fc ∈ Sr, (card12 fc + card12 (phiRot fc) + card12 (phiRot (phiRot fc))) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum1, hsum2]
    ring
  change 3 * ∑ fc ∈ Sr, card12 fc = 2 * r * (n.choose r * 3 ^ r)
  rw [h3]
  have hcongr : ∑ fc ∈ Sr, (card12 fc + card12 (phiRot fc) + card12 (phiRot (phiRot fc))) =
      ∑ _fc ∈ Sr, 2 * r := by
    apply Finset.sum_congr rfl
    intro fc hfc
    rw [card12_rot_sum, (Finset.mem_filter.mp hfc).2]
  rw [hcongr, Finset.sum_const, smul_eq_mul]
  dsimp only [Sr]
  rw [card_suppFin_card_eq n 3 r]
  ring

lemma three_mul_card_Blow (n : ℕ) :
    3 * (Blow n).card =
      ∑ r ∈ Finset.range (n + 1), Acount n r r * (6 * (n - r) + 2 * r) := by
  classical
  let DiagLow := Finset.univ.filter (fun p₂ : LowP n => (suppFin p₂.1).card = (suppFin p₂.2).card)
  have hpart1 : Blow n = DiagLow.biUnion (fun p₂ =>
      (fiberLow n p₂).map ⟨fun p₁ => (p₁, p₂), fun _ _ h => (Prod.mk.inj h).1⟩) := by
    ext ⟨p₁, p₂⟩
    simp only [Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk, DiagLow,
      fiberLow, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨p₂, mem_Blow_diag h, p₁, h, rfl⟩
    · rintro ⟨p₂', _, p₁', h, heq⟩
      cases heq
      exact h
  have hcard1 : (Blow n).card = ∑ p₂ ∈ DiagLow, (fiberLow n p₂).card := by
    rw [hpart1, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro p₂ _; exact Finset.card_map _
    · intro a _ b _ hne
      refine Finset.disjoint_left.mpr ?_
      intro e he₁ he₂
      rcases Finset.mem_map.mp he₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_map.mp he₂ with ⟨_, _, heq⟩
      exact hne (Prod.mk.inj heq).2.symm
  have hpart2 : DiagLow = (Finset.range (n + 1)).biUnion (fun r =>
      (Finset.univ.filter (fun fc : Fin n → Fin 4 => (suppFin fc).card = r)) ×ˢ
      (Finset.univ.filter (fun fd : Fin n → Fin 3 => (suppFin fd).card = r))) := by
    ext ⟨fc, fd⟩
    simp only [DiagLow, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_product]
    constructor
    · intro h
      refine ⟨(suppFin fc).card, ?_, rfl, h.symm⟩
      have hle : (suppFin fc).card ≤ n := by
        calc (suppFin fc).card ≤ (Finset.univ : Finset (Fin n)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
      omega
    · rintro ⟨r, _, rfl, h⟩; exact h.symm
  rw [hcard1, hpart2, Finset.sum_biUnion]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    let Sr := Finset.univ.filter (fun fc : Fin n → Fin 4 => (suppFin fc).card = r)
    let Tr := Finset.univ.filter (fun fd : Fin n → Fin 3 => (suppFin fd).card = r)
    change 3 * ∑ p₂ ∈ Sr ×ˢ Tr, (fiberLow n p₂).card = Acount n r r * (6 * (n - r) + 2 * r)
    have hfib_sum : ∑ p₂ ∈ Sr ×ˢ Tr, (fiberLow n p₂).card =
        ∑ p₂ ∈ Sr ×ˢ Tr, (card12 p₂.1 + 2 * (n - r)) := by
      apply Finset.sum_congr rfl
      rintro ⟨fc, fd⟩ hp
      simp only [Sr, Tr, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [card_fiberLow n fc fd (hp.1.trans hp.2.symm), hp.2]
    rw [hfib_sum, Finset.sum_product]
    have hinner : ∑ x ∈ Sr, ∑ _y ∈ Tr, (card12 x + 2 * (n - r)) =
        Tr.card * (∑ x ∈ Sr, card12 x + Sr.card * (2 * (n - r))) := by
      simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
    rw [hinner]
    have h3 : 3 * (Tr.card * (∑ x ∈ Sr, card12 x + Sr.card * (2 * (n - r)))) =
        Tr.card * (3 * ∑ x ∈ Sr, card12 x + 3 * (Sr.card * (2 * (n - r)))) := by ring
    rw [h3]
    dsimp only [Sr, Tr]
    rw [three_mul_sum_card12 n r, card_suppFin_card_eq n 3 r, card_suppFin_card_eq n 2 r, Acount]
    ring
  · intro r₁ _ r₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨fc, fd⟩ h₁ h₂
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact hne (h₁.1.symm.trans h₂.1)

lemma card_Bhigh (n : ℕ) :
    (Bhigh n).card = ∑ r ∈ Finset.range (n + 1), Acount n r r * (2 * (n - r) + r) := by
  classical
  let DiagHigh := Finset.univ.filter (fun q₂ : HighP n => (suppFin q₂.1).card = (suppFin q₂.2).card)
  have hpart1 : Bhigh n = DiagHigh.biUnion (fun q₂ =>
      (fiberHigh n q₂).map ⟨fun q₁ => (q₁, q₂), fun _ _ h => (Prod.mk.inj h).1⟩) := by
    ext ⟨q₁, q₂⟩
    simp only [Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk, DiagHigh,
      fiberHigh, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨q₂, mem_Bhigh_diag h, q₁, h, rfl⟩
    · rintro ⟨q₂', _, q₁', h, heq⟩
      cases heq
      exact h
  have hcard1 : (Bhigh n).card = ∑ q₂ ∈ DiagHigh, (fiberHigh n q₂).card := by
    rw [hpart1, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro q₂ _; exact Finset.card_map _
    · intro a _ b _ hne
      refine Finset.disjoint_left.mpr ?_
      intro e he₁ he₂
      rcases Finset.mem_map.mp he₁ with ⟨_, _, rfl⟩
      rcases Finset.mem_map.mp he₂ with ⟨_, _, heq⟩
      exact hne (Prod.mk.inj heq).2.symm
  have hpart2 : DiagHigh = (Finset.range (n + 1)).biUnion (fun r =>
      (Finset.univ.filter (fun fd : Fin n → Fin 3 => (suppFin fd).card = r)) ×ˢ
      (Finset.univ.filter (fun fc : Fin n → Fin 4 => (suppFin fc).card = r))) := by
    ext ⟨fd, fc⟩
    simp only [DiagHigh, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_product]
    constructor
    · intro h
      refine ⟨(suppFin fd).card, ?_, rfl, h.symm⟩
      have hle : (suppFin fd).card ≤ n := by
        calc (suppFin fd).card ≤ (Finset.univ : Finset (Fin n)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
      omega
    · rintro ⟨r, _, rfl, h⟩; exact h.symm
  rw [hcard1, hpart2, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro r _
    let Tr := Finset.univ.filter (fun fd : Fin n → Fin 3 => (suppFin fd).card = r)
    let Sr := Finset.univ.filter (fun fc : Fin n → Fin 4 => (suppFin fc).card = r)
    change ∑ q₂ ∈ Tr ×ˢ Sr, (fiberHigh n q₂).card = Acount n r r * (2 * (n - r) + r)
    have hfib_sum : ∑ q₂ ∈ Tr ×ˢ Sr, (fiberHigh n q₂).card =
        ∑ _q₂ ∈ Tr ×ˢ Sr, (r + 2 * (n - r)) := by
      apply Finset.sum_congr rfl
      rintro ⟨fd, fc⟩ hq
      simp only [Tr, Sr, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [card_fiberHigh n fd fc (hq.1.trans hq.2.symm), hq.1, hq.2]
    rw [hfib_sum, Finset.sum_const, smul_eq_mul, Finset.card_product]
    dsimp only [Tr, Sr]
    rw [card_suppFin_card_eq n 2 r, card_suppFin_card_eq n 3 r, Acount]
    ring
  · intro r₁ _ r₂ _ hne
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨fd, fc⟩ h₁ h₂
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact hne (h₁.1.symm.trans h₂.1)

lemma three_mul_ncard_edgeBoundary (n : ℕ) (hn : 1 ≤ n) :
    3 * (edgeBoundary (Gn n) (Sn n)).ncard =
      ∑ r ∈ Finset.range (n + 1), Acount n r r * (12 * (n - r) + 5 * r) := by
  rw [ncard_edgeBoundary_eq n hn, Nat.mul_add, three_mul_card_Blow n, card_Bhigh n,
      Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

end Aux_ZOE_lemma13

open ZeroOneExpansion Aux_ZOE_lemma13

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ((edgeBoundary (Gn n) (Sn n)).ncard : ℝ) =
        ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ) * (4 * ((n : ℝ) - r) + 5 * (r : ℝ) / 3) ∧
    ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ) * (4 * ((n : ℝ) - r) + 5 * (r : ℝ) / 3) ≤
        4 * n * ∑ r ∈ Finset.range (n + 1), (Acount n r r : ℝ) := by
  constructor
  · have hnat := three_mul_ncard_edgeBoundary n hn
    have hreal : (3 : ℝ) * ((edgeBoundary (Gn n) (Sn n)).ncard : ℝ) =
        ∑ r ∈ Finset.range (n + 1),
          ((Acount n r r : ℝ) * (12 * (((n - r : ℕ) : ℝ)) + 5 * (r : ℝ))) := by
      exact_mod_cast hnat
    have hrhs : ∑ r ∈ Finset.range (n + 1),
          ((Acount n r r : ℝ) * (12 * (((n - r : ℕ) : ℝ)) + 5 * (r : ℝ))) =
        3 * ∑ r ∈ Finset.range (n + 1),
          (Acount n r r : ℝ) * (4 * ((n : ℝ) - r) + 5 * (r : ℝ) / 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hr_le : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [Nat.cast_sub hr_le]
      ring
    linarith
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    have hA : 0 ≤ (Acount n r r : ℝ) := Nat.cast_nonneg _
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    have hcoeff : 4 * ((n : ℝ) - r) + 5 * (r : ℝ) / 3 ≤ 4 * (n : ℝ) := by linarith
    calc (Acount n r r : ℝ) * (4 * ((n : ℝ) - r) + 5 * (r : ℝ) / 3)
        ≤ (Acount n r r : ℝ) * (4 * (n : ℝ)) := mul_le_mul_of_nonneg_left hcoeff hA
      _ = 4 * (n : ℝ) * (Acount n r r : ℝ) := by ring
