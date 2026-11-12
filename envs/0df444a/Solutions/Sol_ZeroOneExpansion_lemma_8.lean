-- Prove2me | solution 1 for ZeroOneExpansion.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:54:15.520955+00:00
-- url     : https://prove2.me/submissions/7da395c2-8784-4905-82ad-139e63fe5106

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn
import Definitions.Def_ZeroOneExpansion_IsAdj
import Theorems.Thm_ZeroOneExpansion_fact_2
import Theorems.Thm_ZeroOneExpansion_fact_3
import Theorems.Thm_ZeroOneExpansion_fact_5

set_option autoImplicit false

namespace Aux_ZOE_lemma8

open ZeroOneExpansion Matrix

def mkDual {m : ℕ} (c : Fin m → ℝ) : StrongDual ℝ (Fin m → ℝ) :=
  ∑ k : Fin m, c k • ContinuousLinearMap.proj k

lemma mkDual_apply {m : ℕ} (c y : Fin m → ℝ) : mkDual c y = c ⬝ᵥ y := by
  simp [mkDual, dotProduct]

lemma vec_eq_sum_single {m : ℕ} (y : Fin m → ℝ) :
    y = ∑ k : Fin m, y k • Pi.single k (1 : ℝ) := by
  ext j; simp [Pi.single_apply]

lemma dual_eq_dot {m : ℕ} (L : StrongDual ℝ (Fin m → ℝ)) :
    ∃ c : Fin m → ℝ, ∀ y : Fin m → ℝ, L y = c ⬝ᵥ y := by
  refine ⟨fun k => L (Pi.single k 1), fun y => ?_⟩
  conv_lhs => rw [vec_eq_sum_single y]
  simp [map_sum, map_smul, dotProduct, mul_comm]

lemma dot_withLast {d : ℕ} (w x : Fin d → ℝ) (γ t : ℝ) :
    withLast w γ ⬝ᵥ withLast x t = w ⬝ᵥ x + γ * t := by
  simp [dotProduct, Fin.sum_univ_castSucc, withLast]

lemma withLast_decomp {d : ℕ} (x : Fin d → ℝ) (t : ℝ) :
    withLast x t =
      (∑ i : Fin d, x i • Pi.single i.castSucc (1 : ℝ)) +
        t • Pi.single (Fin.last d) (1 : ℝ) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [withLast]
  · simp [withLast, Pi.single_apply]

lemma dual_withLast {d : ℕ} (l : StrongDual ℝ (Fin (d + 1) → ℝ)) :
    ∃ (w : Fin d → ℝ) (γ : ℝ), ∀ (x : Fin d → ℝ) (t : ℝ),
      l (withLast x t) = w ⬝ᵥ x + γ * t := by
  refine ⟨fun i => l (Pi.single i.castSucc 1), l (Pi.single (Fin.last d) 1), fun x t => ?_⟩
  rw [withLast_decomp x t, map_add, map_sum, map_smul, smul_eq_mul, mul_comm t]
  congr 1
  simp [map_smul, dotProduct, mul_comm]

def withLastZeroLinear (d : ℕ) : (Fin d → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun z := withLast z 0
  map_add' x y := by
    ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [withLast]
  map_smul' r x := by
    ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [withLast]

def withLastOneAffine (d : ℕ) : (Fin d → ℝ) →ᵃ[ℝ] (Fin (d + 1) → ℝ) where
  toFun z := withLast z 1
  linear := withLastZeroLinear d
  map_vadd' p v := by
    ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;>
      simp [withLastZeroLinear, withLast, vadd_eq_add, add_comm]

lemma withLast_inj_left {d : ℕ} {x y : Fin d → ℝ} {t : ℝ}
    (h : withLast x t = withLast y t) : x = y := by
  ext i
  have := congr_fun h i.castSucc
  simpa [withLast] using this

lemma image_withLastZero_segment {d : ℕ} (x y : Fin d → ℝ) :
    (fun z => withLast z 0) '' segment ℝ x y = segment ℝ (withLast x 0) (withLast y 0) := by
  rw [← convexHull_pair, ← convexHull_pair]
  have := (withLastZeroLinear d).image_convexHull {x, y}
  simpa [withLastZeroLinear, Set.image_pair] using this

lemma image_withLastOne_segment {d : ℕ} (x y : Fin d → ℝ) :
    (fun z => withLast z 1) '' segment ℝ x y = segment ℝ (withLast x 1) (withLast y 1) := by
  rw [← convexHull_pair, ← convexHull_pair]
  have := (withLastOneAffine d).image_convexHull {x, y}
  simpa [withLastOneAffine, Set.image_pair] using this

lemma isExposed_cayleySum_lower_segment {d : ℕ} (A B : Finset (Fin d → ℝ))
    (hA : A.Nonempty) (hB : B.Nonempty) {x y : Fin d → ℝ} (hx : x ∈ A) (hy : y ∈ A) :
    IsExposed ℝ (cayleySum (A : Set (Fin d → ℝ)) (B : Set (Fin d → ℝ)))
        (segment ℝ (withLast x 0) (withLast y 0)) ↔
      IsExposed ℝ (convexHull ℝ (A : Set (Fin d → ℝ))) (segment ℝ x y) := by
  have hsub_cay : ∀ z ∈ convexHull ℝ (A : Set (Fin d → ℝ)),
      withLast z 0 ∈ cayleySum (A : Set (Fin d → ℝ)) (B : Set (Fin d → ℝ)) := by
    intro z hz
    have hmem : withLast z 0 ∈ (withLastZeroLinear d) '' convexHull ℝ (A : Set (Fin d → ℝ)) :=
      ⟨z, hz, rfl⟩
    rw [(withLastZeroLinear d).image_convexHull] at hmem
    exact convexHull_mono Set.subset_union_left hmem
  constructor
  · intro hExp _
    obtain ⟨l, hl⟩ := hExp ⟨withLast x 0, left_mem_segment ℝ _ _⟩
    obtain ⟨c, γ, hcγ⟩ := dual_withLast l
    have hx_mem : withLast x 0 ∈ {u ∈ cayleySum (A : Set _) (B : Set _) |
        ∀ v ∈ cayleySum (A : Set _) (B : Set _), l v ≤ l u} :=
      hl ▸ left_mem_segment ℝ _ _
    refine ⟨mkDual c, ?_⟩
    ext z
    simp only [mkDual_apply]
    change z ∈ segment ℝ x y ↔
      z ∈ convexHull ℝ (A : Set _) ∧ ∀ w ∈ convexHull ℝ (A : Set _), c ⬝ᵥ w ≤ c ⬝ᵥ z
    constructor
    · intro hz
      have hz_seg : withLast z 0 ∈ segment ℝ (withLast x 0) (withLast y 0) := by
        rw [← image_withLastZero_segment]
        exact ⟨z, hz, rfl⟩
      have hz_max : withLast z 0 ∈ {u ∈ cayleySum (A : Set _) (B : Set _) |
          ∀ v ∈ cayleySum (A : Set _) (B : Set _), l v ≤ l u} := hl ▸ hz_seg
      refine ⟨segment_subset_convexHull (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hz,
        fun w hw => ?_⟩
      have hle := hz_max.2 (withLast w 0) (hsub_cay w hw)
      rw [hcγ, hcγ] at hle
      linarith
    · rintro ⟨hz_hull, hz_max⟩
      have hxz : c ⬝ᵥ x ≤ c ⬝ᵥ z := hz_max x (subset_convexHull ℝ _ hx)
      have hz_seg : withLast z 0 ∈ segment ℝ (withLast x 0) (withLast y 0) := by
        rw [hl]
        refine ⟨hsub_cay z hz_hull, fun v hv => ?_⟩
        calc l v ≤ l (withLast x 0) := hx_mem.2 v hv
          _ ≤ l (withLast z 0) := by rw [hcγ, hcγ]; linarith
      rw [← image_withLastZero_segment] at hz_seg
      rcases hz_seg with ⟨z', hz', heq⟩
      rwa [← withLast_inj_left heq]
  · intro hExp _
    classical
    obtain ⟨l₀, hl₀⟩ := hExp ⟨x, left_mem_segment ℝ x y⟩
    obtain ⟨c, hc⟩ := dual_eq_dot l₀
    have hseg_A : segment ℝ x y =
        exposedFace (convexHull ℝ (A : Set (Fin d → ℝ))) (fun z => c ⬝ᵥ z) := by
      rw [hl₀]; ext z; simp [exposedFace, hc]
    have hx_face : x ∈ exposedFace (convexHull ℝ (A : Set (Fin d → ℝ))) (fun z => c ⬝ᵥ z) := by
      rw [← hseg_A]
      exact left_mem_segment ℝ x y
    rw [ZeroOneExpansion.fact_2 A hA c] at hseg_A
    have hA_le_x : ∀ a ∈ A, c ⬝ᵥ a ≤ c ⬝ᵥ x :=
      fun a ha => hx_face.2 a (subset_convexHull ℝ _ ha)
    obtain ⟨b_max, hb_max, hB_le⟩ := B.exists_max_image (fun b => c ⬝ᵥ b) hB
    let γ : ℝ := c ⬝ᵥ x - c ⬝ᵥ b_max - 1
    let c' : Fin (d + 1) → ℝ := withLast c γ
    let X : Finset (Fin (d + 1) → ℝ) :=
      A.image (fun a => withLast a 0) ∪ B.image (fun b => withLast b 1)
    have hX_coe : (X : Set (Fin (d + 1) → ℝ)) =
        (fun a => withLast a 0) '' (A : Set _) ∪ (fun b => withLast b 1) '' (B : Set _) := by
      simp [X, Finset.coe_union, Finset.coe_image]
    have hX_ne : X.Nonempty :=
      ⟨withLast x 0, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)⟩
    refine ⟨mkDual c', ?_⟩
    have hexp : {u ∈ cayleySum (A : Set _) (B : Set _) |
        ∀ v ∈ cayleySum (A : Set _) (B : Set _), mkDual c' v ≤ mkDual c' u} =
        exposedFace (convexHull ℝ (X : Set (Fin (d + 1) → ℝ))) (fun u => c' ⬝ᵥ u) := by
      rw [cayleySum, ← hX_coe]
      ext u; simp [exposedFace, mkDual_apply]
    rw [hexp, ZeroOneExpansion.fact_2 X hX_ne c']
    have hX_le : ∀ z ∈ X, c' ⬝ᵥ z ≤ c ⬝ᵥ x := by
      intro z hz
      simp only [X, Finset.mem_union, Finset.mem_image] at hz
      rcases hz with ⟨a, haA, rfl⟩ | ⟨b, hbB, rfl⟩
      · simpa [c', dot_withLast] using hA_le_x a haA
      · have := hB_le b hbB
        simp only [c', γ, dot_withLast, mul_one]
        linarith
    have hset : {u | u ∈ X ∧ ∀ z ∈ X, c' ⬝ᵥ z ≤ c' ⬝ᵥ u} =
        (fun a => withLast a 0) '' {a | a ∈ A ∧ ∀ a' ∈ A, c ⬝ᵥ a' ≤ c ⬝ᵥ a} := by
      ext u
      simp only [Set.mem_image]
      change (u ∈ X ∧ ∀ z ∈ X, c' ⬝ᵥ z ≤ c' ⬝ᵥ u) ↔
        ∃ a, (a ∈ A ∧ ∀ a' ∈ A, c ⬝ᵥ a' ≤ c ⬝ᵥ a) ∧ withLast a 0 = u
      constructor
      · rintro ⟨huX, humax⟩
        have hge : c ⬝ᵥ x ≤ c' ⬝ᵥ u := by
          have := humax (withLast x 0) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx))
          simpa [c', dot_withLast] using this
        simp only [X, Finset.mem_union, Finset.mem_image] at huX
        rcases huX with ⟨a, haA, rfl⟩ | ⟨b, hbB, rfl⟩
        · refine ⟨a, ⟨haA, fun a' ha' => ?_⟩, rfl⟩
          have := humax (withLast a' 0) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha'))
          simpa [c', dot_withLast] using this
        · exfalso
          have hb_bound := hB_le b hbB
          simp only [c', γ, dot_withLast, mul_one] at hge
          linarith
      · rintro ⟨a, ⟨haA, hamax⟩, rfl⟩
        refine ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ haA), fun z hz => ?_⟩
        have hxa : c ⬝ᵥ x ≤ c ⬝ᵥ a := hamax x hx
        have hzx := hX_le z hz
        simp only [c', dot_withLast, mul_zero, add_zero]
        linarith
    rw [hset]
    have himg := (withLastZeroLinear d).image_convexHull {a | a ∈ A ∧ ∀ a' ∈ A, c ⬝ᵥ a' ≤ c ⬝ᵥ a}
    change _ = convexHull ℝ ((withLastZeroLinear d) '' _)
    rw [← himg, ← hseg_A]
    exact (image_withLastZero_segment x y).symm

lemma isExposed_cayleySum_upper_segment {d : ℕ} (A B : Finset (Fin d → ℝ))
    (hA : A.Nonempty) (hB : B.Nonempty) {x y : Fin d → ℝ} (hx : x ∈ B) (hy : y ∈ B) :
    IsExposed ℝ (cayleySum (A : Set (Fin d → ℝ)) (B : Set (Fin d → ℝ)))
        (segment ℝ (withLast x 1) (withLast y 1)) ↔
      IsExposed ℝ (convexHull ℝ (B : Set (Fin d → ℝ))) (segment ℝ x y) := by
  have hsub_cay : ∀ z ∈ convexHull ℝ (B : Set (Fin d → ℝ)),
      withLast z 1 ∈ cayleySum (A : Set (Fin d → ℝ)) (B : Set (Fin d → ℝ)) := by
    intro z hz
    have hmem : withLast z 1 ∈ (withLastOneAffine d) '' convexHull ℝ (B : Set (Fin d → ℝ)) :=
      ⟨z, hz, rfl⟩
    rw [(withLastOneAffine d).image_convexHull] at hmem
    exact convexHull_mono Set.subset_union_right hmem
  constructor
  · intro hExp _
    obtain ⟨l, hl⟩ := hExp ⟨withLast x 1, left_mem_segment ℝ _ _⟩
    obtain ⟨c, γ, hcγ⟩ := dual_withLast l
    have hx_mem : withLast x 1 ∈ {u ∈ cayleySum (A : Set _) (B : Set _) |
        ∀ v ∈ cayleySum (A : Set _) (B : Set _), l v ≤ l u} :=
      hl ▸ left_mem_segment ℝ _ _
    refine ⟨mkDual c, ?_⟩
    ext z
    simp only [mkDual_apply]
    change z ∈ segment ℝ x y ↔
      z ∈ convexHull ℝ (B : Set _) ∧ ∀ w ∈ convexHull ℝ (B : Set _), c ⬝ᵥ w ≤ c ⬝ᵥ z
    constructor
    · intro hz
      have hz_seg : withLast z 1 ∈ segment ℝ (withLast x 1) (withLast y 1) := by
        rw [← image_withLastOne_segment]
        exact ⟨z, hz, rfl⟩
      have hz_max : withLast z 1 ∈ {u ∈ cayleySum (A : Set _) (B : Set _) |
          ∀ v ∈ cayleySum (A : Set _) (B : Set _), l v ≤ l u} := hl ▸ hz_seg
      refine ⟨segment_subset_convexHull (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hz,
        fun w hw => ?_⟩
      have hle := hz_max.2 (withLast w 1) (hsub_cay w hw)
      rw [hcγ, hcγ] at hle
      linarith
    · rintro ⟨hz_hull, hz_max⟩
      have hxz : c ⬝ᵥ x ≤ c ⬝ᵥ z := hz_max x (subset_convexHull ℝ _ hx)
      have hz_seg : withLast z 1 ∈ segment ℝ (withLast x 1) (withLast y 1) := by
        rw [hl]
        refine ⟨hsub_cay z hz_hull, fun v hv => ?_⟩
        calc l v ≤ l (withLast x 1) := hx_mem.2 v hv
          _ ≤ l (withLast z 1) := by rw [hcγ, hcγ]; linarith
      rw [← image_withLastOne_segment] at hz_seg
      rcases hz_seg with ⟨z', hz', heq⟩
      rwa [← withLast_inj_left heq]
  · intro hExp _
    classical
    obtain ⟨l₀, hl₀⟩ := hExp ⟨x, left_mem_segment ℝ x y⟩
    obtain ⟨c, hc⟩ := dual_eq_dot l₀
    have hseg_B : segment ℝ x y =
        exposedFace (convexHull ℝ (B : Set (Fin d → ℝ))) (fun z => c ⬝ᵥ z) := by
      rw [hl₀]; ext z; simp [exposedFace, hc]
    have hx_face : x ∈ exposedFace (convexHull ℝ (B : Set (Fin d → ℝ))) (fun z => c ⬝ᵥ z) := by
      rw [← hseg_B]
      exact left_mem_segment ℝ x y
    rw [ZeroOneExpansion.fact_2 B hB c] at hseg_B
    have hB_le_x : ∀ b ∈ B, c ⬝ᵥ b ≤ c ⬝ᵥ x :=
      fun b hb => hx_face.2 b (subset_convexHull ℝ _ hb)
    obtain ⟨a_max, ha_max, hA_le⟩ := A.exists_max_image (fun a => c ⬝ᵥ a) hA
    let γ : ℝ := c ⬝ᵥ a_max - c ⬝ᵥ x + 1
    let c' : Fin (d + 1) → ℝ := withLast c γ
    let X : Finset (Fin (d + 1) → ℝ) :=
      A.image (fun a => withLast a 0) ∪ B.image (fun b => withLast b 1)
    have hX_coe : (X : Set (Fin (d + 1) → ℝ)) =
        (fun a => withLast a 0) '' (A : Set _) ∪ (fun b => withLast b 1) '' (B : Set _) := by
      simp [X, Finset.coe_union, Finset.coe_image]
    have hX_ne : X.Nonempty :=
      ⟨withLast x 1, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)⟩
    refine ⟨mkDual c', ?_⟩
    have hexp : {u ∈ cayleySum (A : Set _) (B : Set _) |
        ∀ v ∈ cayleySum (A : Set _) (B : Set _), mkDual c' v ≤ mkDual c' u} =
        exposedFace (convexHull ℝ (X : Set (Fin (d + 1) → ℝ))) (fun u => c' ⬝ᵥ u) := by
      rw [cayleySum, ← hX_coe]
      ext u; simp [exposedFace, mkDual_apply]
    rw [hexp, ZeroOneExpansion.fact_2 X hX_ne c']
    have hX_le : ∀ z ∈ X, c' ⬝ᵥ z ≤ c ⬝ᵥ x + γ := by
      intro z hz
      simp only [X, Finset.mem_union, Finset.mem_image] at hz
      rcases hz with ⟨a, haA, rfl⟩ | ⟨b, hbB, rfl⟩
      · have := hA_le a haA
        simp only [c', γ, dot_withLast, mul_zero, add_zero]
        linarith
      · have := hB_le_x b hbB
        simp only [c', dot_withLast, mul_one]
        linarith
    have hset : {u | u ∈ X ∧ ∀ z ∈ X, c' ⬝ᵥ z ≤ c' ⬝ᵥ u} =
        (fun b => withLast b 1) '' {b | b ∈ B ∧ ∀ b' ∈ B, c ⬝ᵥ b' ≤ c ⬝ᵥ b} := by
      ext u
      simp only [Set.mem_image]
      change (u ∈ X ∧ ∀ z ∈ X, c' ⬝ᵥ z ≤ c' ⬝ᵥ u) ↔
        ∃ b, (b ∈ B ∧ ∀ b' ∈ B, c ⬝ᵥ b' ≤ c ⬝ᵥ b) ∧ withLast b 1 = u
      constructor
      · rintro ⟨huX, humax⟩
        have hge : c ⬝ᵥ x + γ ≤ c' ⬝ᵥ u := by
          have := humax (withLast x 1) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
          simpa [c', dot_withLast] using this
        simp only [X, Finset.mem_union, Finset.mem_image] at huX
        rcases huX with ⟨a, haA, rfl⟩ | ⟨b, hbB, rfl⟩
        · exfalso
          have ha_bound := hA_le a haA
          simp only [c', γ, dot_withLast, mul_zero, add_zero] at hge
          linarith
        · refine ⟨b, ⟨hbB, fun b' hb' => ?_⟩, rfl⟩
          have := humax (withLast b' 1) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb'))
          simp only [c', dot_withLast, mul_one] at this
          linarith
      · rintro ⟨b, ⟨hbB, hbmax⟩, rfl⟩
        refine ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hbB), fun z hz => ?_⟩
        have hxb : c ⬝ᵥ x ≤ c ⬝ᵥ b := hbmax x hx
        have hzx := hX_le z hz
        simp only [c', dot_withLast, mul_one]
        linarith
    rw [hset]
    have himg := (withLastOneAffine d).image_convexHull {b | b ∈ B ∧ ∀ b' ∈ B, c ⬝ᵥ b' ≤ c ⬝ᵥ b}
    change _ = convexHull ℝ ((withLastOneAffine d) '' _)
    rw [← himg, ← hseg_B]
    exact (image_withLastOne_segment x y).symm

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
        push_neg at ht_neg
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
        push_neg at ht_gt
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

lemma isExposed_image_cle {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    (e : E₁ ≃L[ℝ] E₂) (P F : Set E₁) :
    IsExposed ℝ (e '' P) (e '' F) ↔ IsExposed ℝ P F := by
  constructor
  · intro hExp hFne
    obtain ⟨l₂, hl₂⟩ := hExp (hFne.image e)
    refine ⟨l₂.comp e.toContinuousLinearMap, ?_⟩
    ext x
    constructor
    · intro hx
      have hex : e x ∈ {u ∈ e '' P | ∀ v ∈ e '' P, l₂ v ≤ l₂ u} := hl₂ ▸ ⟨x, hx, rfl⟩
      rcases hex.1 with ⟨x', hx'P, heq⟩
      rw [e.injective heq] at hx'P
      exact ⟨hx'P, fun y hy => hex.2 (e y) ⟨y, hy, rfl⟩⟩
    · rintro ⟨hxP, hmax⟩
      have hex : e x ∈ e '' F := by
        rw [hl₂]
        refine ⟨⟨x, hxP, rfl⟩, ?_⟩
        rintro _ ⟨y, hyP, rfl⟩
        exact hmax y hyP
      rcases hex with ⟨x', hx'F, heq⟩
      rwa [← e.injective heq]
  · intro hExp hFne
    rcases hFne with ⟨_, x, hxF, rfl⟩
    obtain ⟨l₁, hl₁⟩ := hExp ⟨x, hxF⟩
    refine ⟨l₁.comp e.symm.toContinuousLinearMap, ?_⟩
    ext u
    constructor
    · rintro ⟨x', hx'F, rfl⟩
      have hx' : x' ∈ {z ∈ P | ∀ y ∈ P, l₁ y ≤ l₁ z} := hl₁ ▸ hx'F
      refine ⟨⟨x', hx'.1, rfl⟩, ?_⟩
      rintro _ ⟨y, hyP, rfl⟩
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, e.symm_apply_apply]
      exact hx'.2 y hyP
    · rintro ⟨⟨x', hx'P, rfl⟩, hmax⟩
      refine ⟨x', ?_, rfl⟩
      rw [hl₁]
      refine ⟨hx'P, fun y hyP => ?_⟩
      have := hmax (e y) ⟨y, hyP, rfl⟩
      simpa using this

lemma finrank_direction_image_cle {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    (e : E₁ ≃L[ℝ] E₂) (F : Set E₁) :
    Module.finrank ℝ (affineSpan ℝ (e '' F)).direction =
      Module.finrank ℝ (affineSpan ℝ F).direction := by
  have hdir : (affineSpan ℝ (e '' F)).direction =
      Submodule.map (e.toLinearEquiv : E₁ →ₗ[ℝ] E₂) (affineSpan ℝ F).direction := by
    rw [direction_affineSpan, direction_affineSpan]
    apply le_antisymm
    · rw [vectorSpan_def, Submodule.span_le]
      rintro w ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨u -ᵥ v, vsub_mem_vectorSpan ℝ hu hv, ?_⟩
      simp [vsub_eq_sub, map_sub]
    · rw [Submodule.map_le_iff_le_comap, vectorSpan_def, Submodule.span_le]
      rintro w ⟨u, hu, v, hv, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      have heq : (e.toLinearEquiv : E₁ →ₗ[ℝ] E₂) (u -ᵥ v) = e u -ᵥ e v := by
        simp [vsub_eq_sub, map_sub]
      rw [heq]
      exact vsub_mem_vectorSpan ℝ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  rw [hdir, LinearEquiv.finrank_map_eq]

lemma isAdj_image_cle {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    (e : E₁ ≃L[ℝ] E₂) (P : Set E₁) (x y : E₁) :
    IsAdj (e '' P) (e x) (e y) ↔ IsAdj P x y := by
  have hvx : IsVertexOf (e '' P) (e x) ↔ IsVertexOf P x := by
    simpa [IsVertexOf] using isExposed_image_cle e P {x}
  have hvy : IsVertexOf (e '' P) (e y) ↔ IsVertexOf P y := by
    simpa [IsVertexOf] using isExposed_image_cle e P {y}
  constructor
  · rintro ⟨hne, hex, hey, F₂, hF₂exp, hF₂dim, hxF₂, hyF₂⟩
    have hxy : x ≠ y := fun h => hne (by rw [h])
    let F₁ := e.symm '' F₂
    have himg : e '' F₁ = F₂ := by
      ext u; simp [F₁]
    have hF₁exp : IsExposed ℝ P F₁ := by
      rw [← isExposed_image_cle e P F₁, himg]
      exact hF₂exp
    have hF₁dim : Module.finrank ℝ (affineSpan ℝ F₁).direction = 1 := by
      rw [← finrank_direction_image_cle e F₁, himg]
      exact hF₂dim
    exact ⟨hxy, hvx.mp hex, hvy.mp hey, F₁, hF₁exp, hF₁dim,
      ⟨e x, hxF₂, e.symm_apply_apply x⟩, ⟨e y, hyF₂, e.symm_apply_apply y⟩⟩
  · rintro ⟨hxy, hex, hey, F₁, hF₁exp, hF₁dim, hxF₁, hyF₁⟩
    refine ⟨e.injective.ne hxy, hvx.mpr hex, hvy.mpr hey, e '' F₁,
      (isExposed_image_cle e P F₁).mpr hF₁exp, ?_, ⟨x, hxF₁, rfl⟩, ⟨y, hyF₁, rfl⟩⟩
    rw [finrank_direction_image_cle]
    exact hF₁dim

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

def fin2nEquiv (n : ℕ) : Fin (2 * n) ≃ Fin n ⊕ Fin n where
  toFun idx :=
    if h : idx.val < n then Sum.inl ⟨idx.val, h⟩
    else Sum.inr ⟨idx.val - n, by omega⟩
  invFun
    | Sum.inl i => ⟨i.val, by omega⟩
    | Sum.inr j => ⟨n + j.val, by omega⟩
  left_inv idx := by
    by_cases h : idx.val < n
    · simp [h]
    · simp only [h, ↓reduceDIte]
      ext; simp; omega
  right_inv b := by
    rcases b with i | j
    · simp [i.isLt]
    · have h : ¬ (n + j.val < n) := by omega
      simp [h]

def prodLinEquiv (n : ℕ) : (Fin (4 * n) → ℝ) ≃ₗ[ℝ] (Fin (2 * n) → Fin 2 → ℝ) where
  toFun x idx := blk n x (fin2nEquiv n idx)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := mkBlocks n (fun b => y ((fin2nEquiv n).symm b))
  left_inv x := by
    simp only [Equiv.apply_symm_apply]
    exact mkBlocks_blk n x
  right_inv y := by
    funext idx
    simp [blk_mkBlocks]

noncomputable def prodCLE (n : ℕ) : (Fin (4 * n) → ℝ) ≃L[ℝ] (Fin (2 * n) → Fin 2 → ℝ) :=
  (prodLinEquiv n).toContinuousLinearEquiv

@[simp]
lemma prodCLE_apply (n : ℕ) (x : Fin (4 * n) → ℝ) (idx : Fin (2 * n)) :
    prodCLE n x idx = blk n x (fin2nEquiv n idx) := rfl

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

lemma Xn_zeroOne (n : ℕ) (x : Fin (4 * n) → ℝ) (hx : x ∈ Xn n) (k : Fin (4 * n)) :
    x k = 0 ∨ x k = 1 := by
  rw [← mkBlocks_blk n x]
  simp only [mkBlocks]
  rcases h : (unBlockIdx n k).1 with i | j
  · have hm := (hx i).1
    rw [← range_cMap] at hm
    rcases hm with ⟨a, ha⟩
    rw [← ha]
    exact cMap_bit a _
  · have hm := (hx j).2
    rw [← range_dMap] at hm
    rcases hm with ⟨b, hb⟩
    rw [← hb]
    exact dMap_bit b _

lemma Yn_zeroOne (n : ℕ) (y : Fin (4 * n) → ℝ) (hy : y ∈ Yn n) (k : Fin (4 * n)) :
    y k = 0 ∨ y k = 1 := by
  rw [← mkBlocks_blk n y]
  simp only [mkBlocks]
  rcases h : (unBlockIdx n k).1 with i | j
  · have hm := (hy i).1
    rw [← range_dMap] at hm
    rcases hm with ⟨b, hb⟩
    rw [← hb]
    exact dMap_bit b _
  · have hm := (hy j).2
    rw [← range_cMap] at hm
    rcases hm with ⟨a, ha⟩
    rw [← ha]
    exact cMap_bit a _

lemma vertices_Pn_mem_Vn (n : ℕ) {u : Fin (4 * n + 1) → ℝ} (hu : IsVertexOf (Pn n) u) :
    u ∈ Vn n := by
  classical
  let X : Finset (Fin (4 * n + 1) → ℝ) :=
    (Xn_fin n).image (fun x => withLast x 0) ∪ (Yn_fin n).image (fun y => withLast y 1)
  have hX_coe : (X : Set (Fin (4 * n + 1) → ℝ)) = Vn n := by
    simp [X, Vn, Finset.coe_union, Finset.coe_image, coe_Xn_fin, coe_Yn_fin]
  have h0_mem : (0 : Fin (4 * n) → ℝ) ∈ Xn n := by
    intro i
    have hz : (0 : Fin 2 → ℝ) = ![0, 0] := by ext j; fin_cases j <;> rfl
    constructor <;> (change (0 : Fin 2 → ℝ) ∈ _; rw [hz])
    · simp [C]
    · simp [D]
  have h0_fin : (0 : Fin (4 * n) → ℝ) ∈ Xn_fin n := by
    rw [← Finset.mem_coe, coe_Xn_fin]; exact h0_mem
  have hX_ne : X.Nonempty :=
    ⟨withLast 0 0, Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0_fin)⟩
  have hPn : Pn n = convexHull ℝ (X : Set (Fin (4 * n + 1) → ℝ)) := by
    rw [Pn, cayleySum, ← Vn, hX_coe]
  have h01 : ∀ v ∈ X, ∀ k, v k = 0 ∨ v k = 1 := by
    intro v hv k
    simp only [X, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
    · refine Fin.lastCases ?_ (fun m => ?_) k
      · simp [withLast]
      · simp only [withLast, Fin.snoc_castSucc]
        exact Xn_zeroOne n x (by rw [← coe_Xn_fin]; exact hx) m
    · refine Fin.lastCases ?_ (fun m => ?_) k
      · simp [withLast]
      · simp only [withLast, Fin.snoc_castSucc]
        exact Yn_zeroOne n y (by rw [← coe_Yn_fin]; exact hy) m
  have hfact3 := ZeroOneExpansion.fact_3 X hX_ne h01
  have hu' : u ∈ {z | IsVertexOf (convexHull ℝ (X : Set _)) z} := by
    rwa [← hPn]
  rw [hfact3, hX_coe] at hu'
  exact hu'

lemma isPolytope_Qsq : IsPolytope Qsq := by
  classical
  refine ⟨Finset.univ.image cMap, ⟨cMap 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_⟩
  simp [Qsq, Finset.coe_image, range_cMap]

lemma isPolytope_Delta : IsPolytope Delta := by
  classical
  refine ⟨Finset.univ.image dMap, ⟨dMap 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_⟩
  simp [Delta, Finset.coe_image, range_dMap]

lemma blk_prodCLE_symm (n : ℕ) (y : Fin (2 * n) → Fin 2 → ℝ) (b : Fin n ⊕ Fin n) :
    blk n ((prodCLE n).symm y) b = y ((fin2nEquiv n).symm b) := by
  have h := congr_fun ((prodCLE n).apply_symm_apply y) ((fin2nEquiv n).symm b)
  simpa [prodCLE_apply] using h

lemma image_prodCLE_Xn (n : ℕ) :
    prodCLE n '' convexHull ℝ (Xn n) =
      Set.univ.pi (fun idx : Fin (2 * n) =>
        Sum.elim (fun _ : Fin n => Qsq) (fun _ : Fin n => Delta) (fin2nEquiv n idx)) := by
  have himg_set : prodCLE n '' Xn n =
      Set.univ.pi (fun idx : Fin (2 * n) =>
        Sum.elim (fun _ : Fin n => C) (fun _ : Fin n => D) (fin2nEquiv n idx)) := by
    ext y
    simp only [Set.mem_image, Set.mem_univ_pi]
    constructor
    · rintro ⟨x, hx, rfl⟩ idx
      rcases h : fin2nEquiv n idx with i | j
      · simpa [h] using (hx i).1
      · simpa [h] using (hx j).2
    · intro hy
      refine ⟨(prodCLE n).symm y, ?_, (prodCLE n).apply_symm_apply y⟩
      intro i
      rw [blk_prodCLE_symm, blk_prodCLE_symm]
      have h1 := hy ((fin2nEquiv n).symm (Sum.inl i))
      have h2 := hy ((fin2nEquiv n).symm (Sum.inr i))
      simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr] at h1 h2
      exact ⟨h1, h2⟩
  have hlin : prodCLE n '' convexHull ℝ (Xn n) = convexHull ℝ (prodCLE n '' Xn n) :=
    (prodLinEquiv n).toLinearMap.image_convexHull (Xn n)
  rw [hlin, himg_set, convexHull_pi]
  ext y
  simp only [Set.mem_univ_pi]
  refine forall_congr' fun idx => ?_
  rcases fin2nEquiv n idx with i | j <;> rfl

lemma image_prodCLE_Yn (n : ℕ) :
    prodCLE n '' convexHull ℝ (Yn n) =
      Set.univ.pi (fun idx : Fin (2 * n) =>
        Sum.elim (fun _ : Fin n => Delta) (fun _ : Fin n => Qsq) (fin2nEquiv n idx)) := by
  have himg_set : prodCLE n '' Yn n =
      Set.univ.pi (fun idx : Fin (2 * n) =>
        Sum.elim (fun _ : Fin n => D) (fun _ : Fin n => C) (fin2nEquiv n idx)) := by
    ext y
    simp only [Set.mem_image, Set.mem_univ_pi]
    constructor
    · rintro ⟨x, hx, rfl⟩ idx
      rcases h : fin2nEquiv n idx with i | j
      · simpa [h] using (hx i).1
      · simpa [h] using (hx j).2
    · intro hy
      refine ⟨(prodCLE n).symm y, ?_, (prodCLE n).apply_symm_apply y⟩
      intro i
      rw [blk_prodCLE_symm, blk_prodCLE_symm]
      have h1 := hy ((fin2nEquiv n).symm (Sum.inl i))
      have h2 := hy ((fin2nEquiv n).symm (Sum.inr i))
      simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr] at h1 h2
      exact ⟨h1, h2⟩
  have hlin : prodCLE n '' convexHull ℝ (Yn n) = convexHull ℝ (prodCLE n '' Yn n) :=
    (prodLinEquiv n).toLinearMap.image_convexHull (Yn n)
  rw [hlin, himg_set, convexHull_pi]
  ext y
  simp only [Set.mem_univ_pi]
  refine forall_congr' fun idx => ?_
  rcases fin2nEquiv n idx with i | j <;> rfl

end Aux_ZOE_lemma8

open ZeroOneExpansion Aux_ZOE_lemma8

theorem solution (n : ℕ) (hn : 1 ≤ n) (u v : Fin (4 * n + 1) → ℝ)
    (hu : IsVertexOf (Pn n) u) (hv : IsVertexOf (Pn n) v) (huv : u ≠ v)
    (ht : layer n u = layer n v) :
    (layer n u = 0 →
      (IsExposed ℝ (Pn n) (segment ℝ u v) ↔
        ∃ k : Fin n ⊕ Fin n, (∀ k', k' ≠ k → ublk n u k' = ublk n v k') ∧
          IsAdj (Sum.elim (fun _ : Fin n => Qsq) (fun _ : Fin n => Delta) k)
            (ublk n u k) (ublk n v k))) ∧
    (layer n u = 1 →
      (IsExposed ℝ (Pn n) (segment ℝ u v) ↔
        ∃ k : Fin n ⊕ Fin n, (∀ k', k' ≠ k → ublk n u k' = ublk n v k') ∧
          IsAdj (Sum.elim (fun _ : Fin n => Delta) (fun _ : Fin n => Qsq) k)
            (ublk n u k) (ublk n v k))) := by
  have huV := vertices_Pn_mem_Vn n hu
  have hvV := vertices_Pn_mem_Vn n hv
  have h0Y : (0 : Fin (4 * n) → ℝ) ∈ Yn_fin n := by
    rw [← Finset.mem_coe, coe_Yn_fin]
    intro i
    have hz : (0 : Fin 2 → ℝ) = ![0, 0] := by ext j; fin_cases j <;> rfl
    constructor <;> (change (0 : Fin 2 → ℝ) ∈ _; rw [hz])
    · simp [D]
    · simp [C]
  have h0X : (0 : Fin (4 * n) → ℝ) ∈ Xn_fin n := by
    rw [← Finset.mem_coe, coe_Xn_fin]
    intro i
    have hz : (0 : Fin 2 → ℝ) = ![0, 0] := by ext j; fin_cases j <;> rfl
    constructor <;> (change (0 : Fin 2 → ℝ) ∈ _; rw [hz])
    · simp [C]
    · simp [D]
  have hPn_coe : Pn n = cayleySum (Xn_fin n : Set _) (Yn_fin n : Set _) := by
    rw [Pn, coe_Xn_fin, coe_Yn_fin]
  constructor
  · intro hlu0
    have hlv0 : layer n v = 0 := ht ▸ hlu0
    obtain ⟨xu, hxu, rfl⟩ : ∃ x ∈ Xn n, withLast x 0 = u := by
      rcases huV with ⟨x, hx, rfl⟩ | ⟨y, _, rfl⟩
      · exact ⟨x, hx, rfl⟩
      · simp [layer, withLast] at hlu0
    obtain ⟨xv, hxv, rfl⟩ : ∃ x ∈ Xn n, withLast x 0 = v := by
      rcases hvV with ⟨x, hx, rfl⟩ | ⟨y, _, rfl⟩
      · exact ⟨x, hx, rfl⟩
      · simp [layer, withLast] at hlv0
    have hxuv : xu ≠ xv := fun h => huv (by rw [h])
    have hxu_fin : xu ∈ Xn_fin n := by rw [← Finset.mem_coe, coe_Xn_fin]; exact hxu
    have hxv_fin : xv ∈ Xn_fin n := by rw [← Finset.mem_coe, coe_Xn_fin]; exact hxv
    rw [hPn_coe, isExposed_cayleySum_lower_segment (Xn_fin n) (Yn_fin n)
      ⟨xu, hxu_fin⟩ ⟨0, h0Y⟩ hxu_fin hxv_fin, coe_Xn_fin]
    have hverts_X : {z | IsVertexOf (convexHull ℝ (Xn n)) z} = Xn n := by
      rw [← coe_Xn_fin]
      exact ZeroOneExpansion.fact_3 (Xn_fin n) ⟨xu, hxu_fin⟩
        (fun z hz k => Xn_zeroOne n z (by rw [← coe_Xn_fin]; exact hz) k)
    have hxu_vert : IsVertexOf (convexHull ℝ (Xn n)) xu := by
      change xu ∈ {z | IsVertexOf (convexHull ℝ (Xn n)) z}; rwa [hverts_X]
    have hxv_vert : IsVertexOf (convexHull ℝ (Xn n)) xv := by
      change xv ∈ {z | IsVertexOf (convexHull ℝ (Xn n)) z}; rwa [hverts_X]
    rw [isExposed_segment_iff_isAdj (convex_convexHull ℝ (Xn n)) hxu_vert hxv_vert hxuv]
    rw [← isAdj_image_cle (prodCLE n), image_prodCLE_Xn n]
    let P_low : Fin (2 * n) → Set (Fin 2 → ℝ) := fun idx =>
      Sum.elim (fun _ : Fin n => Qsq) (fun _ : Fin n => Delta) (fin2nEquiv n idx)
    have hP_low : ∀ idx, IsPolytope (P_low idx) := by
      intro idx
      dsimp only [P_low]
      rcases fin2nEquiv n idx with i | j
      · exact isPolytope_Qsq
      · exact isPolytope_Delta
    have hex_vert : IsVertexOf (Set.univ.pi P_low) (prodCLE n xu) := by
      have : IsVertexOf (prodCLE n '' convexHull ℝ (Xn n)) (prodCLE n xu) := by
        simpa [IsVertexOf] using (isExposed_image_cle (prodCLE n) (convexHull ℝ (Xn n)) {xu}).mpr hxu_vert
      rwa [image_prodCLE_Xn n] at this
    have hev_vert : IsVertexOf (Set.univ.pi P_low) (prodCLE n xv) := by
      have : IsVertexOf (prodCLE n '' convexHull ℝ (Xn n)) (prodCLE n xv) := by
        simpa [IsVertexOf] using (isExposed_image_cle (prodCLE n) (convexHull ℝ (Xn n)) {xv}).mpr hxv_vert
      rwa [image_prodCLE_Xn n] at this
    have hf5 := (ZeroOneExpansion.fact_5 (2 * n) (by omega) (fun _ => 2) P_low hP_low).2.2
      (prodCLE n xu) (prodCLE n xv) hex_vert hev_vert ((prodCLE n).injective.ne hxuv)
    change IsAdj (Set.univ.pi P_low) (prodCLE n xu) (prodCLE n xv) ↔ _
    rw [hf5]
    constructor
    · rintro ⟨idx, hother, hadj⟩
      refine ⟨fin2nEquiv n idx, ?_, ?_⟩
      · intro k' hk'
        have hidx' : (fin2nEquiv n).symm k' ≠ idx := fun h => hk' (by rw [← h, Equiv.apply_symm_apply])
        have := hother ((fin2nEquiv n).symm k') hidx'
        simpa [ublk, withLast, Fin.init_snoc] using this
      · simpa [P_low, ublk, withLast, Fin.init_snoc] using hadj
    · rintro ⟨k, hother, hadj⟩
      refine ⟨(fin2nEquiv n).symm k, ?_, ?_⟩
      · intro idx' hidx'
        have hk' : fin2nEquiv n idx' ≠ k := fun h => hidx' (by rw [← h, Equiv.symm_apply_apply])
        have := hother (fin2nEquiv n idx') hk'
        simpa [ublk, withLast, Fin.init_snoc] using this
      · simpa [P_low, ublk, withLast, Fin.init_snoc] using hadj
  · intro hlu1
    have hlv1 : layer n v = 1 := ht ▸ hlu1
    obtain ⟨yu, hyu, rfl⟩ : ∃ y ∈ Yn n, withLast y 1 = u := by
      rcases huV with ⟨x, _, rfl⟩ | ⟨y, hy, rfl⟩
      · simp [layer, withLast] at hlu1
      · exact ⟨y, hy, rfl⟩
    obtain ⟨yv, hyv, rfl⟩ : ∃ y ∈ Yn n, withLast y 1 = v := by
      rcases hvV with ⟨x, _, rfl⟩ | ⟨y, hy, rfl⟩
      · simp [layer, withLast] at hlv1
      · exact ⟨y, hy, rfl⟩
    have hyuv : yu ≠ yv := fun h => huv (by rw [h])
    have hyu_fin : yu ∈ Yn_fin n := by rw [← Finset.mem_coe, coe_Yn_fin]; exact hyu
    have hyv_fin : yv ∈ Yn_fin n := by rw [← Finset.mem_coe, coe_Yn_fin]; exact hyv
    rw [hPn_coe, isExposed_cayleySum_upper_segment (Xn_fin n) (Yn_fin n)
      ⟨0, h0X⟩ ⟨yu, hyu_fin⟩ hyu_fin hyv_fin, coe_Yn_fin]
    have hverts_Y : {z | IsVertexOf (convexHull ℝ (Yn n)) z} = Yn n := by
      rw [← coe_Yn_fin]
      exact ZeroOneExpansion.fact_3 (Yn_fin n) ⟨yu, hyu_fin⟩
        (fun z hz k => Yn_zeroOne n z (by rw [← coe_Yn_fin]; exact hz) k)
    have hyu_vert : IsVertexOf (convexHull ℝ (Yn n)) yu := by
      change yu ∈ {z | IsVertexOf (convexHull ℝ (Yn n)) z}; rwa [hverts_Y]
    have hyv_vert : IsVertexOf (convexHull ℝ (Yn n)) yv := by
      change yv ∈ {z | IsVertexOf (convexHull ℝ (Yn n)) z}; rwa [hverts_Y]
    rw [isExposed_segment_iff_isAdj (convex_convexHull ℝ (Yn n)) hyu_vert hyv_vert hyuv]
    rw [← isAdj_image_cle (prodCLE n), image_prodCLE_Yn n]
    let P_high : Fin (2 * n) → Set (Fin 2 → ℝ) := fun idx =>
      Sum.elim (fun _ : Fin n => Delta) (fun _ : Fin n => Qsq) (fin2nEquiv n idx)
    have hP_high : ∀ idx, IsPolytope (P_high idx) := by
      intro idx
      dsimp only [P_high]
      rcases fin2nEquiv n idx with i | j
      · exact isPolytope_Delta
      · exact isPolytope_Qsq
    have hex_vert : IsVertexOf (Set.univ.pi P_high) (prodCLE n yu) := by
      have : IsVertexOf (prodCLE n '' convexHull ℝ (Yn n)) (prodCLE n yu) := by
        simpa [IsVertexOf] using (isExposed_image_cle (prodCLE n) (convexHull ℝ (Yn n)) {yu}).mpr hyu_vert
      rwa [image_prodCLE_Yn n] at this
    have hev_vert : IsVertexOf (Set.univ.pi P_high) (prodCLE n yv) := by
      have : IsVertexOf (prodCLE n '' convexHull ℝ (Yn n)) (prodCLE n yv) := by
        simpa [IsVertexOf] using (isExposed_image_cle (prodCLE n) (convexHull ℝ (Yn n)) {yv}).mpr hyv_vert
      rwa [image_prodCLE_Yn n] at this
    have hf5 := (ZeroOneExpansion.fact_5 (2 * n) (by omega) (fun _ => 2) P_high hP_high).2.2
      (prodCLE n yu) (prodCLE n yv) hex_vert hev_vert ((prodCLE n).injective.ne hyuv)
    change IsAdj (Set.univ.pi P_high) (prodCLE n yu) (prodCLE n yv) ↔ _
    rw [hf5]
    constructor
    · rintro ⟨idx, hother, hadj⟩
      refine ⟨fin2nEquiv n idx, ?_, ?_⟩
      · intro k' hk'
        have hidx' : (fin2nEquiv n).symm k' ≠ idx := fun h => hk' (by rw [← h, Equiv.apply_symm_apply])
        have := hother ((fin2nEquiv n).symm k') hidx'
        simpa [ublk, withLast, Fin.init_snoc] using this
      · simpa [P_high, ublk, withLast, Fin.init_snoc] using hadj
    · rintro ⟨k, hother, hadj⟩
      refine ⟨(fin2nEquiv n).symm k, ?_, ?_⟩
      · intro idx' hidx'
        have hk' : fin2nEquiv n idx' ≠ k := fun h => hidx' (by rw [← h, Equiv.symm_apply_apply])
        have := hother (fin2nEquiv n idx') hk'
        simpa [ublk, withLast, Fin.init_snoc] using this
      · simpa [P_high, ublk, withLast, Fin.init_snoc] using hadj
