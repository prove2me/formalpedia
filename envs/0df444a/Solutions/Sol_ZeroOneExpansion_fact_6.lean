-- Prove2me | solution 1 for ZeroOneExpansion.fact_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:38:25.729615+00:00
-- url     : https://prove2.me/submissions/a4e4a055-6f4c-4882-a219-1a2024ac016d

import Mathlib
import Definitions.Def_ZeroOneExpansion_cayleySum
import Theorems.Thm_ZeroOneExpansion_fact_2

set_option autoImplicit false

namespace Aux_ZOE_fact6

open ZeroOneExpansion Matrix

lemma withLast_last {d : ℕ} (x : Fin d → ℝ) (t : ℝ) :
    withLast x t (Fin.last d) = t := by
  simp [withLast]

lemma withLast_castSucc {d : ℕ} (x : Fin d → ℝ) (t : ℝ) (i : Fin d) :
    withLast x t i.castSucc = x i := by
  simp [withLast]

lemma withLast_inj_left {d : ℕ} {x y : Fin d → ℝ} {t : ℝ}
    (h : withLast x t = withLast y t) : x = y := by
  ext i
  have := congr_fun h i.castSucc
  simpa [withLast] using this

lemma dot_withLast {d : ℕ} (w x : Fin d → ℝ) (γ t : ℝ) :
    withLast w γ ⬝ᵥ withLast x t = w ⬝ᵥ x + γ * t := by
  simp [dotProduct, Fin.sum_univ_castSucc, withLast]

lemma withLast_decomp {d : ℕ} (x : Fin d → ℝ) (t : ℝ) :
    withLast x t =
      (∑ i : Fin d, x i • Pi.single i.castSucc (1 : ℝ)) +
        t • Pi.single (Fin.last d) (1 : ℝ) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [withLast, Pi.single_apply]
  · simp [withLast, Pi.single_apply]

lemma dual_withLast {d : ℕ} (l : StrongDual ℝ (Fin (d + 1) → ℝ)) :
    ∃ (w : Fin d → ℝ) (γ : ℝ), ∀ (x : Fin d → ℝ) (t : ℝ),
      l (withLast x t) = w ⬝ᵥ x + γ * t := by
  refine ⟨fun i => l (Pi.single i.castSucc 1), l (Pi.single (Fin.last d) 1), fun x t => ?_⟩
  rw [withLast_decomp x t, map_add, map_sum, map_smul, smul_eq_mul, mul_comm t]
  congr 1
  simp [map_smul, dotProduct, mul_comm]

lemma mem_segment_withLast_zero {d : ℕ} {a₀ b₀ x : Fin d → ℝ}
    (h : withLast x 0 ∈ segment ℝ (withLast a₀ 0) (withLast b₀ 1)) : x = a₀ := by
  obtain ⟨α, β, _, _, hαβ, heq⟩ := h
  have hlast : (α • withLast a₀ 0 + β • withLast b₀ 1) (Fin.last d) = withLast x 0 (Fin.last d) :=
    congr_fun heq (Fin.last d)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, withLast_last, mul_zero, mul_one,
    zero_add] at hlast
  have hα : α = 1 := by linarith
  rw [hα, hlast, one_smul, zero_smul, add_zero] at heq
  exact (withLast_inj_left heq).symm

lemma mem_segment_withLast_one {d : ℕ} {a₀ b₀ y : Fin d → ℝ}
    (h : withLast y 1 ∈ segment ℝ (withLast a₀ 0) (withLast b₀ 1)) : y = b₀ := by
  obtain ⟨α, β, _, _, hαβ, heq⟩ := h
  have hlast : (α • withLast a₀ 0 + β • withLast b₀ 1) (Fin.last d) = withLast y 1 (Fin.last d) :=
    congr_fun heq (Fin.last d)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, withLast_last, mul_zero, mul_one,
    zero_add] at hlast
  have hα : α = 0 := by linarith
  rw [hα, hlast, zero_smul, one_smul, zero_add] at heq
  exact (withLast_inj_left heq).symm

end Aux_ZOE_fact6

open ZeroOneExpansion Matrix Aux_ZOE_fact6

theorem solution {d : ℕ} (A B : Finset (Fin d → ℝ)) (hA : A.Nonempty) (hB : B.Nonempty)
    (a₀ b₀ : Fin d → ℝ) (ha : a₀ ∈ A) (hb : b₀ ∈ B) :
    IsExposed ℝ (cayleySum (A : Set (Fin d → ℝ)) (B : Set (Fin d → ℝ)))
        (segment ℝ (withLast a₀ 0) (withLast b₀ 1)) ↔
      ∃ w : Fin d → ℝ, (∀ a ∈ A, a ≠ a₀ → w ⬝ᵥ a < w ⬝ᵥ a₀) ∧
        (∀ b ∈ B, b ≠ b₀ → w ⬝ᵥ b < w ⬝ᵥ b₀) := by
  let _ := hA
  let _ := hB
  constructor
  · intro hExp
    obtain ⟨l, hl⟩ := hExp ⟨withLast a₀ 0, left_mem_segment ℝ _ _⟩
    obtain ⟨w, γ, hwγ⟩ := dual_withLast l
    have hu₀_mem : withLast a₀ 0 ∈ {x ∈ cayleySum (A : Set _) (B : Set _) |
        ∀ y ∈ cayleySum (A : Set _) (B : Set _), l y ≤ l x} :=
      hl ▸ left_mem_segment ℝ _ _
    have hv₀_mem : withLast b₀ 1 ∈ {x ∈ cayleySum (A : Set _) (B : Set _) |
        ∀ y ∈ cayleySum (A : Set _) (B : Set _), l y ≤ l x} :=
      hl ▸ right_mem_segment ℝ _ _
    refine ⟨w, fun a haA hne => ?_, fun b hbB hne => ?_⟩
    · have ha_cay : withLast a 0 ∈ cayleySum (A : Set _) (B : Set _) :=
        subset_convexHull ℝ _ (Or.inl ⟨a, haA, rfl⟩)
      have hle : w ⬝ᵥ a ≤ w ⬝ᵥ a₀ := by
        have := hu₀_mem.2 _ ha_cay
        rw [hwγ, hwγ] at this
        linarith
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hmem_seg : withLast a 0 ∈ segment ℝ (withLast a₀ 0) (withLast b₀ 1) := by
          rw [hl]
          refine ⟨ha_cay, fun y hy => ?_⟩
          calc l y ≤ l (withLast a₀ 0) := hu₀_mem.2 y hy
            _ = l (withLast a 0) := by rw [hwγ, hwγ, heq]
        exact hne (mem_segment_withLast_zero hmem_seg)
    · have hb_cay : withLast b 1 ∈ cayleySum (A : Set _) (B : Set _) :=
        subset_convexHull ℝ _ (Or.inr ⟨b, hbB, rfl⟩)
      have hle : w ⬝ᵥ b ≤ w ⬝ᵥ b₀ := by
        have := hv₀_mem.2 _ hb_cay
        rw [hwγ, hwγ] at this
        linarith
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hmem_seg : withLast b 1 ∈ segment ℝ (withLast a₀ 0) (withLast b₀ 1) := by
          rw [hl]
          refine ⟨hb_cay, fun y hy => ?_⟩
          calc l y ≤ l (withLast b₀ 1) := hv₀_mem.2 y hy
            _ = l (withLast b 1) := by rw [hwγ, hwγ, heq]
        exact hne (mem_segment_withLast_one hmem_seg)
  · rintro ⟨w, hAw, hBw⟩ _
    classical
    let γ : ℝ := w ⬝ᵥ a₀ - w ⬝ᵥ b₀
    let c : Fin (d + 1) → ℝ := withLast w γ
    let X : Finset (Fin (d + 1) → ℝ) :=
      A.image (fun a => withLast a 0) ∪ B.image (fun b => withLast b 1)
    have hX_coe : (X : Set (Fin (d + 1) → ℝ)) =
        (fun a => withLast a 0) '' (A : Set _) ∪ (fun b => withLast b 1) '' (B : Set _) := by
      simp [X, Finset.coe_union, Finset.coe_image]
    have hX_ne : X.Nonempty :=
      ⟨withLast a₀ 0, Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)⟩
    let l : StrongDual ℝ (Fin (d + 1) → ℝ) := ∑ k : Fin (d + 1), c k • ContinuousLinearMap.proj k
    have hl_dot : ∀ x, l x = c ⬝ᵥ x := fun x => by
      simp [l, ContinuousLinearMap.sum_apply, dotProduct]
    refine ⟨l, ?_⟩
    have hexp : {x ∈ cayleySum (A : Set _) (B : Set _) |
        ∀ y ∈ cayleySum (A : Set _) (B : Set _), l y ≤ l x} =
        exposedFace (convexHull ℝ (X : Set (Fin (d + 1) → ℝ))) (fun x => c ⬝ᵥ x) := by
      rw [cayleySum, ← hX_coe]
      ext x
      simp [exposedFace, hl_dot]
    rw [hexp, ZeroOneExpansion.fact_2 X hX_ne c]
    have hmax_val : ∀ z ∈ X, c ⬝ᵥ z ≤ w ⬝ᵥ a₀ := by
      intro z hz
      simp only [X, Finset.mem_union, Finset.mem_image] at hz
      rcases hz with ⟨a, haA, rfl⟩ | ⟨b, hbB, rfl⟩
      · simp only [c, dot_withLast, mul_zero, add_zero]
        by_cases h : a = a₀
        · subst h; exact le_rfl
        · exact (hAw a haA h).le
      · simp only [c, γ, dot_withLast, mul_one]
        by_cases h : b = b₀
        · subst h; linarith
        · linarith [hBw b hbB h]
    have hset : {x | x ∈ X ∧ ∀ z ∈ X, c ⬝ᵥ z ≤ c ⬝ᵥ x} = {withLast a₀ 0, withLast b₀ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxX, hxmax⟩
        have hge : w ⬝ᵥ a₀ ≤ c ⬝ᵥ x := by
          have := hxmax (withLast a₀ 0) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))
          simpa [c, dot_withLast] using this
        simp only [X, Finset.mem_union, Finset.mem_image] at hxX
        rcases hxX with ⟨a, haA, rfl⟩ | ⟨b, hbB, rfl⟩
        · left
          by_contra hne
          have hlt := hAw a haA (fun h => hne (by rw [h]))
          simp only [c, dot_withLast, mul_zero, add_zero] at hge
          linarith
        · right
          by_contra hne
          have hlt := hBw b hbB (fun h => hne (by rw [h]))
          simp only [c, γ, dot_withLast, mul_one] at hge
          linarith
      · rintro (rfl | rfl)
        · refine ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha), fun z hz => ?_⟩
          simpa [c, dot_withLast] using hmax_val z hz
        · refine ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ hb), fun z hz => ?_⟩
          have := hmax_val z hz
          simp only [c, γ, dot_withLast, mul_one]
          linarith
    rw [hset, convexHull_pair]
