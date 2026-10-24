-- Prove2me | solution 1 for SurelyBetter.CLB.theorem2_interior_optimum
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:08:24.648817+00:00
-- url     : https://prove2.me/submissions/de7aa65a-e037-4f7d-83d2-d13fb98f1e45

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Theorems.Thm_SurelyBetter_CLB_theorem2_min_rep

open SurelyBetter.CLB

theorem solution {S : Type*} [Fintype S] (U : Set ℝ)
    (hU : Convex ℝ U) (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) (hρ : ρ E + ρ Eᶜ < 1)
    (x y w z : ℝ) (hx : x ∈ U) (hy : y ∈ U) (hw : w ∈ U) (hz : z ∈ U)
    (hxy : y < x) (hzw : w < z) (hxw : w < x) (hzy : y < z)
    (hslope_lo : ρ E * (x - w) < (1 - ρ E) * (z - y))
    (hslope_hi : ρ Eᶜ * (z - y) < (1 - ρ Eᶜ) * (x - w)) :
    optMix V (binProf E x y) (binProf E w z) = {1 / (1 + (x - y) / (z - w))} := by
  classical
  have hrep := SurelyBetter.CLB.theorem2_min_rep U hU hU2 V ρ hV E hρ
  clear hU2 hV hρ hxw hzy
  let a : ℝ → ℝ := fun t => t * x + (1 - t) * w
  let b : ℝ → ℝ := fun t => t * y + (1 - t) * z
  let A : ℝ → ℝ := fun t => ρ E * a t + (1 - ρ E) * b t
  let B : ℝ → ℝ := fun t => (1 - ρ Eᶜ) * a t + ρ Eᶜ * b t
  let α : ℝ := (z - w) / ((x - y) + (z - w))
  have hden : 0 < (x - y) + (z - w) := by linarith
  have hα0 : 0 < α := div_pos (sub_pos.mpr hzw) hden
  have hα1 : α < 1 := (div_lt_one hden).mpr (by linarith)
  have hα : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα0.le, hα1.le⟩
  have hcross : a α = b α := by
    dsimp [a, b, α]
    field_simp
    ring
  have hAB : A α = B α := by
    dsimp [A, B]
    rw [hcross]
    ring
  have hweight : α = 1 / (1 + (x - y) / (z - w)) := by
    dsimp [α]
    have hzw0 : z - w ≠ 0 := ne_of_gt (sub_pos.mpr hzw)
    rw [one_add_div hzw0, one_div_div]
    congr 1
    ring
  have hAdiff (t : ℝ) :
      A t - A α = (t - α) * (ρ E * (x - w) - (1 - ρ E) * (z - y)) := by
    dsimp [A, a, b]
    ring
  have hBdiff (t : ℝ) :
      B t - B α = (t - α) * ((1 - ρ Eᶜ) * (x - w) - ρ Eᶜ * (z - y)) := by
    dsimp [B, a, b]
    ring
  have hstrict (t : ℝ) (ht : t ≠ α) : min (A t) (B t) < min (A α) (B α) := by
    rw [min_eq_left hAB.le]
    rcases lt_or_gt_of_ne ht with ht | ht
    · have hp := mul_neg_of_neg_of_pos (sub_neg.mpr ht) (sub_pos.mpr hslope_hi)
      have hb : B t < A α := by linarith [hBdiff t]
      exact lt_of_le_of_lt (min_le_right _ _) hb
    · have hp := mul_neg_of_pos_of_neg (sub_pos.mpr ht) (sub_neg.mpr hslope_lo)
      have ha : A t < A α := by linarith [hAdiff t]
      exact lt_of_le_of_lt (min_le_left _ _) ha
  have hmax (t : ℝ) : min (A t) (B t) ≤ min (A α) (B α) := by
    by_cases ht : t = α
    · subst t
      rfl
    · exact (hstrict t ht).le
  have hmem_a (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : a t ∈ U := by
    exact hU hx hw ht.1 (sub_nonneg.mpr ht.2) (by ring)
  have hmem_b (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : b t ∈ U := by
    exact hU hy hz ht.1 (sub_nonneg.mpr ht.2) (by ring)
  have hmix (t : ℝ) : mix t (binProf E x y) (binProf E w z) = binProf E (a t) (b t) := by
    funext s
    by_cases hs : s ∈ E <;> simp [mix, binProf, a, b, hs]
  have hcompare (t s : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      V (mix t (binProf E x y) (binProf E w z)) ≤
          V (mix s (binProf E x y) (binProf E w z)) ↔
        min (A t) (B t) ≤ min (A s) (B s) := by
    rw [hmix, hmix]
    exact hrep (a t) (hmem_a t ht) (b t) (hmem_b t ht)
      (a s) (hmem_a s hs) (b s) (hmem_b s hs)
  ext t
  constructor
  · rintro ⟨ht, hopt⟩
    have hle := (hcompare α t hα ht).mp (hopt α hα)
    have heq : t = α := by
      by_contra hne
      exact (not_lt_of_ge hle) (hstrict t hne)
    exact Set.mem_singleton_iff.mpr (heq.trans hweight)
  · intro ht
    have heq : t = α := (Set.mem_singleton_iff.mp ht).trans hweight.symm
    rw [heq]
    refine ⟨hα, ?_⟩
    intro s hs
    exact (hcompare s α hs hα).mpr (hmax s)
