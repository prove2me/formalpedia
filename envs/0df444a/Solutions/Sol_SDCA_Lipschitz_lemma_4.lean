-- Prove2me | solution 1 for SDCA.Lipschitz.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:39:09.82102+00:00
-- url     : https://prove2.me/submissions/3a6b2346-6413-470f-b6a4-f4dc1caa6569

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model

set_option autoImplicit false
open SDCA.Lipschitz

theorem conj_top_of_lip (φ : ℝ → ℝ) (L : ℝ) (hLip : ∀ a b : ℝ, |φ a - φ b| ≤ L * |a - b|)
    (α : ℝ) (hα : L < |α|) :
    conj φ α = ⊤ := by
  unfold conj
  rw [iSup_eq_top]
  intro b hb
  obtain ⟨r, hbr, -⟩ := EReal.lt_iff_exists_real_btwn.mp hb
  set ε : ℝ := |α| - L with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  -- choose z = t * sign α with t large
  set t : ℝ := (max 0 (r + φ 0 + 1)) / ε with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have htε : t * ε = max 0 (r + φ 0 + 1) := by rw [ht]; field_simp
  set z : ℝ := t * SignType.sign α with hz
  have hαne : α ≠ 0 := by
    intro h; rw [h] at hα; simp at hα
    have : (0:ℝ) ≤ L := by
      have := hLip 1 0; simp at this; exact (abs_nonneg _).trans this
    linarith
  have hzα : z * α = t * |α| := by
    rw [hz]
    rcases lt_or_gt_of_ne hαne with h | h
    · simp [h, abs_of_neg h]
    · simp [h, abs_of_pos h]
  have hzabs : |z| = t := by
    rw [hz]
    rcases lt_or_gt_of_ne hαne with h | h
    · simp [h, abs_of_nonneg ht0]
    · simp [h, abs_of_nonneg ht0]
  refine ⟨z, ?_⟩
  refine lt_trans hbr ?_
  rw [EReal.coe_lt_coe_iff]
  have h1 := hLip z 0
  have h2 : |φ z - φ 0| ≤ L * t := by simpa [hzabs] using h1
  have h3 := (abs_le.mp h2).2
  have h4 : r + 1 ≤ t * ε - φ 0 := by
    rw [htε]; linarith [le_max_right 0 (r + φ 0 + 1)]
  have h5 : t * |α| = t * ε + L * t := by rw [hε]; ring
  show r < z * α - φ z
  rw [hzα, h5]
  linarith


theorem solution {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (hx : ∀ i, ‖x i‖ ≤ 1)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ i (a b : ℝ), |φ i a - φ i b| ≤ L * |a - b|)
    (u : Fin n → ℝ → ℝ) (hu : ∀ i a, -(u i a) ∈ subdiff (φ i) a)
    (α : Fin n → ℝ) (hα : ∀ j, conj (φ j) (-α j) ≠ ⊤) :
    (1 / (n : ℝ)) * ∑ i, ‖x i‖ ^ 2 * (u i (inner ℝ (wOf x lam α) (x i)) - α i) ^ 2
      ≤ 4 * L ^ 2 := by
  have hterm : ∀ i, ‖x i‖ ^ 2 * (u i (inner ℝ (wOf x lam α) (x i)) - α i) ^ 2 ≤ 4 * L ^ 2 := by
    intro i
    set a := inner ℝ (wOf x lam α) (x i) with ha
    have hαi : |α i| ≤ L := by
      by_contra h
      have h' : L < |-α i| := by rw [abs_neg]; exact not_le.mp h
      exact hα i (conj_top_of_lip (φ i) L (hLip i) (-α i) h')
    have hui : |u i a| ≤ L := by
      have hs := hu i a
      unfold subdiff at hs
      simp only [Set.mem_setOf_eq] at hs
      have h1 := hs (a + 1)
      have h2 := hs (a - 1)
      have l1 := hLip i (a + 1) a
      have l2 := hLip i (a - 1) a
      simp only [add_sub_cancel_left, abs_one, sub_sub_cancel_left, abs_neg, mul_one] at l1 l2
      have l1' := (abs_le.mp l1).2
      have l2' := (abs_le.mp l2).2
      rw [abs_le]
      constructor <;> nlinarith
    have hd : (u i a - α i) ^ 2 ≤ 4 * L ^ 2 := by
      have : |u i a - α i| ≤ 2 * L := by
        calc |u i a - α i| ≤ |u i a| + |α i| := abs_sub _ _
          _ ≤ 2 * L := by linarith
      have := sq_le_sq' (by linarith [abs_le.mp this]) (abs_le.mp this).2
      nlinarith [this]
    have hx2 : ‖x i‖ ^ 2 ≤ 1 := by
      have := hx i
      nlinarith [norm_nonneg (x i)]
    calc ‖x i‖ ^ 2 * (u i a - α i) ^ 2 ≤ 1 * (4 * L ^ 2) :=
          mul_le_mul hx2 hd (sq_nonneg _) zero_le_one
      _ = 4 * L ^ 2 := one_mul _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [one_div, inv_mul_le_iff₀ hnpos]
  exact hsum
