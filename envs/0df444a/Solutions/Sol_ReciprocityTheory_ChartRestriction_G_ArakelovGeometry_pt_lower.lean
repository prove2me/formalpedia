-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.pt_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:40:05.544327+00:00
-- url     : https://prove2.me/submissions/fbb92958-a7f5-4ea3-90d1-1e51d7dc10c5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eval_prodForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_form_enum_sq_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_norm_le_sqrt_of_sq_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sqN_comp_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sq_wgt_le_of_le
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} {m : ConeMetric ℂ (Ix κ)}
    (hFS : IsPullFS x e m) {N kε δ : ℕ} (H : Fin δ → MvPolynomial (Ix κ) ℤ) {Cε : ℝ}
    (hCε0 : 0 ≤ Cε)
    (hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ kε)
    (c : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card) → ℂ) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) :
    ‖∑ p, c p * eval z (map (Int.castRingHom ℂ) (prodForm e (adtEnum D N (finProdFinEquiv.symm p).2)
        (H (finProdFinEquiv.symm p).1)))‖ ^ 2 * wgt m (N + kε) z ≤
      Cε ^ 2 * δ * ((N + D).choose D : ℝ) *
        ∑ l : Fin δ, ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 * monoNormSq (adtEnum D N i) := by
  have hρ0 : 0 ≤ m.ρ z := m.nonneg z
  have hBn0 : (0 : ℝ) ≤ ((N + D).choose D : ℝ) := Nat.cast_nonneg _
  set q : Fin δ → ℝ := fun l =>
    ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 * monoNormSq (adtEnum D N i) with hq
  have hq0 : ∀ l, 0 ≤ q l := fun l =>
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (monoNormSq_pos _).le
  set P : Fin δ → ℂ := fun l =>
    ∑ i, c (finProdFinEquiv (l, i)) * monoC (adtEnum D N i) (z ∘ e) with hP
  have hsum : ∑ p, c p * eval z (map (Int.castRingHom ℂ) (prodForm e
      (adtEnum D N (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1))) =
      ∑ l, eval z (map (Int.castRingHom ℂ) (H l)) * P l := by
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Equiv.symm_apply_apply, eval_prodForm]; ring
  have hPl : ∀ l, ‖P l‖ ≤ Real.sqrt (((N + D).choose D : ℝ) * q l) * m.ρ z ^ N := fun l => by
    have h := form_enum_sq_le D N (fun i => c (finProdFinEquiv (l, i))) (z ∘ e)
    rw [sqN_comp_eq hFS hz] at h
    refine norm_le_sqrt_of_sq_le (norm_nonneg _) (mul_nonneg hBn0 (hq0 l)) (pow_nonneg hρ0 N) ?_
    calc ‖P l‖ ^ 2 ≤ ((N + D).choose D : ℝ) * (m.ρ z ^ 2) ^ N * q l := h
      _ = ((N + D).choose D : ℝ) * q l * (m.ρ z ^ N) ^ 2 := by ring
  have hmain : ‖∑ l, eval z (map (Int.castRingHom ℂ) (H l)) * P l‖ ≤
      (Cε * ∑ l, Real.sqrt (((N + D).choose D : ℝ) * q l)) * m.ρ z ^ (N + kε) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [norm_mul]
    calc ‖eval z (map (Int.castRingHom ℂ) (H l))‖ * ‖P l‖ ≤
          (Cε * m.ρ z ^ kε) * (Real.sqrt (((N + D).choose D : ℝ) * q l) * m.ρ z ^ N) :=
          mul_le_mul (hCε l z hz) (hPl l) (norm_nonneg _) (by positivity)
      _ = Cε * Real.sqrt (((N + D).choose D : ℝ) * q l) * m.ρ z ^ (N + kε) := by ring
  rw [hsum]
  refine (sq_wgt_le_of_le hz.1 (norm_nonneg _) hmain).trans ?_
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun l => Real.sqrt (((N + D).choose D : ℝ) * q l))
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  rw [mul_pow]
  calc Cε ^ 2 * (∑ l, Real.sqrt (((N + D).choose D : ℝ) * q l)) ^ 2 ≤
        Cε ^ 2 * (δ * ∑ l, Real.sqrt (((N + D).choose D : ℝ) * q l) ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ = Cε ^ 2 * δ * ((N + D).choose D : ℝ) * ∑ l, q l := by
        simp_rw [Real.sq_sqrt (mul_nonneg hBn0 (hq0 _))]
        rw [← Finset.mul_sum]; ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
