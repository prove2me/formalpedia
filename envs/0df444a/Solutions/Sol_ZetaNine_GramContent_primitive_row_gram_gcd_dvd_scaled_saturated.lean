-- Prove2me | solution 1 for ZetaNine.GramContent.primitive_row_gram_gcd_dvd_scaled_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:35:45.481028+00:00
-- url     : https://prove2.me/submissions/dff19fb0-92a0-44cc-811a-f4897b5d0991

import Definitions.Def_ZetaNine_GramContent
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators


namespace ZetaNine.GramContent
variable {ι : Type*} [Fintype ι]

/-- A Bézout certificate and a common divisor of all minors give an
integral row decomposition. No restriction on the number of coordinates. -/
theorem exists_integral_decomposition (u v a : ι → ℤ) (Δ : ℤ)
    (hbezout : (∑ i, a i * u i) = 1)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    ∃ (lam : ℤ) (w : ι → ℤ), ∀ i, v i = lam * u i + Δ * w i := by
  classical
  let lam : ℤ := ∑ j, a j * v j
  have hdiv : ∀ i, Δ ∣ v i - lam * u i := by
    intro i
    have hsum : Δ ∣ ∑ j, a j * (u j * v i - u i * v j) :=
      Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hminor j i) (a j)
    have heq : (∑ j, a j * (u j * v i - u i * v j)) = v i - lam * u i := by
      calc
        (∑ j, a j * (u j * v i - u i * v j)) =
            ∑ j, ((a j * u j) * v i - (a j * v j) * u i) := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ j, a j * u j) * v i - (∑ j, a j * v j) * u i := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
        _ = v i - lam * u i := by rw [hbezout]; simp [lam]
    exact heq ▸ hsum
  refine ⟨lam, fun i => (v i - lam * u i) / Δ, ?_⟩
  intro i
  have hmul := Int.ediv_mul_cancel (hdiv i)
  have hmul' : Δ * ((v i - lam * u i) / Δ) = v i - lam * u i := by
    simpa only [mul_comm] using hmul
  calc
    v i = lam * u i + (v i - lam * u i) := by ring
    _ = lam * u i + Δ * ((v i - lam * u i) / Δ) := by
      rw [hmul']

theorem dot_decomposition (u w : ι → ℤ) (lam Δ : ℤ) :
    dot u (fun i => lam * u i + Δ * w i) =
      lam * normSq u + Δ * dot u w := by
  classical
  unfold dot normSq dot
  calc
    (∑ i, u i * (lam * u i + Δ * w i)) =
        ∑ i, (lam * (u i * u i) + Δ * (u i * w i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = lam * (∑ i, u i * u i) + Δ * (∑ i, u i * w i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem normSq_decomposition (u w : ι → ℤ) (lam Δ : ℤ) :
    normSq (fun i => lam * u i + Δ * w i) =
      lam ^ 2 * normSq u + (2 * lam * Δ) * dot u w + Δ ^ 2 * normSq w := by
  classical
  unfold normSq dot
  calc
    (∑ i, (lam * u i + Δ * w i) * (lam * u i + Δ * w i)) =
        ∑ i, (lam ^ 2 * (u i * u i) + (2 * lam * Δ) * (u i * w i) +
          Δ ^ 2 * (w i * w i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = lam ^ 2 * (∑ i, u i * u i) + (2 * lam * Δ) * (∑ i, u i * w i) +
        Δ ^ 2 * (∑ i, w i * w i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Exact Gram determinant identity for an integral row decomposition. -/
theorem gram_det_decomposition (u v w : ι → ℤ) (lam Δ : ℤ)
    (hv : ∀ i, v i = lam * u i + Δ * w i) :
    normSq u * normSq v - (dot u v) ^ 2 =
      Δ ^ 2 * (normSq u * normSq w - (dot u w) ^ 2) := by
  have hvfun : v = fun i => lam * u i + Δ * w i := funext hv
  rw [hvfun, normSq_decomposition, dot_decomposition]
  ring

/-- Any common minor divisor of a primitive row pair has its square
dividing the Gram determinant. -/
theorem minor_divisor_sq_dvd_gram_det (u v a : ι → ℤ) (Δ : ℤ)
    (hbezout : (∑ i, a i * u i) = 1)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    Δ ^ 2 ∣ normSq u * normSq v - (dot u v) ^ 2 := by
  obtain ⟨lam, w, hv⟩ := exists_integral_decomposition u v a Δ hbezout hminor
  exact ⟨normSq u * normSq w - (dot u w) ^ 2,
    gram_det_decomposition u v w lam Δ hv⟩

/-- Gram-content divisibility, in arbitrary finite dimension, using an
explicit Bézout certificate for the primitive first row. This is stronger
than requiring Δ to be the greatest common divisor of the minors: any
nonzero common minor divisor suffices. -/
theorem gram_gcd_dvd_scaled_saturated (u v a : ι → ℤ) (Δ : ℤ)
    (hbezout : (∑ i, a i * u i) = 1) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (Int.gcd (normSq u) (dot u v) : ℤ) ∣ Δ * saturatedGram u v Δ := by
  obtain ⟨lam, w, hv⟩ := exists_integral_decomposition u v a Δ hbezout hminor
  have hvfun : v = fun i => lam * u i + Δ * w i := funext hv
  have hC : dot u v = lam * normSq u + Δ * dot u w := by
    rw [hvfun]
    exact dot_decomposition u w lam Δ
  have hquot : saturatedGram u v Δ = normSq u * normSq w - (dot u w) ^ 2 := by
    unfold saturatedGram
    rw [gram_det_decomposition u v w lam Δ hv]
    exact Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hΔ)
  have hT : (Int.gcd (normSq u) (dot u v) : ℤ) ∣ normSq u :=
    Int.gcd_dvd_left _ _
  have hCv : (Int.gcd (normSq u) (dot u v) : ℤ) ∣ dot u v :=
    Int.gcd_dvd_right _ _
  have hDB : (Int.gcd (normSq u) (dot u v) : ℤ) ∣ Δ * dot u w := by
    have hsub := dvd_sub hCv (dvd_mul_of_dvd_right hT lam)
    have heq : dot u v - lam * normSq u = Δ * dot u w := by
      rw [hC]
      ring
    exact heq ▸ hsub
  have hscaled := dvd_sub (dvd_mul_of_dvd_left hT (Δ * normSq w))
    (dvd_mul_of_dvd_left hDB (dot u w))
  have heq : normSq u * (Δ * normSq w) - (Δ * dot u w) * dot u w =
      Δ * (normSq u * normSq w - (dot u w) ^ 2) := by ring
  rw [heq] at hscaled
  rw [hquot]
  exact hscaled

/-- The same all-dimensional theorem with primitiveness expressed by
existence of a Bézout certificate, rather than a chosen certificate. -/
theorem checked_primitive_row_gram_gcd_dvd_scaled_saturated (u v : ι → ℤ) (Δ : ℤ)
    (hprimitive : ∃ a : ι → ℤ, (∑ i, a i * u i) = 1) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (Int.gcd (normSq u) (dot u v) : ℤ) ∣ Δ * saturatedGram u v Δ := by
  obtain ⟨a, hbezout⟩ := hprimitive
  exact gram_gcd_dvd_scaled_saturated u v a Δ hbezout hΔ hminor


end ZetaNine.GramContent

open ZetaNine.GramContent

theorem solution {ι : Type*} [Fintype ι] (u v : ι → ℤ) (Δ : ℤ)
    (hprimitive : ∃ a : ι → ℤ, (∑ i, a i * u i) = 1) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (Int.gcd (normSq u) (dot u v) : ℤ) ∣ Δ * saturatedGram u v Δ := by
  exact ZetaNine.GramContent.checked_primitive_row_gram_gcd_dvd_scaled_saturated u v Δ hprimitive hΔ hminor

#print axioms solution
