-- Prove2me | solution 1 for ZetaNine.CenterDenominator.primitive_center_denominator_divisor
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:35:48.859194+00:00
-- url     : https://prove2.me/submissions/60e2e5f2-8268-4a82-a3ff-b5893e993250

import Definitions.Def_ZetaNine_GramContent
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset


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
theorem primitive_row_gram_gcd_dvd_scaled_saturated (u v : ι → ℤ) (Δ : ℤ)
    (hprimitive : ∃ a : ι → ℤ, (∑ i, a i * u i) = 1) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (Int.gcd (normSq u) (dot u v) : ℤ) ∣ Δ * saturatedGram u v Δ := by
  obtain ⟨a, hbezout⟩ := hprimitive
  exact gram_gcd_dvd_scaled_saturated u v a Δ hbezout hΔ hminor


end ZetaNine.GramContent


set_option autoImplicit false

/-! The reduced center denominator lower divisor, for arbitrary row contents.
Source: research/direction-arithmetic-next-2026-10-02.md, section 2.
-/

namespace ZetaNine.ProjectionDenominator

theorem forced_divisor (T H : ℤ) (q : ℚ) (hT : T ≠ 0)
    (hdiv : T ∣ H * (q.den : ℤ)) : T.natAbs / T.gcd H ∣ q.den := by
  have hgpos : 0 < T.gcd H := Int.gcd_pos_of_ne_zero_left H hT
  have hg0 : (T.gcd H : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt hgpos)
  have hmul : T / (T.gcd H : ℤ) ∣ (H / (T.gcd H : ℤ)) * (q.den : ℤ) := by
    apply (Int.div_dvd_iff_dvd_mul (Int.gcd_dvd_left T H) hg0).2
    convert hdiv using 1
    rw [← mul_assoc, mul_comm (T.gcd H : ℤ) (H / (T.gcd H : ℤ)),
      Int.ediv_mul_cancel (Int.gcd_dvd_right T H)]
  have hd : T / (T.gcd H : ℤ) ∣ (q.den : ℤ) :=
    Int.dvd_of_dvd_mul_right_of_gcd_one hmul (Int.gcd_ediv_gcd_ediv_gcd hgpos)
  have habs := Int.natAbs_dvd_natAbs.mpr hd
  simpa only [Int.natAbs_ediv, Int.natAbs_natCast,
    Int.gcd_dvd_left, or_true, if_true, Nat.add_zero] using habs

theorem content_denominator_divisor (a b T C H : ℤ) (ha : a ≠ 0) (hT : T ≠ 0)
    (hcontent : (T.gcd C : ℤ) ∣ H) :
    T.natAbs / T.gcd (b * H) ∣ (Rat.divInt (b * C) (a * T)).den := by
  let q : ℚ := Rat.divInt (b * C) (a * T)
  have cross : q.num * (a * T) = (b * C) * (q.den : ℤ) :=
    (Rat.divInt_eq_divInt_iff (Int.natCast_ne_zero.mpr (Rat.den_nz q))
      (mul_ne_zero ha hT)).mp (Rat.num_divInt_den q)
  have hC : T ∣ b * C * (q.den : ℤ) := by
    rw [← cross]
    exact ⟨q.num * a, by ring⟩
  have hg : T ∣ b * (T.gcd C : ℤ) * (q.den : ℤ) := by
    rw [Int.gcd_eq_gcd_ab]
    have hleft : T ∣ b * (T * Int.gcdA T C) * (q.den : ℤ) :=
      ⟨b * Int.gcdA T C * (q.den : ℤ), by ring⟩
    have hright : T ∣ b * (C * Int.gcdB T C) * (q.den : ℤ) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        dvd_mul_of_dvd_left hC (Int.gcdB T C)
    convert Int.dvd_add hleft hright using 1 <;> ring
  obtain ⟨k, hk⟩ := hcontent
  apply forced_divisor T (b * H) q hT
  rw [hk]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_of_dvd_left hg k


end ZetaNine.ProjectionDenominator


set_option autoImplicit false

open scoped BigOperators

namespace ZetaNine.CenterDenominator

open ZetaNine.GramContent

variable {ι : Type*} [Fintype ι]

/-- A primitive integral row cannot have square norm zero. Primitiveness is
expressed by an integral Bézout certificate, in arbitrary finite dimension. -/
theorem primitive_normSq_ne_zero (u : ι → ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1) : normSq u ≠ 0 := by
  classical
  intro hzero
  have hu : ∀ i, u i = 0 := by
    have hz : ∀ i ∈ Finset.univ, u i = 0 :=
      (Finset.sum_mul_self_eq_zero_iff Finset.univ u).mp
        (by simpa only [normSq, dot] using hzero)
    exact fun i => hz i (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := hprimitive
  simp only [hu, mul_zero, Finset.sum_const_zero, zero_ne_one] at hc

/-- The square norm is in fact strictly positive for a primitive row. -/
theorem primitive_normSq_pos (u : ι → ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1) : 0 < normSq u := by
  have hnonneg : 0 ≤ normSq u :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  exact lt_of_le_of_ne hnonneg (primitive_normSq_ne_zero u hprimitive).symm

/-- The full denominator divisor of the content-adjusted rational center.
The numerator-row content coefficient `b` may have either sign and need not
be coprime to the denominator-row content coefficient `a`. Any nonzero
common divisor of all minors is allowed. -/
theorem center_denominator_divisor (u v : ι → ℤ) (a b Δ : ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1)
    (ha : a ≠ 0) (hΔ : Δ ≠ 0) (hT : normSq u ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (normSq u).natAbs /
        Int.gcd (normSq u) (b * Δ * saturatedGram u v Δ) ∣
      (Rat.divInt (b * dot u v) (a * normSq u)).den := by
  have hcontent := primitive_row_gram_gcd_dvd_scaled_saturated
    u v Δ hprimitive hΔ hminor
  simpa only [mul_assoc] using
    ZetaNine.ProjectionDenominator.content_denominator_divisor
      a b (normSq u) (dot u v) (Δ * saturatedGram u v Δ) ha hT hcontent

/-- Original denominator bound (6), with the redundant norm-nonzero
assumption removed by primitiveness. This holds in every finite dimension. -/
theorem checked_primitive_center_denominator_divisor (u v : ι → ℤ) (a b Δ : ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1)
    (ha : a ≠ 0) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (normSq u).natAbs /
        Int.gcd (normSq u) (b * Δ * saturatedGram u v Δ) ∣
      (Rat.divInt (b * dot u v) (a * normSq u)).den := by
  exact center_denominator_divisor u v a b Δ hprimitive ha hΔ
    (primitive_normSq_ne_zero u hprimitive) hminor


end ZetaNine.CenterDenominator

open ZetaNine.CenterDenominator
open ZetaNine.GramContent

theorem solution {ι : Type*} [Fintype ι] (u v : ι → ℤ) (a b Δ : ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1)
    (ha : a ≠ 0) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (normSq u).natAbs /
        Int.gcd (normSq u) (b * Δ * saturatedGram u v Δ) ∣
      (Rat.divInt (b * dot u v) (a * normSq u)).den := by
  exact ZetaNine.CenterDenominator.checked_primitive_center_denominator_divisor u v a b Δ hprimitive ha hΔ hminor

#print axioms solution
