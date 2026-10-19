-- Prove2me | solution 1 for SpherePacking.CohnElkies.LPBoundAux.summable_norm_on_translated_integral_lattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/8c721711-662d-4f5c-bce6-7eb3752e3447

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped SchwartzMap
open scoped FourierTransform
open BigOperators
open SpherePacking SpherePacking.CohnElkies
variable {d : ℕ}
open SpherePacking.CohnElkies.LPBoundAux
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
namespace SpherePacking.CohnElkies.LPBoundAux
theorem _root_.solution (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (a : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Λ => ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖) := by
  let k : ℕ := Module.finrank ℤ Λ + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  have hdecay : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ^ k * ‖f x‖ ≤ C := by
    simpa [norm_iteratedFDeriv_zero] using! hC
  let R : ℝ := max (2 * ‖a‖) 1
  have hfinite : ({ℓ : Λ | ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ ≤ R} : Set Λ).Finite := by
    haveI : DiscreteTopology Λ.toAddSubgroup :=
      (inferInstance : DiscreteTopology Λ)
    have hfiniteAmbient :
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∩
          (Λ.toAddSubgroup : Set (EuclideanSpace ℝ (Fin d)))).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall AddSubgroup.isClosed_of_discrete
    let e : Λ ↪ EuclideanSpace ℝ (Fin d) :=
      ⟨fun ℓ => (ℓ : EuclideanSpace ℝ (Fin d)), Subtype.coe_injective⟩
    have hpreimage :
        (e ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∩
          (Λ : Set (EuclideanSpace ℝ (Fin d))))).Finite := by
      apply Set.Finite.preimage_embedding e
      simpa [Submodule.coe_toAddSubgroup] using! hfiniteAmbient
    have hset :
        e ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R ∩
          (Λ : Set (EuclideanSpace ℝ (Fin d)))) =
            {ℓ : Λ | ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ ≤ R} := by
      ext ℓ
      simp [e, Metric.mem_closedBall, dist_eq_norm]
    simpa [hset] using! hpreimage
  have hsumPow :
      Summable (fun ℓ : Λ =>
        (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k : ℝ)) := by
    simpa [k] using!
      (ZLattice.summable_norm_pow_inv (L := Λ) (n := k)
        (Nat.lt_succ_self (Module.finrank ℤ Λ)))
  have hsumBound :
      Summable (fun ℓ : Λ =>
        (C * (2 ^ k : ℝ)) *
          (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k)) :=
    hsumPow.mul_left (C * (2 ^ k : ℝ))
  refine Summable.of_norm_bounded_eventually hsumBound ?_
  filter_upwards [hfinite.eventually_cofinite_notMem] with ℓ hℓ
  have hR : R < ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    lt_of_not_ge (by simpa using! hℓ)
  have hlarge : 2 * ‖a‖ < ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    lt_of_le_of_lt (le_max_left _ _) hR
  have hpositive : 0 < ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hR.le)
  have htranslate :
      (1 / 2 : ℝ) * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
    have htriangle :
        ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ - ‖a‖ ≤
          ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
      simpa [add_comm] using!
        (norm_sub_norm_le (ℓ : EuclideanSpace ℝ (Fin d)) (-a))
    nlinarith
  have htranslatePositive :
      0 < ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hpositive).trans_le htranslate
  have hpowPositive :
      0 < ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k :=
    pow_pos htranslatePositive _
  have hbound :
      ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤
        C / ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k :=
    (le_div_iff₀' hpowPositive).2
      (hdecay (a + (ℓ : EuclideanSpace ℝ (Fin d))))
  have hpower :
      ((1 / 2 : ℝ) * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖) ^ k ≤
        ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k :=
    pow_le_pow_left₀ (by positivity) htranslate _
  have hsourcePositive :
      0 < ((1 / 2 : ℝ) * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖) ^ k :=
    pow_pos (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hpositive) _
  have hinverse :
      (‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k)⁻¹ ≤
        (2 ^ k : ℝ) *
          (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k) := by
    have h := one_div_le_one_div_of_le hsourcePositive hpower
    simpa [one_div, mul_pow, mul_inv_rev, inv_pow, mul_assoc, mul_comm]
      using! h
  have hfinal :=
    (mul_le_mul_of_nonneg_left hinverse hCpos.le)
  have hresult :
      ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤
        (C * (2 ^ k : ℝ)) *
          (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k) := by
    calc
      ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤
          C / ‖a + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k := hbound
      _ ≤ (C * (2 ^ k : ℝ)) *
          (‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k) := by
        simpa [div_eq_mul_inv, mul_assoc] using! hfinal
  simpa [Real.norm_of_nonneg (norm_nonneg _)] using! hresult
end SpherePacking.CohnElkies.LPBoundAux
