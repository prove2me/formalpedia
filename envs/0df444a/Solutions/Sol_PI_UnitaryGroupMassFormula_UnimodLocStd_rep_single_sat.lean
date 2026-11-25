-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_single_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:22:35.279035+00:00
-- url     : https://prove2.me/submissions/e6d2a673-b5ce-4d92-8df4-e7ccf43e7e25

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_elt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (j : m)
    (hj : SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) {z : m → ℂ} (hz : z ∈ Λ) :
    SatMem l Λ (Pi.single j (z j)) := by
  obtain ⟨hc4, -, -, -⟩ := hOK
  set θ := cmTheta b d with hθdef
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by positivity)
  have hθre : θ.re = b / 2 := by simp [hθdef, cmTheta]
  have hθim : θ.im = Real.sqrt d / 2 := by simp [hθdef, cmTheta]
  have hconj : conj θ = b - θ := by
    apply Complex.ext <;> simp [hθre, hθim] <;> ring
  set α : ℂ := (x * a : ℂ) + y * θ with hαdef
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef

  have hαn : Complex.normSq α = a * Q := by
    rw [Complex.normSq_apply]
    have hre : α.re = x * a + y * (b / 2) := by simp [hαdef, hθre]
    have him : α.im = y * (Real.sqrt d / 2) := by simp [hαdef, hθim]
    rw [hre, him, hQdef]
    have hc4' : (b : ℝ) ^ 2 + d = 4 * a * c := by exact_mod_cast hc4.symm
    push_cast
    linear_combination (y ^ 2 / 4) * hsq + (y ^ 2 / 4) * hc4'
  have hQ0 : Q ≠ 0 := fun h => hQ (by rw [h]; exact dvd_zero _)
  have hQ0' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hα0 : α ≠ 0 := by
    intro h
    have h1 := hαn
    rw [h, map_zero] at h1
    have h2 : (a : ℝ) * Q ≠ 0 := mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hQ0)
    exact h2 h1.symm
  have hnl : Complex.normSq lam ≠ 0 := (Complex.normSq_pos.2 hlam).ne'
  have harea : area (cmL a b d ha hd lam hlam) = Complex.normSq lam * a * (Real.sqrt d / 2) := by
    have e : conj (lam * (a : ℂ)) * (lam * θ) = ((Complex.normSq lam * a : ℝ) : ℂ) * θ := by
      rw [map_mul, Complex.conj_natCast]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    show |(conj (lam * (a : ℂ)) * (lam * θ)).im| = _
    rw [e, Complex.im_ofReal_mul, hθim]
    exact abs_of_pos (by have := Complex.normSq_pos.2 hlam; positivity)

  have hHs : ∀ u : ℂ, stdH (cmL a b d ha hd lam hlam) m z (Pi.single j u) =
      z j * ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj u := by
    intro u
    simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply]
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
    · simp [Matrix.smul_apply]
    · intro j' _ hj'
      simp [Pi.single_apply, hj']
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j' _ => ?_
      by_cases hj' : j' = j
      · subst hj'
        simp [Matrix.smul_apply, Matrix.one_apply_ne hi]
      · simp [Pi.single_apply, hj']
    · simp
  obtain ⟨N, hN, hw⟩ := hj
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero _)
  have hN0' : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hz' : z ∈ dualLat (stdH (cmL a b d ha hd lam hlam) m) Λ := by rw [hΛ]; exact hz
  have hwe : (N • Pi.single j (lam * α) : m → ℂ) = Pi.single j ((N : ℂ) * (lam * α)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [nsmul_eq_mul]
    · simp [Pi.single_apply, hi]
  have hθw : θ • Pi.single j ((N : ℂ) * (lam * α)) = Pi.single j (θ * ((N : ℂ) * (lam * α))) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Pi.single_apply, hi]
  obtain ⟨m1, hm1⟩ := hz' _ hw
  obtain ⟨m2, hm2⟩ := hz' _ (hθ _ hw)
  simp only [altE] at hm1 hm2
  rw [hwe] at hm1 hm2
  rw [hθw, hHs] at hm2
  rw [hHs] at hm1
  set X := z j * ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) with hXdef
  have hm2' : X.re * (-(Real.sqrt d / 2)) + X.im * (b / 2) = m2 := by
    have e : (X * conj θ).im = m2 := by
      rw [← hm2, hXdef, map_mul (starRingEnd ℂ) θ]
      congr 1
      ring
    rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hθre, hθim] at e
    linarith
  rw [hm1] at hm2'
  have hX : X * (Real.sqrt d : ℂ) = 2 * ((m1 : ℂ) * θ - m2) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hθre, hθim, mul_zero,
        sub_zero, zero_mul, Complex.mul_im, Complex.sub_im]
      linarith
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.sub_re,
        Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, hθre, hθim, mul_zero,
        zero_mul, add_zero, sub_zero, Complex.mul_re, hm1]
      ring

  have hcl : conj lam = (Complex.normSq lam : ℂ) / lam := by
    rw [eq_div_iff hlam, mul_comm, Complex.mul_conj]
  have hca : conj α = (Complex.normSq α : ℂ) / α := by
    rw [eq_div_iff hα0, mul_comm, Complex.mul_conj]
  have hsdC : (Real.sqrt d : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hnlC : (Complex.normSq lam : ℂ) ≠ 0 := by exact_mod_cast hnl
  have hzj : z j = ((((m1 * b - m2 : ℤ) : ℂ) - (m1 : ℂ) * conj θ) / ((N * Q : ℤ) : ℂ)) * (lam * α) := by
    have hareaC : ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ) ≠ 0 := by
      rw [harea]
      push_cast
      exact mul_ne_zero (mul_ne_zero hnlC ha0) (div_ne_zero hsdC two_ne_zero)
    have hK : ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) *
        (Real.sqrt d : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (inv_ne_zero hareaC)
        ((map_ne_zero _).2 (mul_ne_zero hN0' (mul_ne_zero hlam hα0)))) hsdC
    apply mul_right_cancel₀ hK
    calc z j * (((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * conj ((N : ℂ) * (lam * α)) *
          (Real.sqrt d : ℂ)) = X * (Real.sqrt d : ℂ) := by rw [hXdef]; ring
      _ = 2 * ((m1 : ℂ) * θ - m2) := hX
      _ = _ := by
          rw [harea, map_mul, map_mul, map_natCast, hcl, hca, hαn, hconj]
          push_cast
          field_simp
          ring
  have hsing : Pi.single j (z j) = ((((m1 * b - m2 : ℤ) : ℂ) - (m1 : ℂ) * conj θ) / ((N * Q : ℤ) : ℂ)) •
      Pi.single j (lam * α) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [hzj]
    · simp [Pi.single_apply, hi]
  have hs : ¬ (l : ℤ) ∣ (N * Q : ℤ) := by
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    intro h
    rcases hp.dvd_or_dvd h with h1 | h1
    · exact hN (Int.natCast_dvd_natCast.1 h1)
    · exact hQ h1
  rw [hsing]
  exact rep_sat_elt l Λ hl hθ ⟨N, hN, hw⟩ (m1 * b - m2) m1 (N * Q) hs
end PI.UnitaryGroupMassFormula.UnimodLocStd
