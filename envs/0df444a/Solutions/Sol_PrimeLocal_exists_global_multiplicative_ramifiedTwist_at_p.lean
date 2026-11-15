-- Prove2me | solution 1 for PrimeLocal.exists_global_multiplicative_ramifiedTwist_at_p
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:13:23.69512+00:00
-- url     : https://prove2.me/submissions/0bd68071-b262-4dde-abd2-de4c21d274fd

import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open IsLocalRing IsDedekindDomain.HeightOneSpectrum
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
/-- The ramified quadratic twist of a minimal potentially multiplicative equation is multiplicative. -/
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} [Fact p.Prime] (hmin : WeierstrassCurve.IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p]))) (hp5 : 5 ≤ p) (hpΔ : (p : ℤ) ∣ W.Δ) (hpc₄ : (p : ℤ) ∣ W.c₄) (hj : ¬ ((p : ℤ) ^ padicValInt p W.Δ ∣ W.c₄ ^ 3)) (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) (hQord : addOrderOf Q = p) : ∃ (W' : WeierstrassCurve ℤ) (Q' : ((W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (s : AlgebraicClosure ℚ), s ^ 2 = (p : AlgebraicClosure ℚ) ∧ W'.Δ ≠ 0 ∧ (p : ℤ) ∣ W'.Δ ∧ ¬ (p : ℤ) ∣ W'.c₄ ∧ addOrderOf Q' = p ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (σ s = s → σ • Q' = Q') ∧ (σ s = -s → σ • Q' = -Q') := by
  classical
  have minimalInvariant (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
      {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
      (hmin : WeierstrassCurve.IsMinimal ℤ_[p] (W.map (Int.castRingHom ℚ_[p]))) :
      ¬ ((p : ℤ)^4 ∣ W.c₄ ∧ (p : ℤ)^6 ∣ W.c₆) := by
    classical
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let V := W.map (Int.castRingHom ℚ_[p])
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    let u : ℚ_[p]ˣ := Units.mk0 ((p : ℚ_[p]) / 6) (div_ne_zero hp0 (by norm_num))
    let C : VariableChange ℚ_[p] :=
      ⟨u, -V.b₂ / 12, -V.a₁ / 2, (V.a₁ * V.b₂ / 12 - V.a₃) / 2⟩
    have hshort (K : Type) [Field K] [CharZero K] (E : WeierstrassCurve K) (u : Kˣ) :
        (⟨u, -E.b₂ / 12, -E.a₁ / 2, (E.a₁ * E.b₂ / 12 - E.a₃) / 2⟩ : VariableChange K) • E =
          (⟨0, 0, 0, -E.c₄ / (48 * (u : K)^4), -E.c₆ / (864 * (u : K)^6)⟩ : WeierstrassCurve K) := by
      ext <;>
        simp only [variableChange_def, WeierstrassCurve.c₄, WeierstrassCurve.c₆,
          WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
          Units.val_inv_eq_inv_val] <;> field_simp <;> ring
    have hC : C • V =
        (⟨0, 0, 0, -27 * (a : ℚ_[p]), -54 * (b : ℚ_[p])⟩ : WeierstrassCurve ℚ_[p]) := by
      rw [show C = (⟨u, -V.b₂ / 12, -V.a₁ / 2, (V.a₁ * V.b₂ / 12 - V.a₃) / 2⟩ : VariableChange ℚ_[p]) from rfl, hshort]
      have ha' : V.c₄ = (p : ℚ_[p])^4 * (a : ℚ_[p]) := by
        simpa [V, map_c₄] using congrArg (Int.castRingHom ℚ_[p]) ha
      have hb' : V.c₆ = (p : ℚ_[p])^6 * (b : ℚ_[p]) := by
        simpa [V, map_c₆] using congrArg (Int.castRingHom ℚ_[p]) hb
      ext <;> simp only [ha', hb', u, Units.val_mk0] <;> field_simp <;> ring
    let : WeierstrassCurve.IsMinimal ℤ_[p] V := hmin
    let : WeierstrassCurve.IsIntegral ℤ_[p] (C • V) := by
      refine ⟨(⟨0, 0, 0, -27 * a, -54 * b⟩ : WeierstrassCurve ℤ).map (Int.castRingHom ℤ_[p]), ?_⟩
      rw [hC]
      ext <;> simp [WeierstrassCurve.baseChange]
      · left; change (27 : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] 27; simp only [map_ofNat]
      · left; change (54 : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] 54; simp only [map_ofNat]
    have hp6 : ¬ p ∣ 6 := by
      intro h
      rcases hp.out.dvd_mul.mp (show p ∣ 2 * 3 from h) with h | h
      · have := Nat.le_of_dvd (by norm_num : 0 < 2) h; omega
      · have := Nat.le_of_dvd (by norm_num : 0 < 3) h; omega
    have hn6 : ‖(6 : ℚ_[p])‖ = 1 := by
      exact (Padic.norm_natCast_eq_one_iff).mpr ((hp.out.coprime_iff_not_dvd).mpr hp6)
    have hnorm : ‖(C.u : ℚ_[p])‖ < 1 := by
      change ‖(p : ℚ_[p]) / 6‖ < 1
      rw [norm_div, hn6, div_one, Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    let z : ℤ_[p] := ⟨(C.u : ℚ_[p]), hnorm.le⟩
    have hz : z ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact PadicInt.not_isUnit_iff.mpr hnorm
    let v := (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p]
    have hvu : v (C.u : ℚ_[p]) < 1 := by
      exact (valuation_lt_one_iff_mem (K := ℚ_[p]) (IsDiscreteValuationRing.maximalIdeal ℤ_[p]) z).mpr hz
    have hvu0 : v (C.u : ℚ_[p]) ≠ 0 := by simp [v]
    have hVΔ : V.Δ ≠ 0 := by simpa [V] using (Int.cast_ne_zero.mpr hΔ : (W.Δ : ℚ_[p]) ≠ 0)
    have hvΔ : 0 < v V.Δ := by exact pos_iff_ne_zero.mpr (by simpa [v] using hVΔ)
    have hinv : 1 < (v (C.u : ℚ_[p]))⁻¹ := (one_lt_inv₀ (pos_iff_ne_zero.mpr hvu0)).mpr hvu
    have hstrict : v V.Δ < v (C • V).Δ := by
      rw [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
      change v V.Δ < (v (C.u : ℚ_[p]))⁻¹ ^ 12 * v V.Δ
      exact lt_mul_of_one_lt_left hvΔ (one_lt_pow₀ hinv (by norm_num))
    have hstrict' : valuation_Δ_aux ℤ_[p] V < valuation_Δ_aux ℤ_[p] (C • V) := by
      change (valuation_Δ_aux ℤ_[p] V : WithZero (Multiplicative ℤ)) <
        (valuation_Δ_aux ℤ_[p] (C • V) : WithZero (Multiplicative ℤ))
      simpa only [valuation_Δ_aux_eq_of_isIntegral] using hstrict
    have hle := hmin.val_Δ_maximal.2 (show WeierstrassCurve.IsIntegral ℤ_[p] (C • V) from inferInstance)
      (show valuation_Δ_aux ℤ_[p] ((1 : VariableChange ℚ_[p]) • V) ≤ valuation_Δ_aux ℤ_[p] (C • V) by simpa using hstrict'.le)
    exact (not_le_of_gt hstrict') (by simpa using hle)
  have invariantValuations (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} [Fact p.Prime]
      (hp5 : 5 ≤ p) (hpc₄ : (p : ℤ) ∣ W.c₄)
      (hj : ¬ ((p : ℤ) ^ padicValInt p W.Δ ∣ W.c₄ ^ 3))
      (hnm : ¬ ((p : ℤ)^4 ∣ W.c₄ ∧ (p : ℤ)^6 ∣ W.c₆)) :
      padicValInt p W.c₄ = 2 ∧ padicValInt p W.c₆ = 3 ∧ 6 < padicValInt p W.Δ := by
    have hc4 : W.c₄ ≠ 0 := by
      intro h
      apply hj
      rw [h, zero_pow (by decide : 3 ≠ 0)]
      exact dvd_zero _
    have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
    have hpow : ∀ (z : ℤ) (n : ℕ), padicValInt p (z ^ n) = n * padicValInt p z := by
      intro z n
      simp only [padicValInt, Int.natAbs_pow, padicValNat.pow]
    have hlt : 3 * padicValInt p W.c₄ < padicValInt p W.Δ := by
      rw [padicValInt_dvd_iff] at hj
      rw [hpow] at hj
      omega
    have hpos : 0 < padicValInt p W.c₄ := by
      have hh := (padicValInt_dvd_iff 1 W.c₄).mp (by simpa using hpc₄)
      rcases hh with hh | hh
      · exact (hc4 hh).elim
      · omega
    have hp2 : ¬ (p : ℤ) ∣ 2 := by
      intro h
      have h' : p ∣ 2 := by exact_mod_cast h
      have := Nat.le_of_dvd (by decide : 0 < 2) h'
      omega
    have hp3 : ¬ (p : ℤ) ∣ 3 := by
      intro h
      have h' : p ∣ 3 := by exact_mod_cast h
      have := Nat.le_of_dvd (by decide : 0 < 3) h'
      omega
    have hp1728 : ¬ (p : ℤ) ∣ 1728 := by
      have hprime : Prime (p : ℤ) := (Nat.prime_iff_prime_int).mp (Fact.out : p.Prime)
      rw [show (1728 : ℤ) = 2 ^ 6 * 3 ^ 3 by norm_num]
      intro h
      rcases hprime.dvd_mul.mp h with h | h
      · exact hp2 (hprime.dvd_of_dvd_pow h)
      · exact hp3 (hprime.dvd_of_dvd_pow h)
    have h1728 : padicValInt p (1728 * W.Δ) = padicValInt p W.Δ := by
      rw [padicValInt.mul (by norm_num) hΔ, padicValInt.eq_zero_of_not_dvd hp1728, zero_add]
    have hid : W.c₄ ^ 3 - W.c₆ ^ 2 = 1728 * W.Δ := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.Δ,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    have hc6 : W.c₆ ≠ 0 := by
      intro h
      have hh := congrArg (padicValInt p) hid
      rw [h, zero_pow (by decide : 2 ≠ 0), sub_zero, hpow, h1728] at hh
      omega
    have hvq : ∀ z : ℤ, padicValRat p (z : ℚ) = (padicValInt p z : ℤ) := by
      intro z
      simp
    have hrel : 2 * padicValInt p W.c₆ = 3 * padicValInt p W.c₄ := by
      have he : (W.c₆ : ℚ) ^ 2 = (W.c₄ : ℚ) ^ 3 + -((1728 * W.Δ : ℤ) : ℚ) := by
        exact_mod_cast (show W.c₆ ^ 2 = W.c₄ ^ 3 + -(1728 * W.Δ) by linear_combination -hid)
      have hc4q : (W.c₄ : ℚ) ^ 3 ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.mpr hc4)
      have hdq : -((1728 * W.Δ : ℤ) : ℚ) ≠ 0 := neg_ne_zero.mpr (Int.cast_ne_zero.mpr (mul_ne_zero (by norm_num) hΔ))
      have hs : (W.c₄ : ℚ) ^ 3 + -((1728 * W.Δ : ℤ) : ℚ) ≠ 0 := by
        rw [← he]
        exact pow_ne_zero _ (Int.cast_ne_zero.mpr hc6)
      have hval : padicValRat p ((W.c₄ : ℚ) ^ 3) < padicValRat p (-((1728 * W.Δ : ℤ) : ℚ)) := by
        rw [padicValRat.pow, padicValRat.neg, hvq, hvq, h1728]
        exact_mod_cast hlt
      have hh := padicValRat.add_eq_of_lt hs hc4q hdq hval
      rw [← he, padicValRat.pow, padicValRat.pow, hvq, hvq] at hh
      exact_mod_cast hh
    have ha4 : padicValInt p W.c₄ < 4 := by
      by_contra h
      apply hnm
      constructor
      · exact (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))
      · exact (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))
    omega
  have twistReduction (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} [Fact p.Prime]
      (hp5 : 5 ≤ p) (a b : ℤ)
      (ha : (p : ℤ)^2 * a = W.c₄) (hb : (p : ℤ)^3 * b = W.c₆)
      (hva : padicValInt p W.c₄ = 2) (hvd : 6 < padicValInt p W.Δ) :
      let D : WeierstrassCurve ℤ := ⟨0, 0, 0, -27*a, -54*b⟩
      D.Δ ≠ 0 ∧ (p : ℤ) ∣ D.Δ ∧ ¬ (p : ℤ) ∣ D.c₄ := by
    let D : WeierstrassCurve ℤ := ⟨0, 0, 0, -27*a, -54*b⟩
    change D.Δ ≠ 0 ∧ (p : ℤ) ∣ D.Δ ∧ ¬ (p : ℤ) ∣ D.c₄
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hp6 : (p : ℤ)^6 ≠ 0 := pow_ne_zero _ hp0
    have hid : W.c₄ ^ 3 - W.c₆ ^ 2 = 1728 * W.Δ := by
      simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.Δ,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    have hDc : D.c₄ = 6^4*a := by
      dsimp [D, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
      ring
    have hDd : D.Δ = 1259712 * (a^3-b^2) := by
      dsimp [D, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring
    have hrel : (p : ℤ)^6 * D.Δ = 6^12 * W.Δ := by
      rw [← ha, ← hb] at hid
      rw [hDd]
      linear_combination 1259712 * hid
    have hDn : D.Δ ≠ 0 := by
      intro h
      rw [h, mul_zero] at hrel
      exact hΔ ((mul_eq_zero.mp hrel.symm).resolve_left (by norm_num))
    have hd7 : (p : ℤ)^7 ∣ W.Δ :=
      (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))
    have hDp : (p : ℤ) ∣ D.Δ := by
      obtain ⟨z, hz⟩ := hd7
      refine ⟨6^12*z, ?_⟩
      apply mul_left_cancel₀ hp6
      rw [hrel, hz]
      ring
    have hc4 : W.c₄ ≠ 0 := by
      intro h
      rw [h, padicValInt.zero] at hva
      omega
    have hpa : ¬ (p : ℤ) ∣ a := by
      rintro ⟨z, hz⟩
      have hd3 : (p : ℤ)^3 ∣ W.c₄ := by
        refine ⟨z, ?_⟩
        rw [← ha, hz]
        ring
      have hh := (padicValInt_dvd_iff _ _).mp hd3
      rw [hva] at hh
      rcases hh with hh | hh
      · exact hc4 hh
      · omega
    have hp6nd : ¬ (p : ℤ) ∣ 6 := by
      intro h
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
      rw [show (6 : ℤ) = 2*3 by norm_num] at h
      rcases hpz.dvd_mul.mp h with h | h
      · have hh : p ∣ 2 := by exact_mod_cast h
        have := Nat.le_of_dvd (by decide : 0 < 2) hh
        omega
      · have hh : p ∣ 3 := by exact_mod_cast h
        have := Nat.le_of_dvd (by decide : 0 < 3) hh
        omega
    refine ⟨hDn, hDp, ?_⟩
    rw [hDc]
    intro h
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
    rcases hpz.dvd_mul.mp h with h | h
    · exact hp6nd (hpz.dvd_of_dvd_pow h)
    · exact hpa h
  have twistAlgebra (W : WeierstrassCurve ℤ) (p : ℕ) (a b : ℤ)
      (ha : (p : ℤ)^2 * a = W.c₄) (hb : (p : ℤ)^3 * b = W.c₆)
      (s : AlgebraicClosure ℚ) (hs : s^2 = (p : AlgebraicClosure ℚ)) (hs0 : s ≠ 0) :
      let E := (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))
      let D : WeierstrassCurve ℤ := ⟨0, 0, 0, -27*a, -54*b⟩
      let C : VariableChange (AlgebraicClosure ℚ) :=
        ⟨Units.mk0 (s / 6) (div_ne_zero hs0 (by norm_num)),
         -(W.b₂ : AlgebraicClosure ℚ)/12, -(W.a₁ : AlgebraicClosure ℚ)/2,
         ((W.a₁ : AlgebraicClosure ℚ)*(W.b₂ : AlgebraicClosure ℚ)/12 - W.a₃)/2⟩
      C • E = (D.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ)) := by
    dsimp only
    have ha' : (p : AlgebraicClosure ℚ)^2 * a = W.c₄ := by exact_mod_cast ha
    have hb' : (p : AlgebraicClosure ℚ)^3 * b = W.c₆ := by exact_mod_cast hb
    have hs4 : s^4 = (p : AlgebraicClosure ℚ)^2 := by rw [show 4 = 2*2 by omega, pow_mul, hs]
    have hs6 : s^6 = (p : AlgebraicClosure ℚ)^3 := by rw [show 6 = 2*3 by omega, pow_mul, hs]
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_pow, Int.cast_ofNat, Int.cast_neg] at ha' hb'
    ext
    all_goals simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      Units.val_inv_eq_inv_val, Units.val_mk0, eq_intCast, map_intCast,
      Int.cast_mul, Int.cast_ofNat, _root_.map_zero, _root_.map_neg, _root_.map_mul, map_ofNat, WeierstrassCurve.b₂, Int.cast_add, Int.cast_pow]
    all_goals field_simp
    all_goals try ring_nf
    all_goals try rw [hs4]
    all_goals try rw [hs6]
    all_goals first | linear_combination 373248 * hb' | linear_combination 7776 * ha'
  have twistTransport (W D : WeierstrassCurve ℤ) (p : ℕ) (hp : p.Prime)
      (s : AlgebraicClosure ℚ) (hs : s^2 = (p : AlgebraicClosure ℚ)) (hs0 : s ≠ 0)
      (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
      (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
      (hQord : addOrderOf Q = p)
      (hDa1 : D.a₁ = 0) (hDa3 : D.a₃ = 0)
      (hC : (⟨Units.mk0 (s / 6) (div_ne_zero hs0 (by norm_num)),
         -(W.b₂ : AlgebraicClosure ℚ)/12, -(W.a₁ : AlgebraicClosure ℚ)/2,
         ((W.a₁ : AlgebraicClosure ℚ)*(W.b₂ : AlgebraicClosure ℚ)/12 - W.a₃)/2⟩ :
         VariableChange (AlgebraicClosure ℚ)) •
         ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) =
         ((D.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ))) :
      ∃ Q' : ((D.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
        addOrderOf Q' = p ∧ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (σ s = s → σ • Q' = Q') ∧ (σ s = -s → σ • Q' = -Q') := by
    classical
    let E := ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ))
    let E' := ((D.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ))
    let C : VariableChange (AlgebraicClosure ℚ) :=
      ⟨Units.mk0 (s / 6) (div_ne_zero hs0 (by norm_num)),
       -(W.b₂ : AlgebraicClosure ℚ)/12, -(W.a₁ : AlgebraicClosure ℚ)/2,
       ((W.a₁ : AlgebraicClosure ℚ)*(W.b₂ : AlgebraicClosure ℚ)/12 - W.a₃)/2⟩
    let f : E.toAffine.Point →+ (C • E).toAffine.Point :=
      { toFun := Point.vcInvFun C E.toAffine
        map_zero' := rfl
        map_add' := Point.vcInvFun_add C E.toAffine }
    have hf : Function.Injective f := (Point.variableChangeEquiv C E.toAffine).symm.injective
    have hor : addOrderOf (f Q) = p := (addOrderOf_injective f hf Q).trans hQord
    cases Q with
    | zero =>
      change addOrderOf (0 : E.toAffine.Point) = p at hQord
      rw [addOrderOf_zero] at hQord
      exact (hp.ne_one hQord.symm).elim
    | some x y h =>
      have hxy : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ x = x ∧ σ y = y := by
        intro σ
        have hh := hQfix σ
        change Point.map σ.toAlgHom (Point.some x y h) = Point.some x y h at hh
        exact Point.some.inj hh
      let X := vcXInv C x
      let Y := vcYInv C x y
      have hns : E'.toAffine.Nonsingular X Y := by
        change E'.toAffine.Nonsingular X Y
        change C • E = E' at hC
        rw [← hC]
        exact (nonsingular_variableChange_iff X Y).mpr (by simpa [X, Y] using h)
      refine ⟨Point.some X Y hns, ?_, ?_⟩
      · have hh : ∀ (V : WeierstrassCurve (AlgebraicClosure ℚ)) (he : C • E = V)
            (hns' : V.toAffine.Nonsingular X Y), addOrderOf (Point.some X Y hns') = p := by
          intro V he hns'
          subst V
          exact hor
        exact hh E' hC hns
      · intro σ
        have hx : σ X = X := by
          have hpow : (σ s)^2 = s^2 := by rw [← map_pow, hs]; simp
          simp only [X, vcXInv, C, Units.val_inv_eq_inv_val, Units.val_mk0,
            _root_.map_mul, map_pow, _root_.map_sub, _root_.map_neg, map_intCast,
            map_inv₀, map_div₀, map_ofNat, (hxy σ).1]
          try norm_num
          simp only [div_pow, hpow]
          simp

        have hy (e : AlgebraicClosure ℚ) (he : σ s = e) :
            σ Y = (e / 6)⁻¹ ^ 3 *
              (y - (((W.a₁ : AlgebraicClosure ℚ)*(W.b₂ : AlgebraicClosure ℚ)/12 - W.a₃)/2) -
               (-(W.a₁ : AlgebraicClosure ℚ)/2) * (x - (-(W.b₂ : AlgebraicClosure ℚ)/12))) := by
          simp only [Y, vcYInv, C, Units.val_inv_eq_inv_val, Units.val_mk0, _root_.map_mul, map_pow, _root_.map_sub, _root_.map_neg, map_intCast, map_inv₀, map_div₀, map_ofNat, (hxy σ).1, (hxy σ).2, he]
          try norm_num
        constructor
        · intro he
          have hy' : σ Y = Y := by simpa [Y, vcYInv, C] using hy s he
          change Point.map σ.toAlgHom (Point.some X Y hns) = Point.some X Y hns
          rw [Point.map_some]
          congr 1
        · intro he
          have hy' : σ Y = -Y := by
            rw [hy (-s) he]
            simp [Y, vcYInv, C, neg_div]
            ring
          change Point.map σ.toAlgHom (Point.some X Y hns) = -Point.some X Y hns
          simp only [Point.map_some, Point.neg_some]
          congr 1
          simpa [E', hDa1, hDa3] using hy'
  have hnm := minimalInvariant W hΔ hp5 hmin
  obtain ⟨hv4, hv6, hvΔ⟩ := invariantValuations W hΔ hp5 hpc₄ hj hnm
  obtain ⟨a, ha⟩ : (p : ℤ)^2 ∣ W.c₄ :=
    (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))
  obtain ⟨b, hb⟩ : (p : ℤ)^3 ∣ W.c₆ :=
    (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))
  let D : WeierstrassCurve ℤ := ⟨0, 0, 0, -27*a, -54*b⟩
  have hred : D.Δ ≠ 0 ∧ (p : ℤ) ∣ D.Δ ∧ ¬ (p : ℤ) ∣ D.c₄ :=
    twistReduction W hΔ hp5 a b ha.symm hb.symm hv4 hvΔ
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (p : AlgebraicClosure ℚ) (n := 2) (by norm_num)
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num : 2 ≠ 0)] at hs
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hs.symm
  have hC := twistAlgebra W p a b ha.symm hb.symm s hs hs0
  obtain ⟨Q', hord, hsign⟩ :=
    twistTransport W D p (Fact.out : p.Prime) s hs hs0 Q hQfix hQord rfl rfl hC
  exact ⟨D, Q', s, hs, hred.1, hred.2.1, hred.2.2, hord, hsign⟩

end PrimeLocal
