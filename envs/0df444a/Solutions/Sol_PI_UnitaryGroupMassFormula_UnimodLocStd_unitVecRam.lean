-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.unitVecRam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:49.030217+00:00
-- url     : https://prove2.me/submissions/4df0a54e-f6d8-44df-b042-134f3a0d0c18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RamDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_UnitVecRam
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UnimodLocStd_not_dvd_mul__02e58b10b277
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_H_self_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_im_pi_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_kappa_real
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_conj
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_H_zT
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_kappa_ne
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_elt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_sub
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sqrt_sq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_theta_add_conj
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_zT_sat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_sat_norm
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_sat_pair
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution : UnitVecRam := by
  classical
  intro a b c d ha hd lam hlam m _ _ Λ x0 y0 T i₀ hK x hxs hxT hx z₀ hz₀ hz₀T hz₀x hz₀ne
  obtain ⟨hOK, hΛ, hθ, h1, h2, hl, hQ, hi₀, hT⟩ := hK
  have hdp : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hκ0 : repKappa a b d ha hd lam hlam ≠ 0 := rep_kappa_ne a b d ha hd lam hlam
  have hr0 : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hπ : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by unfold cmTheta; ring
  have hπ0 : (2 * cmTheta b d - b) ≠ 0 := by rw [hπ]; exact mul_ne_zero Complex.I_ne_zero hr0
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hππ : (2 * cmTheta b d - b)⁻¹ * conj (2 * cmTheta b d - b)⁻¹ = (d : ℂ)⁻¹ := by
    rw [map_inv₀, ← mul_inv]
    congr 1
    rw [hπ, map_mul, Complex.conj_I, Complex.conj_ofReal]
    linear_combination (-((Real.sqrt d : ℝ) : ℂ) ^ 2) * Complex.I_sq + rep_sqrt_sq d
  have nz : ∀ {z : ℤ}, ¬ (d : ℤ) ∣ z → (z : ℂ) ≠ 0 := by
    intro z hz h; apply hz; rw [show z = 0 by exact_mod_cast h]; exact dvd_zero _

  obtain ⟨n0, s0, hs0, e0⟩ := sat_norm hOK hΛ hθ hl hz₀
  have hn0 : n0 ≠ 0 := by
    intro h
    apply H_self_ne m (cmL a b d ha hd lam hlam) hz₀ne
    rw [e0, h]; simp
  let P : ℕ → Prop := fun j => SatMem d Λ (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)
  have hbound : ∀ j, P j → j ≤ n0.natAbs := by
    intro j hj
    obtain ⟨p, q, hq, e⟩ := sat_norm hOK hΛ hθ hl hj
    have eH : stdH (cmL a b d ha hd lam hlam) m (((2 * cmTheta b d - b)⁻¹) ^ j • z₀) (((2 * cmTheta b d - b)⁻¹) ^ j • z₀)
        = ((d : ℂ)⁻¹) ^ j * stdH (cmL a b d ha hd lam hlam) m z₀ z₀ := by
      rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, map_pow,
        ← mul_assoc, ← mul_pow, hππ]
    rw [eH, e0] at e
    have e' : repKappa a b d ha hd lam hlam * ((p : ℂ) / q) =
        repKappa a b d ha hd lam hlam * ((n0 : ℂ) / ((s0 : ℂ) * (d : ℂ) ^ j)) := by
      calc _ = repKappa a b d ha hd lam hlam * p / q := by ring
        _ = _ := e.symm
        _ = _ := by ring
    have e'' := mul_left_cancel₀ hκ0 e'
    rw [div_eq_div_iff (nz hq) (mul_ne_zero (nz hs0) (pow_ne_zero _ hdc))] at e''
    have hZ : p * (s0 * (d : ℤ) ^ j) = n0 * q := by exact_mod_cast e''
    have hdj : (d : ℤ) ^ j ∣ n0 := by
      have h' : (d : ℤ) ^ j ∣ n0 * q := ⟨p * s0, by rw [← hZ]; ring⟩
      have hcop : IsCoprime ((d : ℤ) ^ j) q := IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hdp).mpr hq)
      exact hcop.dvd_of_dvd_mul_right h'
    have hle : d ^ j ≤ n0.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdj
      rw [Int.natAbs_pow, Int.natAbs_natCast] at this
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn0) this
    have hlt : j < d ^ j := Nat.lt_pow_self hl.one_lt
    omega
  have hP0 : P 0 := by simpa [P] using hz₀
  set J := Nat.findGreatest P n0.natAbs with hJ
  have hPJ : P J := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hPJ1 : ¬ P (J + 1) := by
    intro h
    by_cases hle : J + 1 ≤ n0.natAbs
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hle h
    · exact hle (hbound _ h)
  set xh : m → ℂ := ((2 * cmTheta b d - b)⁻¹) ^ J • z₀ with hxh
  have hxhT : ∀ j ∈ T, xh j = 0 := by intro j hj; simp [xh, hz₀T j hj]
  have hxhx : stdH (cmL a b d ha hd lam hlam) m xh x = 0 := by
    rw [hxh, LinearMap.map_smul, LinearMap.smul_apply, hz₀x, smul_zero]
  have hnot : ¬ SatMem d Λ ((2 * cmTheta b d - b)⁻¹ • xh) := by
    rw [hxh, smul_smul, ← pow_succ']; exact hPJ1
  have hxhs : SatMem d Λ xh := hPJ
  obtain ⟨s, hs, hsx⟩ := hPJ
  have hs' : ¬ (d : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)

  obtain ⟨y, hy, n, c₂, hny, hdn⟩ : ∃ y ∈ Λ, ∃ n c₂ : ℤ,
      stdH (cmL a b d ha hd lam hlam) m (s • xh) y = repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) ∧
      ¬ (d : ℤ) ∣ 2 * n - c₂ * b := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    refine ⟨s, hs, ?_⟩
    rw [smul_comm, ← hΛ]
    intro y' hy'
    obtain ⟨n', c', e1, -⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsx hy'
    obtain ⟨k, hk⟩ := hcon y' hy' n' c' e1
    refine ⟨-k, ?_⟩
    unfold altE
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, e1, im_pi_inv, hk]
    push_cast
    field_simp

  set yz := zT T y with hyzdef
  have hyz : SatMem d Λ yz := rep_zT_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x0 y0 hQ T hT hy
  set μ := stdH (cmL a b d ha hd lam hlam) m yz x / stdH (cmL a b d ha hd lam hlam) m x x with hμdef
  set y' := yz - μ • x with hy'def
  have hy's : SatMem d Λ y' := by
    rcases hx with rfl | ⟨p, q, hp, hq, e⟩
    · simpa [y'] using hyz
    · obtain ⟨n2, c3, s2, hs2, e2⟩ := sat_pair hOK hΛ hθ hl hyz hxs
      have hμ : μ = (((q * n2 : ℤ) : ℂ) - ((q * c3 : ℤ) : ℂ) * conj (cmTheta b d)) / ((s2 * p : ℤ) : ℂ) := by
        have hp0 := nz hp
        have hq0 := nz hq
        have hs20 := nz hs2
        rw [hμdef, e2, e]
        push_cast
        field_simp
      refine rep_sat_sub d Λ hl hyz ?_
      rw [hμ]
      exact rep_sat_elt d Λ hl hθ hxs _ _ _ (not_dvd_mul' hl hs2 hp)
  have hy'T : ∀ j ∈ T, y' j = 0 := by
    intro j hj; simp [y', yz, zT, hj, hxT j hj]
  have hy'x : stdH (cmL a b d ha hd lam hlam) m y' x = 0 := by
    rcases hx with rfl | ⟨p, q, hp, hq, e⟩
    · simp
    · have hxx : stdH (cmL a b d ha hd lam hlam) m x x ≠ 0 := by
        rw [e]; exact div_ne_zero (mul_ne_zero hκ0 (nz hp)) (nz hq)
      rw [hy'def, map_sub, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hμdef,
        div_mul_cancel₀ _ hxx, sub_self]
  have hxhy' : stdH (cmL a b d ha hd lam hlam) m xh y' = stdH (cmL a b d ha hd lam hlam) m xh y := by
    rw [hy'def, map_sub, (stdH (cmL a b d ha hd lam hlam) m xh).map_smulₛₗ μ x, hxhx, smul_zero, sub_zero]
    exact rep_H_zT a b d ha hd lam hlam m T hxhT
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast nz hs'
  have hxhy : stdH (cmL a b d ha hd lam hlam) m xh y =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s := by
    have e3 : stdH (cmL a b d ha hd lam hlam) m (s • xh) y = (s : ℂ) * stdH (cmL a b d ha hd lam hlam) m xh y := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hny] at e3
    rw [eq_div_iff hsc]
    linear_combination (-1 : ℂ) * e3

  obtain ⟨p1, q1, hq1, e1⟩ := sat_norm hOK hΛ hθ hl hxhs
  obtain ⟨p2, q2, hq2, e2⟩ := sat_norm hOK hΛ hθ hl hy's
  by_cases hp1 : (d : ℤ) ∣ p1
  · by_cases hp2 : (d : ℤ) ∣ p2
    · refine ⟨xh + y', rep_sat_add d Λ hl hxhs hy's, ?_, ?_, ?_⟩
      · intro j hj; simp [hxhT j hj, hy'T j hj]
      · rw [map_add, LinearMap.add_apply, hxhx, hy'x, add_zero]
      · refine ⟨p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2, q1 * q2 * s, ?_,
          not_dvd_mul' hl (not_dvd_mul' hl hq1 hq2) hs', ?_⟩
        · intro hdv
          have e4 : (2 * n - c₂ * b) * q1 * q2 =
              (p1 * q2 * s + p2 * q1 * s + (2 * n - c₂ * b) * q1 * q2) - (p1 * q2 * s + p2 * q1 * s) := by ring
          have : (d : ℤ) ∣ (2 * n - c₂ * b) * q1 * q2 := by
            rw [e4]
            exact dvd_sub hdv (dvd_add ((hp1.mul_right _).mul_right _) ((hp2.mul_right _).mul_right _))
          exact not_dvd_mul' hl (not_dvd_mul' hl hdn hq1) hq2 this
        · have hyx : stdH (cmL a b d ha hd lam hlam) m y' xh =
              repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * cmTheta b d) / s := by
            rw [← rep_H_conj (cmL a b d ha hd lam hlam) m xh y', hxhy', hxhy]
            simp only [map_div₀, map_mul, map_sub, map_intCast, map_natCast, Complex.conj_conj,
              kappa_real a b d ha hd lam hlam]
          rw [map_add (stdH (cmL a b d ha hd lam hlam) m) xh y', LinearMap.add_apply, map_add, map_add, e1, e2, hxhy',
            hxhy, hyx]
          have htb := rep_theta_add_conj b d
          have hA : (q1 : ℂ) * (q1 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (nz hq1)
          have hB : (q2 : ℂ) * (q2 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (nz hq2)
          have hC : (s : ℂ) * (s : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hsc
          set κ := repKappa a b d ha hd lam hlam
          push_cast
          simp only [div_eq_mul_inv, mul_inv]
          linear_combination
            (-κ * p2 * (q2 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b) * ((q2 : ℂ) * (q2 : ℂ)⁻¹)) * hA +
            (-κ * p1 * (q1 : ℂ)⁻¹ * ((s : ℂ) * (s : ℂ)⁻¹) - κ * (s : ℂ)⁻¹ * (2 * n - c₂ * b)) * hB +
            (-κ * p1 * (q1 : ℂ)⁻¹ - κ * p2 * (q2 : ℂ)⁻¹) * hC +
            (-κ * (s : ℂ)⁻¹ * c₂) * htb
    · exact ⟨y', hy's, hy'T, hy'x, p2, q2, hp2, hq2, e2⟩
  · exact ⟨xh, hxhs, hxhT, hxhx, p1, q1, hp1, hq1, e1⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
