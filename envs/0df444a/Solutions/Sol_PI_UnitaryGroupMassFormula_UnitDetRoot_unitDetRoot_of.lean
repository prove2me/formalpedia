-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.unitDetRoot_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:45.397134+00:00
-- url     : https://prove2.me/submissions/1e2cefd6-0509-46b3-8d47-95da4e2b59c1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_UnitDetRootOf

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (h1 : DetInK) (h2 : LocalStd) (h3 : GlobalLUnit) (h4 : NormOne)
    (h5 : RootStep) (h6 : ConjMem) (h7 : ConjLUnit) : PI.UnitDetRoot := by
  intro a b c d ha hd lam hlam hOK m _ _ Λa hSD hθ hi1 hi2
  have hH : Hyp a b c d ha hd lam hlam m Λa := ⟨hOK, hSD, hθ, hi1, hi2⟩
  obtain ⟨γ, hγK, hγ0, n, hn, hγ⟩ := h3 a b c d ha hd lam hlam m Λa hH
  have hγc0 : conj γ ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hγ0
  have hβK : γ / conj γ ∈ KF b d := div_mem hγK (h6 b d γ hγK)
  have hββ : γ / conj γ * conj (γ / conj γ) = 1 := by
    rw [map_div₀, Complex.conj_conj]
    field_simp
  obtain ⟨κ, hκN, hκalg, hκσ⟩ := h5 a b c d hOK (γ / conj γ) hβK hββ (4 * n) (by omega)
  refine ⟨κ, ?_, hκalg, hκσ, ?_⟩
  · rintro rfl
    rw [zero_pow (by omega), eq_comm, inv_eq_zero, div_eq_zero_iff] at hκN
    exact hκN.elim hγ0 hγc0
  · intro l _ ι δ hIso hidx1 hnl hidx2
    have hA : admitted a b d ha hd lam hlam m Λa δ := ⟨hIso, hidx1, hidx2⟩
    have hEq := h2 a b c d ha hd lam hlam m Λa hH l δ hA hnl
    have hU := hγ l δ hA hEq
    have n1 := h4 l ι _ hU
    have n2 := h4 l ι _ (h7 l _ hU)
    obtain ⟨-, hdd⟩ := h1 a b c d ha hd lam hlam m Λa hH δ hA
    set D := LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) with hD
    have hD0 : D ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hdd
      exact zero_ne_one hdd
    have hDc : conj D = D⁻¹ := eq_inv_of_mul_eq_one_right hdd
    have hu0 : 0 < ‖ι D‖ := norm_pos_iff.mpr ((map_ne_zero ι).mpr hD0)
    have hDc0 : conj D ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hD0
    have n1' : ‖ι γ‖ = ‖ι D‖ ^ n := by
      have e : γ = (γ / D ^ n) * D ^ n := by field_simp
      rw [e, map_mul, norm_mul, n1, one_mul, map_pow, norm_pow]
    have n2' : ‖ι (conj γ)‖ = ‖ι D‖⁻¹ ^ n := by
      have e : conj γ = conj (γ / D ^ n) * (conj D) ^ n := by
        rw [map_div₀, map_pow]
        field_simp
      rw [e, map_mul, norm_mul, n2, one_mul, map_pow, norm_pow, hDc, map_inv₀, norm_inv]
    have e3 : ‖ι κ‖ ^ (4 * n) = ‖ι (conj γ)‖ / ‖ι γ‖ := by
      rw [← norm_pow, ← map_pow, hκN, inv_div, map_div₀, norm_div]
    have ht : (‖ι κ‖ ^ 2 * ‖ι D‖) ^ (2 * n) = 1 := by
      rw [mul_pow, ← pow_mul, show 2 * (2 * n) = 4 * n by ring, e3, n1', n2', inv_pow]
      field_simp
      ring
    exact (pow_eq_one_iff_of_nonneg (by positivity) (by omega)).mp ht
end PI.UnitaryGroupMassFormula.UnitDetRoot
