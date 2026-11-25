-- Prove2me | solution 1 for PI.KerLat.PerPairProof.im_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:38.022274+00:00
-- url     : https://prove2.me/submissions/68a85276-4c68-4d79-9561-610e1c76a3e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PeriodPairIndependence_IndepOfImNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField ComplexConjugate
open scoped nonZeroDivisors
open PI PI.KerLat PI.KerLat.PerPairProof
namespace PI.KerLat.PerPairProof
theorem _root_.solution {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (hφ : ∃ k : K, (φ k).im ≠ 0)
    (B : Module.Basis (Fin 2) ℚ K) : (conj (φ (B 0)) * φ (B 1)).im ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := hφ
  have hB0 : φ (B 0) ≠ 0 := (map_ne_zero φ).2 (B.ne_zero 0)
  have hs : ∀ (q : ℚ) (v : K),
      (conj (φ (B 0)) * φ (q • v)).im = (q : ℝ) * (conj (φ (B 0)) * φ v).im := by
    intro q v
    rw [Rat.smul_def, map_mul, map_ratCast, mul_left_comm, ← Complex.ofReal_ratCast,
      Complex.im_ofReal_mul]
  have e0 : (conj (φ (B 0)) * φ (B 0)).im = 0 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_im]
  have key : ∀ x : K, (conj (φ (B 0)) * φ x).im = 0 := by
    intro x
    rw [← B.sum_repr x, map_sum, Finset.mul_sum, Complex.im_sum, Fin.sum_univ_two, hs, hs, e0, h0]
    simp
  have h1 := key 1
  rw [map_one, mul_one, Complex.conj_im, neg_eq_zero] at h1
  have h2 := key k
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, h1, neg_zero, zero_mul, add_zero] at h2
  have hre : (φ (B 0)).re ≠ 0 := fun hr => hB0 (Complex.ext hr h1)
  exact hk ((mul_eq_zero.1 h2).resolve_left hre)
end PI.KerLat.PerPairProof
