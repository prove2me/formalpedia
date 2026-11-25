-- Prove2me | solution 1 for PI.KerLat.PerPairProof.indep_of_im_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:47:39.905465+00:00
-- url     : https://prove2.me/submissions/7ec720d1-f5c6-4842-86a7-de35c450696b

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
theorem _root_.solution {a b : ℂ} (h : (conj a * b).im ≠ 0) : LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h
  simp only [Complex.real_smul] at hst
  have h2 := congrArg Complex.im (congrArg (fun z => conj a * z) hst)
  simp only [mul_zero, Complex.zero_im] at h2
  have e1 : (conj a * ((s : ℂ) * a)).im = 0 := by
    rw [mul_left_comm, mul_comm (conj a) a, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_im]
  have e2 : (conj a * ((t : ℂ) * b)).im = t * (conj a * b).im := by
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [mul_add, Complex.add_im, e1, e2, zero_add] at h2
  have ht : t = 0 := (mul_eq_zero.1 h2).resolve_right h
  refine ⟨?_, ht⟩
  rw [ht, Complex.ofReal_zero, zero_mul, add_zero] at hst
  exact (mul_eq_zero.1 hst).resolve_right ha |> Complex.ofReal_eq_zero.1
end PI.KerLat.PerPairProof
