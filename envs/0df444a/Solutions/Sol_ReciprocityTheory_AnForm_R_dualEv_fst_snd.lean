-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.dualEv_fst_snd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:43.076129+00:00
-- url     : https://prove2.me/submissions/fe842261-9ea9-40fd-b21b-da35fc5accc0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (p v : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) :
    (dualEv p v h).fst = eval p h ∧
      (dualEv p v h).snd = ∑ j, eval p (pderiv j h) * v j := by
  induction h using MvPolynomial.induction_on
  next a =>
    simp [dualEv, TrivSqZeroExt.algebraMap_eq_inl]
  next q r hq hr =>
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨h3, h4⟩ := hr
    refine ⟨?_, ?_⟩
    · rw [map_add, TrivSqZeroExt.fst_add, h1, h3, map_add]
    · rw [map_add, TrivSqZeroExt.snd_add, h2, h4, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_add, map_add, add_mul]
  next q i hq =>
    obtain ⟨h1, h2⟩ := hq
    have hX : dualEv p v (X i) = TrivSqZeroExt.inl (p i) + v i • DualNumber.eps := by
      simp [dualEv]
    refine ⟨?_, ?_⟩
    · rw [map_mul, TrivSqZeroExt.fst_mul, h1, hX]
      simp
    · rw [map_mul, TrivSqZeroExt.snd_mul, h1, h2, hX]
      simp [Derivation.leibniz, pderiv_X, Pi.single_apply, Finset.sum_add_distrib, add_mul, Finset.mul_sum,
        DualNumber.snd_eps, DualNumber.fst_eps]
      have e1 : (∑ x, (eval p) (if i = x then q else 0) * v x) = eval p q * v i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      rw [e1, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun x _ => by ring
end ReciprocityTheory.AnForm.R
