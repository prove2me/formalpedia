-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.coeff_evalYZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:56:59.472514+00:00
-- url     : https://prove2.me/submissions/268ea2ea-b1cd-40bb-a068-df704d5d2692

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (F : MvPowerSeries (Fin 2) R) (n : ℕ) :
    coeff n (ev0 F) = MvPowerSeries.coeff (Finsupp.single 0 n) F := by
  have ha : MvPowerSeries.HasSubst ![(X : PowerSeries R), 0] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => by fin_cases i <;> first | exact PowerSeries.constantCoeff_X | simp)
  have hc : ∀ f : PowerSeries R, MvPowerSeries.coeff (Finsupp.single () n) f = coeff n f := fun f => rfl
  have h := MvPowerSeries.coeff_subst ha F (Finsupp.single () n)
  unfold ev0
  rw [← hc, h, finsum_eq_single _ (Finsupp.single 0 n)]
  · rw [Finsupp.prod_single_index (by simp), hc]
    simp
  · intro d hd
    rw [hc, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    by_cases h1 : d 1 = 0
    · rw [h1, pow_zero, mul_one, coeff_X_pow, if_neg, smul_zero]
      intro h0
      apply hd
      ext i
      fin_cases i
      · simp [h0]
      · simp [h1]
    · rw [zero_pow h1, mul_zero, map_zero, smul_zero]
end ReciprocityTheory.ChartRestriction.L1
