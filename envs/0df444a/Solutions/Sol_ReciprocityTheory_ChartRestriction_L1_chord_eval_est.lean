-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.chord_eval_est
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:42.636006+00:00
-- url     : https://prove2.me/submissions/bdf45e02-a8e6-4dfb-8063-ad322e71d244

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorChord
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_X0
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_X1
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_sub
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_integral_X
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution [CompleteSpace C] {F : MvPowerSeries (Fin 2) C} (hF : Formalism.G.IntegralMv F)
    (h00 : MvPowerSeries.constantCoeff F = 0)
    (h10 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1)
    (h01 : MvPowerSeries.coeff (Finsupp.single 1 1) F = 1) {a b : C} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖evalMv2 F a b - a - b‖ ≤ (max ‖a‖ ‖b‖) ^ 2 := by
  set r := max ‖a‖ ‖b‖ with hr
  have hr0 : 0 ≤ r := le_trans (norm_nonneg a) (le_max_left _ _)
  have hr1 : r < 1 := max_lt ha hb
  set G : MvPowerSeries (Fin 2) C := F - MvPowerSeries.X 0 - MvPowerSeries.X 1 with hG
  have hI1 : Formalism.G.IntegralMv (F - MvPowerSeries.X 0) :=
    (FormalGroupPointsHom.IL C).sub_mem hF (FormalGroupPointsHom.integral_X 0)
  have hIG : Formalism.G.IntegralMv G := (FormalGroupPointsHom.IL C).sub_mem hI1 (FormalGroupPointsHom.integral_X 1)
  have hev : evalMv2 G a b = evalMv2 F a b - a - b := by
    rw [hG, FormalGroupPointsHom.evalMv2_sub hI1 (FormalGroupPointsHom.integral_X 1) ha hb,
      FormalGroupPointsHom.evalMv2_sub hF (FormalGroupPointsHom.integral_X 0) ha hb, FormalGroupPointsHom.evalMv2_X0,
      FormalGroupPointsHom.evalMv2_X1]
  rw [← hev, FormalGroupPointsHom.evalMv2_eq]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (pow_nonneg hr0 2)
  intro d
  by_cases hd : 2 ≤ d.degree
  · exact (FormalGroupPointsHom.norm_term_le hIG (le_max_left _ _) (le_max_right _ _) d).trans
      (pow_le_pow_of_le_one hr0 hr1.le hd)
  · have hz : MvPowerSeries.coeff d G = 0 := by
      rw [FormalGroupPointsHom.degree_fin_two_eq_add_of_ne] at hd
      have hcases : d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
        have h3 : (d 0 = 0 ∧ d 1 = 0) ∨ (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
        rcases h3 with ⟨u, v⟩ | ⟨u, v⟩ | ⟨u, v⟩
        · left; ext i; fin_cases i <;> simp [u, v]
        · right; left; ext i; fin_cases i <;> simp [u, v]
        · right; right; ext i; fin_cases i <;> simp [u, v]
      have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
        intro he
        have := DFunLike.congr_fun he 0
        simp at this
      rcases hcases with rfl | rfl | rfl
      · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hG]
        simp [h00]
      · rw [hG, map_sub, map_sub, h10, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
          if_neg hne]
        ring
      · rw [hG, map_sub, map_sub, h01, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
          if_neg hne.symm]
        ring
    rw [FormalGroupPointsHom.term, hz, zero_mul, norm_zero]
    exact pow_nonneg hr0 2
end ReciprocityTheory.ChartRestriction.L1
