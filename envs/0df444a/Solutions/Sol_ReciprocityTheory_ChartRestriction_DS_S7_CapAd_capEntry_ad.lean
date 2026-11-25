-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapAd.capEntry_ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:53.206403+00:00
-- url     : https://prove2.me/submissions/04453f14-3209-4b6c-97da-89d216c435e0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.CapAd
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapAd
theorem _root_.solution (E : Fin n → Fin n → 𝒰) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (x : ℂ)
    (a b : Fin n) :
    capEntry (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) x a b =
      ∑ c, ∑ d, (P c a * Q b d) • capEntry E x c d := by
  simp only [capEntry, smul_add, Finset.sum_add_distrib]
  congr 1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_smul]
  have h : ∑ c, P c a * Q b c = (Q * P) b a := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)
  rw [h, hQP, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab, zero_smul]
end ReciprocityTheory.ChartRestriction.DS.S7.CapAd
