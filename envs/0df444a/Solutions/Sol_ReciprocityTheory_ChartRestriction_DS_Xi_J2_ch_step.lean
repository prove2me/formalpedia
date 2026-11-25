-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.ch_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:53.930159+00:00
-- url     : https://prove2.me/submissions/8147c8ec-063e-4865-b0b4-7b6cad915502

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_chF_meas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_tailF_meas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_ch_pt
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_J2_split_cons__05b34922c7ac


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution (p m : ℕ) (ν : Fin (p + 2) → ℝ) :
    CHInt (p + 1) m ν = kc (2 + ν 0) * TailInt p m (ν 0) (Fin.tail ν) := by
  have hF := chF_meas (p + 1) m ν
  have hT := tailF_meas p m (ν 0) (Fin.tail ν)
  have step : ∀ a : Fin (p + 1) → ℂ,
      ∫⁻ z : (Fin (p + 1) → ℂ) × ((Fin m → ℂ) × ℝ), chF (p + 1) m ν (a, z) =
        ∫⁻ q : (Fin p → ℂ) × ((Fin m → ℂ) × ℝ), kc (2 + ν 0) * tailF p m (ν 0) (Fin.tail ν) (a, q) := by
    intro a
    rw [split_cons' (fun z => chF (p + 1) m ν (a, z)) (hF.comp measurable_prodMk_left)]
    exact lintegral_congr fun q => ch_pt p m ν (a, q)
  show ∫⁻ x : Xp (p + 1) m, chF (p + 1) m ν x =
    kc (2 + ν 0) * ∫⁻ y : TDom p m, tailF p m (ν 0) (Fin.tail ν) y
  rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable,
    lintegral_congr fun a => (step a).trans (lintegral_const_mul _ (hT.comp measurable_prodMk_left)),
    lintegral_const_mul _ hT.lintegral_prod_right']
  congr 1
  rw [Measure.volume_eq_prod (Fin (p + 1) → ℂ), lintegral_prod _ hT.aemeasurable]
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
