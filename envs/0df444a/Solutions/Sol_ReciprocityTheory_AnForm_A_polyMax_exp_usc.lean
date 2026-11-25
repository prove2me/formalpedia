-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.polyMax_exp_usc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:29.686972+00:00
-- url     : https://prove2.me/submissions/2e76a342-d187-4c19-85c2-4a2210c23be2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Theorems.Thm_ReciprocityTheory_AnForm_A_polyMax_usc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (hU : IsOpen U) (hφ : UpperSemicontinuousOn φ U) {R : ℝ} (hR0 : 0 < R)
    (hR : closedBall z R ⊆ U) :
    UpperSemicontinuousOn (fun s => polyMax φ z (Real.exp s)) (Iic (Real.log R)) := by
  intro s hs y hy
  have hexp : Real.exp s ≤ R := (Real.exp_le_exp.2 hs).trans_eq (Real.exp_log hR0)
  have hsR : closedBall z (Real.exp s) ⊆ U := (closedBall_subset_closedBall hexp).trans hR
  obtain ⟨δ, hδ, -, hδ'⟩ := polyMax_usc hU hφ (Real.exp_pos s).le hsR (sub_pos.2 hy)
  have hev : ∀ᶠ s' in 𝓝 s, Real.exp s' < Real.exp s + δ :=
    (Real.continuous_exp.tendsto s) (Iio_mem_nhds (by linarith))
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [hev] with s' hs'
  have := hδ' _ (Real.exp_pos s').le hs'.le
  linarith
end ReciprocityTheory.AnForm.A
