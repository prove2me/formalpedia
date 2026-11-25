-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_regMax_comp_equiv_0d69f3f85194
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:22:40.219795+00:00
-- url     : https://prove2.me/submissions/00c7e1ad-4ff2-435c-bcca-ee642fca9cfd

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_tmax_comp_equiv_31ff04f21355

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory
open ReciprocityTheory.AnForm.A (regMax tmax kθ)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {κ ι : Type} [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    (e : κ ≃ ι) (η : ℝ) (t : ι → ℝ) : regMax η (t ∘ e) = regMax η t := by
  unfold regMax
  rw [← (volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) e).integral_comp']
  congr 1
  funext g
  have hg : ∀ k, (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) g (e k) = g k := fun k => by
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  set h := (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) g
  have h1 : tmax (fun j => t j + η * h j) = tmax (fun k => (t ∘ e) k + η * g k) := by
    rw [← tmax_comp_equiv e (fun j => t j + η * h j)]
    congr 1
    funext k
    simp [hg]
  have h2 : ∏ j, kθ (h j) = ∏ k, kθ (g k) := by
    rw [← e.prod_comp]
    simp [hg]
  rw [h1, h2]
end GroundTheory.Heights₂.Heights.Regular
