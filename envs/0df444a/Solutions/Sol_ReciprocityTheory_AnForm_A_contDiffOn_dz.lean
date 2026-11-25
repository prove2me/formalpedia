-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.contDiffOn_dz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:13.882799+00:00
-- url     : https://prove2.me/submissions/dc0c27d0-6dca-4d56-99f3-4fa7fa06f509

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsIbp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} {f : (Fin D → ℂ) → ℂ} {U : Set (Fin D → ℂ)} {n m : WithTop ℕ∞}
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (hmn : m + 1 ≤ n) (j : Fin D) :
    ContDiffOn ℝ m (dz j f) U := by
  have hd : ContDiffOn ℝ m (fun y => fderiv ℝ f y) U := hf.fderiv_of_isOpen hU hmn
  have h1 : ContDiffOn ℝ m (fun y => fderiv ℝ f y (Pi.single j 1)) U :=
    hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ m (fun y => fderiv ℝ f y (Complex.I • Pi.single j 1)) U :=
    hd.clm_apply contDiffOn_const
  exact (h1.sub ((contDiffOn_const (c := Complex.I)).mul h2)).div_const 2
end ReciprocityTheory.AnForm.A
