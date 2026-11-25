-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.DH_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:23.651258+00:00
-- url     : https://prove2.me/submissions/f8b84eaa-145f-4781-87dc-c22912cb1ae7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℂ} {p}
    (hg : DifferentiableAt ℂ g p) : DH X g p = Lhol X (fun y => g (y, p.2)) p.1 := by
  have hs : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => ((y, p.2) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
      ((ContinuousLinearMap.id ℂ _).prod 0) p.1 := (hasFDerivAt_id _).prodMk (hasFDerivAt_const _ _)
  have h1 := hg.hasFDerivAt.comp p.1 hs
  have h2 : fderiv ℂ (fun y => g (y, p.2)) p.1 = (fderiv ℂ g p).comp ((ContinuousLinearMap.id ℂ _).prod 0) := h1.fderiv
  unfold DH Lhol
  rw [h2]
  rfl
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
