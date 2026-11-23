-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.cf_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:07.84906+00:00
-- url     : https://prove2.me/submissions/d2dc3b7d-564d-43be-b9c9-3ae93d1ce044

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm.P
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution {α β γ δ : Type*} (k : ℕ) (P : Matrix α β ℂ[X]) (f : γ → α) (g : δ → β) :
    cf k (P.submatrix f g) = (cf k P).submatrix f g := rfl
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
