-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_mat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:49.572848+00:00
-- url     : https://prove2.me/submissions/24c4c60d-1c29-4e51-9f1c-3a9438e3a50b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_mat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x x' : Frame X.Ψ r} {τ : X.Ψ} (h : mat x τ = mat x' τ) (v w : Fin r → ℂ) :
    X.Hf x τ v w = X.Hf x' τ v w := by
  simp only [Data.Hf, ppos_mat_eq X h]
end ReciprocityTheory.ChartRestriction.G.FD.Data
