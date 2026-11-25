-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.PT.column_mem_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:19:43.117576+00:00
-- url     : https://prove2.me/submissions/7a5b07e9-01a4-4477-855f-fa248033d33c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SupRatioLeOfPhaseZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_HC_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex NumberField
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.PT
variable (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2.PT
theorem _root_.solution {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) : X.col1 s ∈ X.toGT.Sec 1 := by
  obtain ⟨hd, hf⟩ := hs
  refine (show Differentiable ℂ (X.col1 s) ∧ ∀ γ ∈ lat X.toGT.b, ∀ v, X.col1 s (v + γ) =
      X.toGT.ka γ * cexp (((1 : ℕ) : ℂ) * Real.pi * Hf v γ + ((1 : ℕ) : ℂ) * Real.pi * Hf γ γ / 2) *
        X.col1 s v from ⟨?_, ?_⟩)
  · exact hd.comp (differentiable_pi.mpr fun _ => differentiable_id)
  · intro γ hγ v
    have h := hf (fun _ => γ) (fun _ => hγ) (fun _ => v)
    simp only [HC_one, Fin.prod_univ_one, pow_one] at h
    exact h
end ReciprocityTheory.ChartRestriction.G.I2.PT
