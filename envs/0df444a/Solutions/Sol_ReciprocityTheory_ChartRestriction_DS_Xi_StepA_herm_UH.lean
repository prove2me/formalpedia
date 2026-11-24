-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.herm_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:56.05081+00:00
-- url     : https://prove2.me/submissions/0adea297-3ec1-4c6b-b524-7c02f09267a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_UHMulInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
