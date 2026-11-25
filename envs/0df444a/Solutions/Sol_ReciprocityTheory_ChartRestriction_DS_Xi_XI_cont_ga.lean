-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.XI.cont_ga
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:18.821254+00:00
-- url     : https://prove2.me/submissions/754fd2e5-db95-46f8-b1c2-a19e66329739

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaNonneg

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.XI
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS ReciprocityTheory.ChartRestriction.DS.Xi.GSB
namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI
theorem _root_.solution {k r : ℕ} (l : Fin (r + 1)) :
    Continuous fun x : Mt k r => Ga k r l (fun a => Matrix.of x *ᵥ phiV k r a) := by
  unfold Ga
  refine Complex.continuous_re.comp ?_
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.of_apply]
  have hx : Continuous fun x : Mt k r => Matrix.of x := continuous_id
  first
    | exact ((hx.matrix_mulVec continuous_const).star).dotProduct (hx.matrix_mulVec continuous_const)
    | (simp only [dotProduct]; exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (hx.matrix_mulVec continuous_const).star).mul ((continuous_apply i).comp (hx.matrix_mulVec continuous_const)))
    | (simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]; fun_prop)
end ReciprocityTheory.ChartRestriction.DS.Xi.XI
