-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux.star_hpk_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:33:23.09415+00:00
-- url     : https://prove2.me/submissions/b952351f-9802-42c7-8821-442793177a93

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermMatrixMulVecFirst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_sg_sg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_FormulaFAux_hpk_mulVec

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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
theorem _root_.solution (k r : ℕ) (u w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ w) = star u ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply, hpk_mulVec]
  calc ∑ i, star ((if i.val = r + k then -1 else 1 : ℂ) * u (sg k r i)) * ((if i.val = r + k then -1 else 1) * w (sg k r i))
      = ∑ i, star (u (sg k r i)) * w (sg k r i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
    _ = ∑ i, star (u i) * w i :=
        Fintype.sum_equiv (Function.Involutive.toPerm _ (sg_sg k r)) _ _ (fun i => rfl)
end ReciprocityTheory.ChartRestriction.DS.Xi.FormulaFAux
