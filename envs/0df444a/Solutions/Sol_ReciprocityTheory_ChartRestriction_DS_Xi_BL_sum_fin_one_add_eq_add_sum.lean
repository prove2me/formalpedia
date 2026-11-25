-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.sum_fin_one_add_eq_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:35.649083+00:00
-- url     : https://prove2.me/submissions/32ae48ad-e615-4b33-90ea-5bbbdbc01fda

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector

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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution {M : Type} [AddCommMonoid M] (F : Fin (1 + r') → M) :
    ∑ a, F a = F ⟨0, by omega⟩ + ∑ a' : Fin r', F ⟨a'.val + 1, by omega⟩ := by
  rw [← Fintype.sum_equiv (finCongr (Nat.add_comm r' 1))
    (fun a : Fin (r' + 1) => F (finCongr (Nat.add_comm r' 1) a)) F (fun _ => rfl), Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg F (Fin.ext (by simp))
  · exact Finset.sum_congr rfl fun a _ => congrArg F (Fin.ext (by simp))
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
