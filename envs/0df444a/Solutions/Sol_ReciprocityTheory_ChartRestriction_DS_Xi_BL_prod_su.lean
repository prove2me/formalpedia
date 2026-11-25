-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.prod_su
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:40.66701+00:00
-- url     : https://prove2.me/submissions/b9d618d1-c545-44fd-9d53-54028217581f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange

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
theorem _root_.solution {M : Type} [CommMonoid M] (f : Fin (1 + r' + 1) → M) :
    ∏ l, f l = f 0 * ∏ a : Fin (r' + 1), f (su a) := by
  rw [Fin.prod_univ_succ]
  congr 1
  exact (Fintype.prod_equiv (finCongr (by omega : r' + 1 = 1 + r')) (fun a => f (su a))
    (fun b => f b.succ) fun a => congrArg f (Fin.ext (by simp [su]))).symm
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
