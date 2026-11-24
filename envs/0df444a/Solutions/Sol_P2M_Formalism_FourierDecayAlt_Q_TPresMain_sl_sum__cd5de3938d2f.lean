-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_Q_TPresMain_sl_sum__cd5de3938d2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:26.700692+00:00
-- url     : https://prove2.me/submissions/b61edc72-a38a-42c7-bc2b-13fd39575c4a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_ExpSecondHermitianMemLevel
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TPresMain_sl_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresMain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.Q.TPresMain
theorem _root_.solution {ι : Type*} [Fintype ι] (f : ι → Mx k r → E) (hf : ∀ j, SmoothLev k r i D (f j)) :
    SmoothLev k r i D (fun x => ∑ j, f j x) := by
  have e : (fun x => ∑ j, f j x) = ∑ j, f j := by
    funext x
    exact (Finset.sum_apply x Finset.univ f).symm
  rw [e]
  exact sl_sum _ _ fun j _ => hf j
end Formalism.FourierDecayAlt.Q.TPresMain
