-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.linInd_toLp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:01:25.131954+00:00
-- url     : https://prove2.me/submissions/66281821-3b63-4a51-8ee4-49b5c6767b08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution {ι : Type*} (Y : ι → Fin n → ℂ) (hY : LinearIndependent ℂ Y) :
    LinearIndependent ℂ (fun a => (WithLp.toLp 2 (Y a) : EuclideanSpace ℂ (Fin n))) :=
  hY.map' (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap (LinearEquiv.ker _)
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
