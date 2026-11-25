-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GSB.linA_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:06.770859+00:00
-- url     : https://prove2.me/submissions/dc3febd4-67a1-4ecc-8f90-852fa02fc388

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GSB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB
theorem _root_.solution {k r : ℕ} (A : Mat k r) (x : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    linA A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.GSB
