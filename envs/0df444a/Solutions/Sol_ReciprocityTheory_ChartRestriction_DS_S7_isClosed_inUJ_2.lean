-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.DS.S7.isClosed_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:07:59.157551+00:00
-- url     : https://prove2.me/submissions/41fc11fa-a729-4913-a8d2-d7887c4c488e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.isClosed_inUJ (ε : Fin n → Bool) : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const


end

theorem solution {n : ℕ} (ε : Fin n → Bool) : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | ReciprocityTheory.ChartRestriction.DS.inUJ ε g} :=
  ReciprocityTheory.ChartRestriction.DS.S7.isClosed_inUJ ε
