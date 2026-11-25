-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.hpk_invol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:26:31.141399+00:00
-- url     : https://prove2.me/submissions/55cee908-c2c7-48b1-a528-26957c3d9e59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_sgn_sig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_sgn_mul_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_hpk_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i; rw [hpk_mulVec, hpk_mulVec, sig_sig, sgn_sig, ← mul_assoc, sgn_mul_self, one_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
