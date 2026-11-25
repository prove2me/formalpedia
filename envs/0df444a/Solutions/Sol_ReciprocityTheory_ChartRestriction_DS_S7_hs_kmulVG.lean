-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hs_kmulVG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:32.305828+00:00
-- url     : https://prove2.me/submissions/8bafd485-832b-44a0-b18c-bccd3296138c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_eq_traceVG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} (k : KG ε) (A : Matrix (Fin n) (Fin n) ℂ) : hs (toMK k * A) = hs A := by
  have hk : (toMK k)ᴴ * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.mp (k.2 : toMK k ∈ Kset ε).1
  rw [← hs_eq_traceVG, ← hs_eq_traceVG, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (toMK k)ᴴ, hk, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS.S7
