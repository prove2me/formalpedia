-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.gN_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:53.932537+00:00
-- url     : https://prove2.me/submissions/0d69cd36-5f4a-4165-abdd-1604e5dcdf44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_sum_lev_le


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
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
theorem _root_.solution (M : Mat k (1 + r')) (g : Mat k r')
    (h : ∀ i j, M (levPos k 1 r' i) (levPos k 1 r' j) = g i j) : gN g ≤ gN M := by
  unfold gN
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (g i j)
      = ∑ i, ∑ j, Complex.normSq (M (levPos k 1 r' i) (levPos k 1 r' j)) := by simp only [h]
    _ ≤ ∑ i, ∑ q, Complex.normSq (M (levPos k 1 r' i) q) :=
        Finset.sum_le_sum fun i _ => sum_lev_le k r' (fun q => Complex.normSq (M (levPos k 1 r' i) q))
          fun q => Complex.normSq_nonneg _
    _ ≤ ∑ p, ∑ q, Complex.normSq (M p q) :=
        sum_lev_le k r' (fun p => ∑ q, Complex.normSq (M p q))
          fun p => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
