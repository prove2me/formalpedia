-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.polar_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:25.368399+00:00
-- url     : https://prove2.me/submissions/afc45bbd-2418-48bd-bb4e-2f888c65dc3b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_L_inP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_k_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_eq_mul_exp_neg_polar_L_mul_exp_polar_L

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ k ∈ Kset ε, ∃ Y, inP ε Y ∧ g = k * NormedSpace.exp Y :=
  ⟨_, polar_k_mem hg, polar_L g, polar_L_inP hg, eq_mul_exp_neg_polar_L_mul_exp_polar_L⟩
end ReciprocityTheory.ChartRestriction.DS
