-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.sum_lev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:10.322796+00:00
-- url     : https://prove2.me/submissions/0e5d9cbd-e9ca-4fc4-a43e-2025846afc11

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levPos_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_levPos_inj

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] (F : Fin (2 * (1 + r') + k + 1) → M)
    (hF : ∀ q : Fin (2 * (1 + r') + k + 1), ¬(1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) → F q = 0) :
    ∑ q, F q = ∑ j : Fin (2 * r' + k + 1), F (levPos k 1 r' j) := by
  symm
  have e := Finset.sum_map Finset.univ ⟨levPos k 1 r', levPos_inj k r'⟩ F
  simp only [Function.Embedding.coeFn_mk] at e
  rw [← e]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  apply hF
  rintro ⟨h1, h2⟩
  apply hq
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  exact ⟨⟨q.val - 1, by omega⟩, by ext; simp only [levPos_val]; omega⟩
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
