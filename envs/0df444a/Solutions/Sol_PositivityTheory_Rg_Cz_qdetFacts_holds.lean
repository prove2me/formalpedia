-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.qdetFacts_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:15:59.797327+00:00
-- url     : https://prove2.me/submissions/1c5c50e6-8ebf-4ea4-a6ba-ef7485e234fa

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_qdet_eq_capelliC
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_qdet_negT
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_evU_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_evU_qdetPoly
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_prod_linear
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_sum_fin_cast
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_natDegree_qdetPoly_le
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_coeff_qdetPoly_top
import Theorems.Thm_PositivityTheory_Rg_Cz_QF_coeff_eq_zero_of_evU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelliC_central


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open QF ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : QdetFacts := by
  intro n M _ _ E hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u a b
    rw [qdet_eq_capelliC]
    exact (capelliC_central E hE u a b).symm
  · refine ⟨fun i => (qdetPoly E).coeff i, fun u => ?_⟩
    rw [← evU_qdetPoly, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  · intro l hl
    have key : ∀ i, (qdetPoly E).coeff i =
        algebraMap ℂ (Module.End ℂ M) ((∏ k : Fin n, (X + C (l k))).coeff i) := by
      intro i
      rw [← coeff_map, ← sub_eq_zero, ← coeff_sub]
      refine coeff_eq_zero_of_evU _ (fun u => ?_) i
      rw [map_sub, evU_qdetPoly, hl u, evU_apply, eval₂_map, RingHom.id_comp, eval₂_at_apply, eval_prod]
      simp only [eval_add, eval_X, eval_C, sub_self]
    cases n with
    | zero => simp
    | succ m =>
      have h1 := key m
      have h2 := (prod_linear (m + 1) fun k => E k k - algebraMap ℂ (Module.End ℂ M) ((k : ℕ) : ℂ)).2.2 m rfl
      have h3 := (prod_linear (m + 1) l).2.2 m rfl
      rw [List.prod_ofFn] at h3
      rw [coeff_qdetPoly_top E m le_rfl, h2, h3, Finset.sum_sub_distrib, sub_eq_iff_eq_add, ← map_sum] at h1
      rw [h1, ← map_add, sum_fin_cast]
  · unfold GlRel
    intro a b c d
    have h := hE d c b a
    simp only [@eq_comm _ c b, @eq_comm _ a d] at h
    simp only [neg_mul_neg]
    rw [← neg_sub, h]
    split_ifs <;> abel
  · intro l hl u
    rw [qdet_negT E hE, hl]
    have hp : ∏ k : Fin n, (u + (-((n : ℂ) - 1) - l k)) = (-1) ^ n * ∏ k : Fin n, ((n : ℂ) - 1 - u + l k) := by
      rw [show (-1 : ℂ) ^ n = ∏ _k : Fin n, (-1 : ℂ) by simp, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by ring
    rw [hp, map_mul, map_pow, map_neg, map_one]
end PositivityTheory.Rg.Cz
