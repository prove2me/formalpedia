-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QF.capelliC_negT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:03.053221+00:00
-- url     : https://prove2.me/submissions/51c49019-5b23-4a3f-b6a4-15c8830989da

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_QdetFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PQdetFacts

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
open PositivityTheory.Rg.Cz.QF
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace PositivityTheory.Rg.Cz.QF
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) :
    capelliC (fun a b => -E b a) x = (-1) ^ n * rminor E id id ((n : ℂ) - 1 - x) := by
  simp only [capelliC, cminor, rminor, id]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h : (List.ofFn fun j : Fin n => capEntry (fun a b => -E b a) (x - ((j : ℕ) : ℂ)) (σ j) j) =
      (List.ofFn fun j : Fin n => capEntry E ((n : ℂ) - 1 - x - (n : ℂ) + 1 + ((j : ℕ) : ℂ)) j (σ j)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext j
    simp only [Function.comp, capEntry]
    by_cases hj : σ j = j
    · rw [if_pos hj, if_pos hj.symm, neg_add, ← map_neg]
      congr 2
      ring
    · rw [if_neg hj, if_neg (Ne.symm hj), neg_add, neg_zero]
  rw [h, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc,
    ((Commute.neg_one_left _).pow_left n).eq]
end PositivityTheory.Rg.Cz.QF
