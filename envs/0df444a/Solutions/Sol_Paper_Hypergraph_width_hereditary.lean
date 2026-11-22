-- Prove2me | solution 1 for Paper.Hypergraph.width_hereditary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:39.559379+00:00
-- url     : https://prove2.me/submissions/ad9ea9b7-f560-462d-8938-cbdbda1b1601

import Definitions.Def_Paper_TrustBoundary
import Definitions.Def_Paper_Formalized
import Theorems.Thm_Paper_Hypergraph_optimalWidth_le_bagWidth
import Theorems.Thm_Paper_Hypergraph_coverCost_mono
import Theorems.Thm_Paper_Hypergraph_cover_restriction
import Theorems.Thm_Paper_Hypergraph_optimal_modular_le_adw

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Paper
open Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution (H : Hypergraph) (W : Finset ℕ) :
    (H.induce W).adw ≤ H.adw ∧ (H.induce W).fhw ≤ H.fhw := by
  constructor
  · have hz : (H.induce W).ModularWeight (fun _ => 0) := ⟨by simp, by simp⟩
    refine csSup_le ⟨_, _, hz, rfl⟩ ?_
    rintro r ⟨w, hw, rfl⟩
    let w' : ℕ → ℝ := fun v => if v ∈ W then w v else 0
    have hsum : ∀ S : Finset ℕ, (∑ v ∈ S, w' v) = ∑ v ∈ S ∩ W, w v := by
      intro S
      simp only [w', ← sum_filter]
      congr 1
    have hw' : H.ModularWeight w' := by
      constructor
      · intro v; dsimp [w']; split_ifs <;> first | exact hw.1 v | exact le_rfl
      · intro e he
        rw [hsum]
        by_cases hn : (H.edge e ∩ W).Nonempty
        · exact hw.2 e (mem_filter.mpr ⟨he, hn⟩)
        · rw [Finset.not_nonempty_iff_eq_empty.mp hn, sum_empty]
          norm_num
    apply le_trans ?_ (H.optimal_modular_le_adw hw')
    refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
    rintro r ⟨n, D, rfl⟩
    calc
      (H.induce W).optimalWidth (modularValue w) ≤ (D.restrict W).bagWidth (modularValue w) :=
        (H.induce W).optimalWidth_le_bagWidth _
          (fun S _ => sum_nonneg (fun v _ => hw.1 v)) _
      _ = D.bagWidth (modularValue w') := by
        unfold TreeDecomposition.bagWidth
        apply congrArg sSup
        exact congrArg Set.range (funext fun t => (hsum (D.bag t)).symm)
  · refine le_csInf ⟨_, 0, H.oneBag, rfl⟩ ?_
    rintro r ⟨n, D, rfl⟩
    apply le_trans ((H.induce W).optimalWidth_le_bagWidth _
      (fun S _ => (H.induce W).coverCost_nonneg (indicator S)) (D.restrict W))
    refine csSup_le ⟨_, 0, rfl⟩ ?_
    rintro r ⟨t, rfl⟩
    have hcost : (H.induce W).setCoverCost (D.bag t ∩ W) ≤ H.setCoverCost (D.bag t) := by
      rw [H.cover_restriction inter_subset_right]
      apply H.coverCost_mono
      intro v hv
      dsimp [indicator]
      split_ifs <;> simp_all
    exact hcost.trans (le_csSup (Set.finite_range _).bddAbove ⟨t, rfl⟩)
end Paper.Hypergraph
