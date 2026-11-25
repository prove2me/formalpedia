-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:55.893265+00:00
-- url     : https://prove2.me/submissions/48f5b7dd-1430-40cc-8373-6a4aa8b0f1ae

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_anti_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_anti_zero
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_evB
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.QuantumDeterminantProducts
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (g : TV n M (Fin n)) (hg : IsAnti g) :
    ev E u (List.finRange n) id g = qdet E u (g id) := by
  rw [evB E u g _ (List.nodup_finRange n) id]
  have hfilt : Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ List.finRange n → c p = id p) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro c _ p hp
    exact absurd (List.mem_finRange p) hp
  rw [hfilt]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨fun σ : Equiv.Perm (Fin n) => ⇑σ, DFunLike.coe_injective⟩)), Finset.sum_map]
  · simp only [qdet, qminor, LinearMap.sum_apply, Function.Embedding.coeFn_mk]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have ha := anti_apply hg σ id
    simp only [Function.id_comp] at ha
    rw [ha, map_smul, Module.End.mul_apply, Module.End.intCast_apply, List.ofFn_eq_map, sg, Int.cast_smul_eq_zsmul]
    rfl
  · intro c _ hc
    have hnc : ¬ Function.Injective c := by
      intro hinj
      apply hc
      rw [Finset.mem_map]
      exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
    rw [anti_zero hg hnc, map_zero]
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
