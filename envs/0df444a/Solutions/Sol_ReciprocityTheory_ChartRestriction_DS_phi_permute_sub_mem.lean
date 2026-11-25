-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.phi_permute_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:43:57.064589+00:00
-- url     : https://prove2.me/submissions/69cd3fda-88aa-4ed0-81da-58ecb99d88ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mem_ncV_iff_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_permute_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_phi_apply_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_listProd_perm_sub_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_word_eq_listProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hV : IsKStableSub ε E V) {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1))) {F : Big n (k + 1) M} (hF : F ∈ ncV ε V (k + 1)) :
    phi E (k + 1) F - phi E (k + 1) (permute σ F) ∈ layer ε E V k := by
  rw [phi_apply_eq, phi_apply_eq]
  have hre : ∑ κ, word E κ ((permute σ F) κ) = ∑ κ, word E (κ ∘ σ.symm) (F κ) := by
    let e : (Fin (k + 1) → Fin n × Fin n) ≃ (Fin (k + 1) → Fin n × Fin n) :=
      ⟨fun κ => κ ∘ σ, fun κ => κ ∘ σ.symm, fun κ => by funext i; simp, fun κ => by funext i; simp⟩
    refine Fintype.sum_equiv e _ _ (fun κ => ?_)
    show word E κ (permute σ F κ) = word E ((κ ∘ σ) ∘ σ.symm) (F (κ ∘ σ))
    have hκ : (κ ∘ σ) ∘ σ.symm = κ := by funext i; simp
    rw [hκ, permute_apply]
  rw [hre, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ (fun κ _ => ?_)
  have hFκ := (mem_ncV_iff_apply.1 hF) κ
  by_cases hc : ∀ i, ε (κ i).1 ≠ ε (κ i).2
  · rw [if_pos hc] at hFκ
    rw [word_eq_listProd, word_eq_listProd]
    have hp : (List.ofFn κ).Perm (List.ofFn (κ ∘ σ.symm)) := (Equiv.Perm.ofFn_comp_perm σ.symm κ).symm
    have hnc : ∀ p ∈ List.ofFn κ, ε p.1 ≠ ε p.2 := fun p hp' => by
      rw [List.mem_ofFn] at hp'
      obtain ⟨i, rfl⟩ := hp'
      exact hc i
    have := listProd_perm_sub_mem hE hV hp hnc (show F κ ∈ layer ε E V 0 from hFκ) k (by simp)
    rw [zero_add] at this
    exact this
  · rw [if_neg hc] at hFκ
    rw [(Submodule.mem_bot ℂ).1 hFκ]
    simp
end ReciprocityTheory.ChartRestriction.DS
