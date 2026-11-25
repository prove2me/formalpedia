-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.crossOp_mem_ncV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:34.147918+00:00
-- url     : https://prove2.me/submissions/2c13f1e5-73e2-45de-b4b6-24b9716addcf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_bcas_sum_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_apply


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
theorem _root_.solution (hV : IsKStableSub ε E V) (k : ℕ) (i : Fin k) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : crossOp ε E k i F ∈ ncV ε V k := by
  classical
  have hmem : ∀ G : Big n k M, G ∈ ncV ε V k ↔
      ∀ κ, G κ ∈ (if ∀ j, ε (κ j).1 ≠ ε (κ j).2 then V else ⊥) := by
    intro G
    unfold ncV
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact Iff.rfl
  rw [hmem] at hF ⊢
  intro κ
  have hc : ∀ p : Fin n × Fin n, ε p.1 = ε (κ i).1 → ε p.2 = ε (κ i).2 →
      ((∀ j, ε ((Function.update κ i p) j).1 ≠ ε ((Function.update κ i p) j).2) ↔
        ∀ j, ε (κ j).1 ≠ ε (κ j).2) := by
    intro p h1 h2
    refine forall_congr' fun j => ?_
    by_cases hj : j = i
    · subst hj
      simp [Function.update_apply, h1, h2]
    · simp [Function.update_apply, hj]
  have hval : (crossOp ε E k i F) κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) -
        (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0)) := by
    unfold crossOp
    simp only [LinearMap.sum_apply, bcas_sum_apply, Module.End.mul_apply, factorAd_apply,
      mAct_apply]
  rw [hval]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  have hT : ∀ v ∈ (if (∀ j, ε (κ j).1 ≠ ε (κ j).2) then V else (⊥ : Submodule ℂ M)),
      E b a v ∈ (if (∀ j, ε (κ j).1 ≠ ε (κ j).2) then V else (⊥ : Submodule ℂ M)) := by
    intro v hv
    split_ifs at hv ⊢ with hcκ
    · exact hV b a hab v hv
    · rw [Submodule.mem_bot] at hv ⊢
      rw [hv, map_zero]
  refine Submodule.sub_mem _ ?_ ?_
  · by_cases h1 : (κ i).1 = a
    · rw [if_pos h1]
      refine hT _ ?_
      have hFκ := hF (Function.update κ i (b, (κ i).2))
      rwa [if_congr (hc (b, (κ i).2) (by show ε b = ε (κ i).1; rw [hab, h1]) rfl) rfl rfl]
        at hFκ
    · rw [if_neg h1]
      exact Submodule.zero_mem _
  · by_cases h2 : (κ i).2 = b
    · rw [if_pos h2]
      refine hT _ ?_
      have hFκ := hF (Function.update κ i ((κ i).1, a))
      rwa [if_congr (hc ((κ i).1, a) rfl (by show ε a = ε (κ i).2; rw [h2, hab])) rfl rfl]
        at hFκ
    · rw [if_neg h2]
      exact Submodule.zero_mem _
end ReciprocityTheory.ChartRestriction.DS
