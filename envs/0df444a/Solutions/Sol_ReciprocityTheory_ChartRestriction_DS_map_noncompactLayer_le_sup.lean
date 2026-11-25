-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.map_noncompactLayer_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:38.265124+00:00
-- url     : https://prove2.me/submissions/23aeb707-daa6-42fb-ba0b-2f66fd488c1d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_LayerBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wordContraction_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_rootWordProduct_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_apply_mem_noncompactLayer_succ
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_mem_noncompactPositionSubmodule_iff__607b2d11fea7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wordContraction_prepend
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_positionPrepend_mem_noncompactPositionSubmodule

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
theorem _root_.solution : ∀ (k : ℕ) (a b : Fin n), ε a ≠ ε b →
    (layer ε E V k).map (E a b) ≤ layer ε E V k ⊔ (ncV ε V (k + 1)).map (phi E (k + 1))
  | 0, a, b, hab => by
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    rw [Submodule.mem_comap]
    refine Submodule.mem_sup_right ?_
    let G : Big n 0 M := WithLp.toLp 2 (fun _ => v)
    have hG : G ∈ ncV ε V 0 := by
      rw [mem_noncompactPositionSubmodule_iff']; intro κ
      rw [if_pos (fun i => i.elim0)]; exact hv
    have hphi : phi E 0 G = v := by
      rw [wordContraction_apply]; simp [G, rootWordProduct_zero]
    refine ⟨indexPairPrepend (a, b) G, positionPrepend_mem_noncompactPositionSubmodule hab hG, ?_⟩
    rw [wordContraction_prepend, hphi]
  | k + 1, a, b, hab => by
    rw [Submodule.map_le_iff_le_comap]
    simp only [layer]
    refine sup_le ?_ (iSup_le fun c => iSup_le fun d => iSup_le fun hcd => ?_)
    · intro w hw
      exact Submodule.mem_sup_left (apply_mem_noncompactLayer_succ hab hw)
    · rw [Submodule.map_le_iff_le_comap]
      intro w hw
      simp only [Submodule.mem_comap]
      have h1 := solution k c d hcd (Submodule.mem_map_of_mem hw)
      obtain ⟨u, hu, y, ⟨G, hG, rfl⟩, hsum⟩ := Submodule.mem_sup.1 h1
      rw [← hsum, map_add]
      refine add_mem (Submodule.mem_sup_left (apply_mem_noncompactLayer_succ hab hu))
        (Submodule.mem_sup_right ⟨indexPairPrepend (a, b) G, positionPrepend_mem_noncompactPositionSubmodule hab hG, ?_⟩)
      rw [wordContraction_prepend]
end ReciprocityTheory.ChartRestriction.DS
