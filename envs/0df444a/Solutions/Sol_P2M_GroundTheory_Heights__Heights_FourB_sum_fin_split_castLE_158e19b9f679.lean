-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_sum_fin_split_castLE_158e19b9f679
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:26.351629+00:00
-- url     : https://prove2.me/submissions/af8cdb25-5227-4a0a-9080-cccce3261894

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution {M : Type*} [AddCommMonoid M] {i N : ℕ} (hi : i ≤ N)
    (f : Fin N → M) :
    ∑ c, f c = ∑ c : Fin i, f (Fin.castLE hi c) + ∑ c, if i ≤ c.val then f c else 0 := by
  have h1 : (Finset.univ.filter fun c : Fin N => c.val < i) =
      Finset.univ.map (Fin.castLEEmb hi) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨c.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨c', rfl⟩; exact c'.isLt
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : Fin N => c.val < i), h1,
    Finset.sum_map, Finset.sum_filter]
  simp only [Fin.castLEEmb_apply, not_lt]
end GroundTheory.Heights₂.Heights.FourB
