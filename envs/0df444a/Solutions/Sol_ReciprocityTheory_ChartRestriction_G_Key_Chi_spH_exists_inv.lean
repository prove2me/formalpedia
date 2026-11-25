-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Key.Chi.spH_exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:27:25.595112+00:00
-- url     : https://prove2.me/submissions/573ee2b5-b8be-4438-9c90-227f19692f88

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SpGenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenBase
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_J_mem_spH
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spTransl_neg_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spDiag_inv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_J_pow_four

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.solution {x : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ} (hx : x ∈ spH g) :
    ∃ y ∈ spH g, y * x = 1 := by

  induction hx using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with (⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | hJ
    · have hS' : (-S).IsSymm := by
        unfold Matrix.IsSymm at hS ⊢
        rw [Matrix.transpose_neg, hS]
      exact ⟨spTransl (-S), spTransl_mem hS', spTransl_neg_mul S⟩
    · exact ⟨spDiag U⁻¹, spDiag_mem _, spDiag_inv_mul U⟩
    · rw [Set.mem_singleton_iff] at hJ
      subst hJ
      exact ⟨J (Fin g) ℤ * J (Fin g) ℤ * J (Fin g) ℤ, mul_mem (mul_mem J_mem_spH J_mem_spH) J_mem_spH, J_pow_four⟩
  | one => exact ⟨1, one_mem _, one_mul 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'm, hx'⟩ := hx
    obtain ⟨y', hy'm, hy'⟩ := hy
    refine ⟨y' * x', mul_mem hy'm hx'm, ?_⟩
    rw [mul_assoc, ← mul_assoc x' x y, hx', one_mul, hy']
end ReciprocityTheory.ChartRestriction.G.Key.Chi
