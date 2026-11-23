-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:38.865815+00:00
-- url     : https://prove2.me/submissions/d95a5a3c-3d26-4523-94df-c4d684323658

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Branch

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.TR ReciprocityTheory.ChartRestriction.TR.Weyl
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
theorem _root_.solution {K : Type*} [Field K] : ∀ (n : ℕ) (t : Fin n → K), gtChar n 0 t = 1
  | 0, _ => rfl
  | n + 1, t => by
    rw [gtChar]
    have h : interl (0 : Fin (n + 1) → ℤ) = {0} := by
      ext mu
      simp only [interl, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · intro h; funext i; have := h i; simp only [Pi.zero_apply]; omega
      · rintro rfl i; simp
    rw [h, sum_singleton, solution n]
    simp [wsum]
end ReciprocityTheory.ChartRestriction.TR.Weyl
