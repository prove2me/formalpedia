-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.TR.Weyl.antitone_of_mem_interl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:16.995612+00:00
-- url     : https://prove2.me/submissions/28f1a675-230e-401d-9f7c-64dd4197b652

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AltBranchStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl

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
theorem _root_.solution {n : ℕ} {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) {mu : Fin n → ℤ}
    (hmu : mu ∈ interl lam) : Antitone mu := by
  have h := Fintype.mem_piFinset.mp hmu
  intro i j hij
  rcases eq_or_lt_of_le hij with hij | hij
  · rw [hij]
  · have hi := Finset.mem_Icc.mp (h i)
    have hj := Finset.mem_Icc.mp (h j)
    have h3 : lam j.castSucc ≤ lam i.succ :=
      hlam (Fin.le_def.mpr (by simp only [Fin.val_succ, Fin.val_castSucc]; exact Fin.lt_def.mp hij))
    omega
end ReciprocityTheory.ChartRestriction.TR.Weyl
