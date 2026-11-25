-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DegAdd.indep_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:30.322137+00:00
-- url     : https://prove2.me/submissions/ebac5093-0119-4a0e-84cb-b367adfb3ef1

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_Lemmata_GeneralBFactBisAlt_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_fin_append_comp_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DegAdd
open NumberField
namespace ReciprocityTheory.MultiplicativeHeights.DegAdd
theorem _root_.solution {K : Type} [Field K] {r k m : ℕ}
    {b : Fin k → Fin r → K} {c : Fin m → Fin r → K} (h : LinearIndependent K (Fin.append b c)) :
    LinearIndependent K b ∧ LinearIndependent K c ∧
      Disjoint (Submodule.span K (Set.range b)) (Submodule.span K (Set.range c)) := by
  have h2 := h.comp finSumFinEquiv finSumFinEquiv.injective
  rw [fin_append_comp_equiv] at h2
  have h3 := linearIndependent_sum.mp h2
  simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr] using h3
end ReciprocityTheory.MultiplicativeHeights.DegAdd
