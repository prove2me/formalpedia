-- Prove2me | solution 1 for PositivityTheory.KReal.CasGl.adC_sw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:16:28.300384+00:00
-- url     : https://prove2.me/submissions/21e2183b-964f-48fd-9ef5-61db92fdfd03

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCas
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasGl
import Theorems.Thm_PositivityTheory_KReal_CasGl_Eab_mul_apply
import Theorems.Thm_PositivityTheory_KReal_CasGl_Eab_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.CasGl
variable {r s : ℕ}
namespace PositivityTheory.KReal.CasGl
theorem _root_.solution (k : KI r s) : adC (swK k) = (adC k)ᴴ := by
  ext j i
  obtain ⟨⟨a, b⟩, hk⟩ := k
  obtain ⟨⟨c, d⟩, hi⟩ := i
  obtain ⟨⟨e, f⟩, hj⟩ := j
  simp only [adC, swK, Matrix.conjTranspose_apply, Matrix.sub_apply, Eab_mul_apply, Eab_apply]
  clear hk hi hj
  simp only [star_sub, apply_ite star, star_one, star_zero]
  split_ifs <;> subst_vars <;> simp_all
  all_goals
    obtain ⟨h1, h2⟩ := ‹_ ∧ _›
    subst h1
    simp_all
end PositivityTheory.KReal.CasGl
