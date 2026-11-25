-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.sum_leviC_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:22.306446+00:00
-- url     : https://prove2.me/submissions/7e743e7d-5385-422c-abb0-40607c173632

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_leviC_add_snd
import Theorems.Thm_ReciprocityTheory_AnForm_A_leviC_smul_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {e : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a x : Fin e → ℂ) :
    ∑ j, leviC H a (Pi.single j 1) * x j = leviC H a (star x) := by
  have hx : star x = ∑ j, star (x j) • (Pi.single j 1 : Fin e → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single (star x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  let ℓ : (Fin e → ℂ) →+ ℂ := AddMonoidHom.mk' (fun b => leviC H a b) (leviC_add_snd H a)
  rw [hx]
  show _ = ℓ _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ℓ, AddMonoidHom.mk'_apply, leviC_smul_snd, star_star]
  ring
end ReciprocityTheory.AnForm.A
