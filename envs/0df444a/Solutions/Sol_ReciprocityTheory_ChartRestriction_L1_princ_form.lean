-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.princ_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:58.009713+00:00
-- url     : https://prove2.me/submissions/e4f0358b-a75b-4d91-a7c2-a649a8467379

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModPrincNorm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_absNorm_span
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_quadInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {d : ℕ} (hsf : Squarefree d) (hd : d % 4 = 3) (v : HeightOneSpectrum (𝓞 (KQ d)))
    (hv : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1) :
    ∃ a b : ℤ, 4 * (Nat.card (𝓞 (KQ d) ⧸ v.asIdeal) : ℤ) = 4 * a ^ 2 + 4 * a * b + b ^ 2 * (1 + d) := by
  rw [ClassGroup.mk0_eq_one_iff] at hv
  obtain ⟨x, hx⟩ := hv.principal
  obtain ⟨a, b, hab⟩ := quadInt hsf hd x
  refine ⟨a, b, ?_⟩
  rw [← absNorm_span hsf hd x a b hab, Ideal.absNorm_apply, Submodule.cardQuot_apply, hx]
end ReciprocityTheory.ChartRestriction.L1
