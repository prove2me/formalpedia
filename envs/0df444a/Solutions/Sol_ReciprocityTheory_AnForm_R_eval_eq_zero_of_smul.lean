-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:18.803027+00:00
-- url     : https://prove2.me/submissions/24a416ee-845b-4416-a6e0-2094c2f81bff

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_eval_smul_of_isMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (c : K → ℂ) (y : (Σ k, ι k) → ℂ) (hy : ∀ f ∈ P, eval y f = 0) :
    ∀ f ∈ P, eval (fun q => c q.1 * y q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hP
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha⟩ := hS g hg
    rw [eval_smul_of_isMultiHomog ha, hy g (Ideal.subset_span hg), mul_zero]
  | zero => simp
  | add g h _ _ hg hh => rw [map_add, hg, hh, add_zero]
  | smul a g _ hg => rw [smul_eq_mul, map_mul, hg, mul_zero]
end ReciprocityTheory.AnForm.R
