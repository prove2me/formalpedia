-- Prove2me | solution 1 for ProbabilityTheory.Copula.IsClassical.sub_le_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:56:18.229607+00:00
-- url     : https://prove2.me/submissions/59e42214-3c1a-4f7e-a188-8304ed1354ee

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_monotone
public import Theorems.Thm_ProbabilityTheory_Copula_IsClassical_sub_le_sum_of_le

set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}
namespace ProbabilityTheory.Copula
namespace IsClassical
theorem _root_.solution (hF : IsClassical F) (a b : Fin d → I) :
    F a - F b ≤ ∑ i, |(a i : ℝ) - (b i : ℝ)| := by
  have h := hF.sub_le_sum_of_le b (a ⊔ b) le_sup_right
  have hm := hF.monotone (show a ≤ a ⊔ b from le_sup_left)
  have hs : ∑ i, (((a ⊔ b) i : ℝ) - (b i : ℝ)) ≤
      ∑ i, |(a i : ℝ) - (b i : ℝ)| := by
    apply Finset.sum_le_sum
    intro i _
    change max (a i : ℝ) (b i : ℝ) - (b i : ℝ) ≤ _
    rw [← max_sub_sub_right, sub_self]
    exact max_le (le_abs_self _) (abs_nonneg _)
  linarith
end IsClassical
end ProbabilityTheory.Copula
