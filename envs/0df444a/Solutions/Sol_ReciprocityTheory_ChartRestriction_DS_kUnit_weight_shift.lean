-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kUnit_weight_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:23:21.125029+00:00
-- url     : https://prove2.me/submissions/47217512-582c-4c0c-a733-8bc988d02138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_Lemmata_SimultaneousEigenvectors_BlSimeig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_IsKUnitaryOfIsInfUnitary

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hA : IsGlRep A) {μ : Fin n → ℝ} {w : X} (hw : ∀ c, A c c w = (μ c : ℂ) • w)
    {a b : Fin n} (hab : a ≠ b) (c : Fin n) :
    A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
  have h := LinearMap.congr_fun (hA c c a b) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
  by_cases hca : c = a
  · subst hca
    simp [hab, Ne.symm hab] at h ⊢
    linear_combination (norm := module) h
  · by_cases hcb : c = b
    · subst hcb
      simp [hca] at h ⊢
      linear_combination (norm := module) h
    · simp [hca, hcb, Ne.symm hcb] at h ⊢
      linear_combination (norm := module) h
end ReciprocityTheory.ChartRestriction.DS
