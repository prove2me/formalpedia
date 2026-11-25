-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.lhol_phiM_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:04.400841+00:00
-- url     : https://prove2.me/submissions/28c6c7b6-1527-4cd7-95a5-48735f5e6fba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_differentiableAt_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hasDerivAt_line
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_tri_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem isUpperTri_one : IsUpperTri (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne h.ne'
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) {a b : Fin n} (hab : b < a) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) : Lhol (Matrix.single a b 1) (PhiM μ) z = 0 := by
  have hconst : ∀ t : ℂ, PhiM μ (z + t • (Matrix.single a b 1 * z)) = PhiM μ z := by
    intro t
    have hc : IsLowerTri (1 + t • Matrix.single a b (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ b = j) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (hab.trans hij) (lt_irrefl _)
      simp [Matrix.one_apply_ne hij.ne, Matrix.single_apply_of_ne (h := this)]
    have hcd : ∀ l, (1 + t • Matrix.single a b (1 : ℂ)) l l = 1 := by
      intro l
      have : ¬(a = l ∧ b = l) := fun ⟨h1, h2⟩ => hab.ne' (h1.trans h2.symm)
      simp [Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ hc isUpperTri_one (fun l => by rw [hcd l]; exact one_ne_zero)
      (fun l => by simp) hz
    have e : (1 + t • Matrix.single a b (1 : ℂ)) * z * 1 = z + t • (Matrix.single a b 1 * z) := by
      rw [Matrix.mul_one, add_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [← e, h, Finset.prod_eq_one (fun l _ => by rw [hcd l, Matrix.one_apply_eq, mul_one, _root_.one_zpow]),
      one_mul]
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (Matrix.single a b 1 * z)
  have h0 : HasDerivAt (fun t : ℂ => PhiM μ (z + t • (Matrix.single a b 1 * z))) 0 0 := by
    simp only [hconst]
    exact hasDerivAt_const _ _
  exact hd.unique h0
end ReciprocityTheory.ChartRestriction.DS.S7
