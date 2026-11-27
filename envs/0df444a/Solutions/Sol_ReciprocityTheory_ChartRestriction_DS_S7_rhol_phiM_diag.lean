-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.rhol_phiM_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:10.051379+00:00
-- url     : https://prove2.me/submissions/34de9dde-5c4d-4d55-9b2e-8bbade72b84f

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
private theorem isLowerTri_one : IsLowerTri (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne h.ne
private theorem diag_line (a l : Fin n) (t : ℂ) :
    (1 + t • Matrix.single a a (1 : ℂ)) l l = if l = a then 1 + t else 1 := by
  by_cases h : l = a
  · subst h
    simp
  · have : ¬(a = l ∧ a = l) := fun h' => h h'.1.symm
    simp [h, Matrix.single_apply_of_ne (h := this)]
private theorem diag_prod (μ : Fin n → ℤ) (a : Fin n) (t : ℂ) :
    ∏ l, ((if l = a then 1 + t else 1) : ℂ) ^ (-μ l) = (1 + t) ^ (-μ a) := by
  rw [Finset.prod_eq_single a (fun l _ hl => by simp [hl]) (by simp)]
  simp
private theorem hasDerivAt_scale (μ : Fin n → ℤ) (a : Fin n) (c : ℂ) :
    HasDerivAt (fun t : ℂ => (1 + t) ^ (-μ a) * c) (-(μ a : ℂ) * c) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => 1 + t) 1 0 := by
    simpa using (hasDerivAt_id' (0 : ℂ)).const_add 1
  have h2 := (hasDerivAt_zpow (-μ a) (1 + 0 : ℂ) (Or.inl (by simp))).comp (0 : ℂ) h1
  simpa [Function.comp_def] using h2.mul_const c
private theorem eventually_ne_line : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 :=
  (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)
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
theorem _root_.solution (μ : Fin n → ℤ) (a : Fin n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Rhol (Matrix.single a a 1) (PhiM μ) z = -(μ a : ℂ) * PhiM μ z := by
  have key : ∀ t : ℂ, 1 + t ≠ 0 →
      PhiM μ (z + t • (z * Matrix.single a a 1)) = (1 + t) ^ (-μ a) * PhiM μ z := by
    intro t ht
    have hc : IsUpperTri (1 + t • Matrix.single a a (1 : ℂ)) := by
      intro i j hij
      have : ¬(a = i ∧ a = j) := fun ⟨h1, h2⟩ => hij.ne' (h1.symm.trans h2)
      simp [Matrix.one_apply_ne hij.ne', Matrix.single_apply_of_ne (h := this)]
    obtain ⟨-, h⟩ := phiM_tri_mul μ isLowerTri_one hc (fun l => by simp)
      (fun l => by rw [diag_line]; split_ifs <;> simp [ht]) hz
    have e : 1 * z * (1 + t • Matrix.single a a (1 : ℂ)) = z + t • (z * Matrix.single a a 1) := by
      rw [Matrix.one_mul, mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [← e, h]
    congr 1
    simp only [Matrix.one_apply_eq, one_mul, diag_line]
    exact diag_prod μ a t
  have hev : (fun t : ℂ => PhiM μ (z + t • (z * Matrix.single a a 1))) =ᶠ[nhds 0]
      fun t => (1 + t) ^ (-μ a) * PhiM μ z := by
    filter_upwards [eventually_ne_line] with t ht using key t ht
  have hd := hasDerivAt_line (differentiableAt_phiM μ hz) (z * Matrix.single a a 1)
  exact hd.unique ((hasDerivAt_scale μ a _).congr_of_eventuallyEq hev)
end ReciprocityTheory.ChartRestriction.DS.S7
