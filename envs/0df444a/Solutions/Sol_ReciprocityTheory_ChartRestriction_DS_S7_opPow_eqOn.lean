-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.opPow_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:52.487975+00:00
-- url     : https://prove2.me/submissions/a51f1e1b-1788-45f9-81c7-b4b9ae8d5311

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsOfFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_eOp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) (a b : Fin n) :
    Set.EqOn (opPow (fun a b => Lhol (Y a b)) k a b F)
      (fun z => c ^ k * ((ePow (fun a b => eOp (X a b)) k (σ a) (σ b) G : smoothS n) :
        Matrix (Fin n) (Fin n) ℂ → ℂ) z) (OmegaSet n) := by
  unfold ePow
  simp only [Bl.ThirdBlockLemmaA.goal1]
  induction k generalizing a b with
  | zero =>
    intro z hz
    by_cases hab : a = b
    · subst hab
      simp [opPow, Matrix.one_apply, hFG hz]
    · have hs : σ a ≠ σ b := fun h => hab (σ.injective h)
      simp [opPow, Matrix.one_apply, hab, hs]
  | succ k ih =>
    intro z hz
    have hterm : ∀ d, Lhol (Y a d) (opPow (fun a b => Lhol (Y a b)) k d b F) z =
        c ^ (k + 1) * ((eOp (X (σ a) (σ d)) ((((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G) :
          smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
      intro d
      set g : smoothS n := (((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G with hg
      rw [lhol_congr (ih d b) hz, eOp_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (fun w => c ^ k * (g : Matrix (Fin n) (Fin n) ℂ → ℂ) w) z (Y a d * z) =
        c ^ (k + 1) * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (X (σ a) (σ d) * z)
      erw [fderiv_const_mul (differentiableAt_of_mem g.2 hz) (c ^ k)]
      rw [hY a d, Matrix.smul_mul]
      show c ^ k * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (c • (X (σ a) (σ d) * z)) = _
      rw [map_smul, smul_eq_mul]
      ring
    simp only [opPow, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun d _ => hterm d, pow_succ' (Matrix.of fun a b => eOp (X a b)) k,
      Matrix.mul_apply]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply,
      Matrix.of_apply, Finset.mul_sum]
    exact Fintype.sum_equiv σ _ _ (fun d => rfl)
end ReciprocityTheory.ChartRestriction.DS.S7
