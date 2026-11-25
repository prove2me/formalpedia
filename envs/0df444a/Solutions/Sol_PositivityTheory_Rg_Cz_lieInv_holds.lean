-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.lieInv_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:44.921778+00:00
-- url     : https://prove2.me/submissions/cf13881f-7fd3-450a-a842-b90143f24b2c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
import Theorems.Thm_PositivityTheory_Rg_Cz_LieInverse_hasDerivAt_det
import Theorems.Thm_PositivityTheory_Rg_Cz_LieInverse_Sop_add
import Theorems.Thm_PositivityTheory_Rg_Cz_LieInverse_Sop_single
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open LieInverse
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : LieInv := by
  intro n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG c ξ hξ τ a b
  have hbt : bar τ ≠ τ := hK.ne τ
  have hD : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
      Sop E bar τ X ξ = ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) • ξ := by
    intro X hX
    obtain ⟨cv, hc0, hcd, hcoth, hρ⟩ := hG.der τ X hX
    let D : ι → ℂ := fun τ' => if τ' = τ then X.trace else if τ' = bar τ then star X.trace else 0
    have hdet : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det) (D τ') 0 := by
      intro τ'
      by_cases h1 : τ' = τ
      · subst h1
        simp only [D, if_true]
        exact hasDerivAt_det _ X (by rw [hc0, hK.one]) hcd
      · by_cases h2 : τ' = bar τ
        · subst h2
          simp only [D, if_neg h1, if_true]
          have ht : (X.map star).trace = star X.trace := by simp [Matrix.trace, star_sum]
          rw [← ht]
          refine hasDerivAt_det _ _ (by rw [hc0, hK.one]) fun i j => ?_
          simp only [hK.conj, Matrix.map_apply]
          exact (hcd i j).star
        · simp only [D, if_neg h1, if_neg h2]
          have hf : (fun t => (κ τ' (cv t)).det) = fun _ => 1 := by
            funext t; rw [hcoth τ' h1 h2 t, Matrix.det_one]
          rw [hf]; exact hasDerivAt_const _ _
    have h1 : ∀ τ', (κ τ' (cv 0)).det = 1 := fun τ' => by rw [hc0, hK.one, Matrix.det_one]
    have hz : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det ^ c τ') ((c τ' : ℂ) * D τ') 0 := by
      intro τ'
      have := (hasDerivAt_zpow (c τ') ((κ τ' (cv 0)).det) (Or.inl (by rw [h1]; exact one_ne_zero))).comp
        (0 : ℝ) (hdet τ')
      rw [h1, _root_.one_zpow, mul_one] at this
      exact this
    have hχ : HasDerivAt (fun t => ∏ τ', (κ τ' (cv t)).det ^ c τ')
        ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) 0 := by
      have := HasDerivAt.finsetProd (u := Finset.univ) (fun τ' _ => hz τ')
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp [Finset.prod_apply])).congr_deriv ?_
      simp only [h1, _root_.one_zpow, Finset.prod_const_one, one_smul]
      rw [Finset.sum_eq_add_of_mem τ (bar τ) (Finset.mem_univ _) (Finset.mem_univ _) hbt.symm]
      · simp [D, hbt]
      · intro x _ hx; simp [D, hx.1, hx.2]
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro lam
    have h2 : HasDerivAt (fun t => lam (ρ (cv t) ξ))
        (((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) * lam ξ) 0 := by
      refine (hχ.mul_const (lam ξ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [hξ, map_smul, smul_eq_mul]
    have hu : lam (Sop E bar τ X ξ) = _ := (hρ ξ lam).unique h2
    rw [map_sub, hu, map_smul, smul_eq_mul, sub_self]
  have hsI : star Complex.I = -Complex.I := Complex.conj_I
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hX : (Matrix.single a a Complex.I)ᴴ = -Matrix.single a a Complex.I := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.single_apply]
      split_ifs with h1 h2 h2
      · simp [hsI]
      · exact (h2 ⟨h1.2, h1.1⟩).elim
      · exact (h1 ⟨h2.2, h2.1⟩).elim
      · simp
    have e := hD _ hX
    rw [Sop_single, Matrix.trace_single_eq_same, hsI] at e
    have e' : Complex.I • (E τ a a ξ - E (bar τ) a a ξ - ((c τ - c (bar τ) : ℤ) : ℂ) • ξ) = 0 := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply] at e
      push_cast
      linear_combination (norm := module) e
    rcases smul_eq_zero.mp e' with h | h
    · exact absurd h Complex.I_ne_zero
    · exact sub_eq_zero.mp h
  · rw [if_neg hab]
    have hX1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
        -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have hX2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
        -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have e1 := hD _ hX1
    have e2 := hD _ hX2
    rw [Sop_add, Sop_single, Sop_single, Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hab,
      Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)] at e1 e2
    simp only [LinearMap.add_apply, LinearMap.smul_apply, add_zero, star_zero, mul_zero, zero_smul, hsI,
      star_one, star_neg] at e1 e2
    have e2' : Complex.I • (E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ) = 0 := by
      linear_combination (norm := module) e2
    have e3 : E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ = 0 :=
      (smul_eq_zero.mp e2').resolve_left Complex.I_ne_zero
    linear_combination (norm := module) (1 / 2 : ℂ) • e1 + (1 / 2 : ℂ) • e3
end PositivityTheory.Rg.Cz
