-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CEq.equivar_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:06.754106+00:00
-- url     : https://prove2.me/submissions/4dc36bef-76f1-4bf7-8e5c-37ed2c465e6d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyEq
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_iteratedFDeriv_comp_clm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_symm_perm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_CEq_mul_single_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
private theorem sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj (F : Matrix ι ι ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ}
    (a : Fin n ≃ ι) (r : Fin n → ι) (hr : ¬ Function.Injective r) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, r i = r j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hr
    obtain ⟨i, j, h, hne⟩ := hr
    exact ⟨i, j, h, hne⟩
  have hane : a i ≠ a j := fun h => hne (a.injective h)
  have key : ∀ σ : Equiv.Perm ι, iteratedFDeriv ℂ n F 0
      (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) =
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) := by
    intro σ
    rw [← symm_perm F hF (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) (Equiv.swap i j)]
    congr 1
    funext k
    simp only [Function.comp, Equiv.Perm.mul_apply]
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left, hij]
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right, hij]
      · have h1 : a k ≠ a i := fun h => hki (a.injective h)
        have h2 : a k ≠ a j := fun h => hkj (a.injective h)
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hS := (Equiv.sum_comp (Equiv.mulRight (Equiv.swap (a i) (a j)))
    (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)))).symm
  have hg : ∀ σ : Equiv.Perm ι, ((Equiv.Perm.sign (σ * Equiv.swap (a i) (a j)) : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0
        (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) =
      -(((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ))) := by
    intro σ
    rw [key σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hane]
    push_cast
    ring
  simp only [Equiv.coe_mulRight] at hS
  rw [Finset.sum_congr rfl (fun σ _ => hg σ), Finset.sum_neg_distrib] at hS
  have h2 : (2 : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0 := by
    linear_combination hS
  simpa using h2
private theorem sum_sign_iteratedFDeriv_single_perm_eq_sign_mul (F : Matrix ι ι ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ}
    (a : Fin n ≃ ι) (ρ : Equiv.Perm ι) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) =
    ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ)) := by
  have hterm : ∀ σ : Equiv.Perm ι,
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) =
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) := by
    intro σ
    rw [← symm_perm F hF (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ))
      ((a.trans ρ).trans a.symm)]
    congr 1
    funext k
    simp [Equiv.Perm.mul_apply]
  calc ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ))
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) :=
        Finset.sum_congr rfl fun σ _ => by rw [hterm σ]
    _ = ∑ τ : Equiv.Perm ι, ((Equiv.Perm.sign (τ * ρ) : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((τ * ρ * ρ⁻¹) (a k)) (1 : ℂ)) :=
        (Equiv.sum_comp (Equiv.mulRight ρ) (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          iteratedFDeriv ℂ n F 0
            (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)))).symm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [mul_inv_cancel_right, Equiv.Perm.sign_mul]
        push_cast
        ring
end PositivityTheory.Rg.Sw.LVs.CEq
namespace PositivityTheory.Rg.Sw.LVs
end PositivityTheory.Rg.Sw.LVs
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CEq
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace PositivityTheory.Rg.Sw.LVs.CEq
theorem _root_.solution : Equivar := by
  intro ι _ _ F A hF
  let a : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let L : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ A)
  have hΦ : ∀ σ : Equiv.Perm ι,
      iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0
        (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) =
      ∑ r : Fin (Fintype.card ι) → ι, (∏ i, A (r i) (a i)) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ)) := by
    intro σ
    have h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0
        (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) =
        iteratedFDeriv ℂ (Fintype.card ι) F 0
          (fun i => A * Matrix.single (a i) (σ (a i)) (1 : ℂ)) :=
      iteratedFDeriv_comp_clm F hF L _ _
    rw [h1]
    simp_rw [mul_single_eq]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have hswap : detD (fun T => F (A * T)) = ∑ r : Fin (Fintype.card ι) → ι,
      (∏ i, A (r i) (a i)) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ)) := by
    unfold detD
    rw [Finset.sum_congr rfl fun σ _ => by rw [hΦ σ]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [hswap]
  have hinj : ∀ ρ ∈ (Finset.univ : Finset (Equiv.Perm ι)), ∀ ρ' ∈ (Finset.univ : Finset (Equiv.Perm ι)),
      (fun i => ρ (a i)) = (fun i => ρ' (a i)) → ρ = ρ' := by
    intro ρ _ ρ' _ h
    ext x
    simpa [a] using congrFun h (Fintype.equivFin ι x)
  rw [← Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset (Equiv.Perm ι)).image fun ρ => (fun i => ρ (a i)))),
    Finset.sum_image hinj]
  · have hD : detD F = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ)) := rfl
    simp_rw [sum_sign_iteratedFDeriv_single_perm_eq_sign_mul F hF a, ← hD]
    rw [Matrix.det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [show (∏ i, A (ρ (a i)) (a i)) = ∏ x, A (ρ x) x from Equiv.prod_comp a (fun x => A (ρ x) x)]
    ring
  · intro r _ hr
    rw [sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj F hF a r ?_, mul_zero]
    intro hr'
    apply hr
    rw [Finset.mem_image]
    refine ⟨Equiv.ofBijective (fun x => r (a.symm x))
      ((hr'.comp a.symm.injective).bijective_of_finite), Finset.mem_univ _, ?_⟩
    funext i
    simp
end PositivityTheory.Rg.Sw.LVs.CEq
