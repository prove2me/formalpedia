-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:52.466183+00:00
-- url     : https://prove2.me/submissions/ff1475e1-7145-4ad8-90be-5c525096fd3a

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_zd_fderiv_symm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_zd_iter_two_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open scoped ContDiff
noncomputable section
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U) :
    ∀ k, ∀ y ∈ U, ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E),
      iteratedFDeriv ℂ k f y (v ∘ σ) = iteratedFDeriv ℂ k f y v := by
  intro k
  induction k with
  | zero =>
    intro y _ σ v
    congr 1
    exact Subsingleton.elim _ _
  | succ k ih =>
    intro y hy
    have hmul : ∀ σ τ : Equiv.Perm (Fin (k + 1)),
        (∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ σ) = iteratedFDeriv ℂ (k + 1) f y v) →
        (∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ τ) = iteratedFDeriv ℂ (k + 1) f y v) →
        ∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ ⇑(σ * τ)) =
          iteratedFDeriv ℂ (k + 1) f y v := by
      intro σ τ hσ hτ v
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hτ, hσ]
    have hstab : ∀ τ' : Equiv.Perm (Fin (k + 1)), τ' 0 = 0 →
        ∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ τ') =
          iteratedFDeriv ℂ (k + 1) f y v := by
      intro τ' h0 v
      set p := Equiv.Perm.decomposeFin τ' with hpdef
      have hp : τ' = Equiv.Perm.decomposeFin.symm p := by rw [hpdef, Equiv.symm_apply_apply]
      have hp1 : p.1 = 0 := by
        have := Equiv.Perm.decomposeFin_symm_apply_zero p.1 p.2
        rw [Prod.mk.eta, ← hp, h0] at this
        exact this.symm
      have hτ : τ' = Equiv.Perm.decomposeFin.symm (0, p.2) := by
        conv_lhs => rw [hp]
        congr 1
        exact Prod.ext hp1 rfl
      rw [hτ, iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have e1 : (v ∘ ⇑(Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), p.2))) 0 = v 0 := by
        simp [Equiv.Perm.decomposeFin_symm_apply_zero]
      have e2 : Fin.tail (v ∘ ⇑(Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), p.2))) =
          Fin.tail v ∘ p.2 := by
        funext i
        simp [Fin.tail, Equiv.Perm.decomposeFin_symm_apply_succ]
      rw [e1, e2]
      refine zd_fderiv_symm ?_ p.2 (v 0) (Fin.tail v)
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ih z hz
    rcases k with _ | k
    · intro σ v
      have hσ1 : σ = 1 := Equiv.ext fun i => Fin.ext (by
        have h1 := (σ i).isLt
        have h2 := i.isLt
        simp only [Equiv.Perm.coe_one, id_eq]
        omega)
      rw [hσ1]
      rfl
    have hswap01 : ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℂ (k + 2) f y (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) 1)) =
          iteratedFDeriv ℂ (k + 2) f y v := by
      intro v
      have hc : ContDiffAt ℂ 2 (iteratedFDeriv ℂ k f) y :=
        (hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (by
          first
          | exact_mod_cast (le_top : ((2 + k : ℕ) : ℕ∞) ≤ ⊤)
          | (norm_cast; exact le_top)
          | exact le_top
          | (rw [← WithTop.coe_natCast, ← WithTop.coe_ofNat, ← WithTop.coe_add]; exact WithTop.coe_le_coe.2 le_top))
      have hsym : IsSymmSndFDerivAt ℂ (iteratedFDeriv ℂ k f) y :=
        hc.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
      rw [zd_iter_two_left, zd_iter_two_left]
      have e3 : Fin.tail (Fin.tail (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) 1))) =
          Fin.tail (Fin.tail v) := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
      rw [e3]
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [hsym (v 1) (v 0)]
    have hswap : ∀ j : Fin (k + 2), ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℂ (k + 2) f y (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) j)) =
          iteratedFDeriv ℂ (k + 2) f y v := by
      intro j
      by_cases hj0 : j = 0
      · subst hj0
        intro v
        rw [Equiv.swap_self]
        rfl
      by_cases hj1 : j = 1
      · subst hj1
        exact hswap01
      have h01 : (0 : Fin (k + 2)) ≠ 1 := by simp
      have hconj : Equiv.swap (1 : Fin (k + 2)) j * Equiv.swap 0 1 * Equiv.swap 1 j =
          Equiv.swap 0 j := by
        rw [Equiv.swap_mul_swap_mul_swap h01 (Ne.symm hj0), Equiv.swap_comm]
      have hfix : (Equiv.swap (1 : Fin (k + 2)) j) 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hj0)
      rw [← hconj]
      exact hmul _ _ (hmul _ _ (hstab _ hfix) hswap01) (hstab _ hfix)
    intro σ v
    have hfix : (Equiv.swap 0 (σ 0) * σ) 0 = 0 := by
      simp [Equiv.swap_apply_right]
    rw [← Equiv.swap_mul_self_mul (0 : Fin (k + 2)) (σ 0) σ]
    exact hmul _ _ (hswap _) (hstab _ hfix) v
end ReciprocityTheory.L2DbarEstimates.Y
