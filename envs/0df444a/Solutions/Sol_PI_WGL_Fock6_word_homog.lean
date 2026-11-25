-- Prove2me | solution 1 for PI.WGL.Fock6.word_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:51.638345+00:00
-- url     : https://prove2.me/submissions/06cb8599-9ccd-41eb-8375-4454f8e8ee17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftFock
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
namespace Fock6
private theorem isWeightedHomogeneous_coeff_mul_rw1 {r n : ℕ} (c : Fin r) (s D E : ℤ) (P Q : Polynomial (MvPolynomial (Fin r × Fin n) ℂ))
    (hP : ∀ j : ℕ, IsWeightedHomogeneous (rw1 c) (P.coeff j) (D + j * s))
    (hQ : ∀ j : ℕ, IsWeightedHomogeneous (rw1 c) (Q.coeff j) (E + j * s)) (j : ℕ) :
    IsWeightedHomogeneous (rw1 c) ((P * Q).coeff j) ((D + E) + j * s) := by
  rw [Polynomial.coeff_mul, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hx' : x.1 + x.2 = j := by simpa using hx
  rw [show (D + E) + (j : ℤ) * s = (D + (x.1 : ℤ) * s) + (E + (x.2 : ℤ) * s) by
    rw [← hx']
    push_cast
    ring]
  exact (hP x.1).mul (hQ x.2)
private theorem isWeightedHomogeneous_coeff_one_rw1 {r n : ℕ} (c : Fin r) (s : ℤ) (j : ℕ) :
    IsWeightedHomogeneous (rw1 c) ((1 : Polynomial (MvPolynomial (Fin r × Fin n) ℂ)).coeff j) (0 + j * s) := by
  by_cases hj : j = 0
  · subst hj
    simpa using isWeightedHomogeneous_one ℂ (rw1 (n := n) c)
  · rw [show (1 : Polynomial (MvPolynomial (Fin r × Fin n) ℂ)).coeff j = 0 by simp [Polynomial.coeff_one, hj]]
    exact isWeightedHomogeneous_zero ℂ _ _
private theorem isWeightedHomogeneous_coeff_rowGen_X {r n : ℕ} (a b c : Fin r) (v : Fin r × Fin n) (j : ℕ) :
    IsWeightedHomogeneous (rw1 c) ((rowGen ℂ a b (X v : MvPolynomial (Fin r × Fin n) ℂ)).coeff j)
      (rw1 c v + j * ((if a = c then 1 else 0) - (if b = c then 1 else 0))) := by
  have hX : ∀ u : Fin r × Fin n, IsWeightedHomogeneous (rw1 c) (X u : MvPolynomial (Fin r × Fin n) ℂ) (rw1 c u) :=
    fun u => isWeightedHomogeneous_X ℂ _ u
  have hdeg : ∀ (φ : MvPolynomial (Fin r × Fin n) ℂ) (d d' : ℤ), d = d' →
      IsWeightedHomogeneous (rw1 c) φ d → IsWeightedHomogeneous (rw1 c) φ d' := fun φ d d' e h => e ▸ h
  unfold rowGen
  rw [aeval_X]
  by_cases hv : v.1 = b
  · rw [if_pos hv]
    have hr : ∀ u : Fin r × Fin n, rw1 c u = if u.1 = c then 1 else 0 := fun u => by
      unfold rw1 wa
      split_ifs <;> simp
    rcases j with _ | _ | k
    · rw [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero, add_zero]
      exact hdeg _ _ _ (by simp) (hX v)
    · rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_zero]
      refine hdeg _ _ _ ?_ (hX (a, v.2))
      rw [hr, hr, hv]
      dsimp only
      split_ifs <;> norm_num
    · rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C, if_neg (by omega)]
      exact isWeightedHomogeneous_zero ℂ _ _
  · rw [if_neg hv, add_zero, Polynomial.coeff_C]
    by_cases hj : j = 0
    · rw [if_pos hj]
      subst hj
      exact hdeg _ _ _ (by simp) (hX v)
    · rw [if_neg hj]
      exact isWeightedHomogeneous_zero ℂ _ _
private theorem isWeightedHomogeneous_coeff_pow_rw1 {r n : ℕ} (c : Fin r) (s D : ℤ) (P : Polynomial (MvPolynomial (Fin r × Fin n) ℂ))
    (hP : ∀ j : ℕ, IsWeightedHomogeneous (rw1 c) (P.coeff j) (D + j * s)) (e : ℕ) :
    ∀ j : ℕ, IsWeightedHomogeneous (rw1 c) ((P ^ e).coeff j) ((e : ℤ) * D + j * s) := by
  induction e with
  | zero =>
    intro j
    simpa using isWeightedHomogeneous_coeff_one_rw1 (n := n) c s j
  | succ e ih =>
    intro j
    rw [pow_succ, show ((e + 1 : ℕ) : ℤ) * D + (j : ℤ) * s = ((e : ℤ) * D + D) + j * s by push_cast; ring]
    exact isWeightedHomogeneous_coeff_mul_rw1 c s _ _ (P ^ e) P ih hP j
private theorem isWeightedHomogeneous_coeff_prod_rowGen_X_pow {r n : ℕ} (a b c : Fin r) (m : Fin r × Fin n →₀ ℕ) (t : Finset (Fin r × Fin n)) :
    ∀ j : ℕ, IsWeightedHomogeneous (rw1 c)
      ((∏ v ∈ t, (rowGen ℂ a b (X v : MvPolynomial (Fin r × Fin n) ℂ)) ^ (m v)).coeff j)
      ((∑ v ∈ t, (m v : ℤ) * rw1 c v) + j * ((if a = c then 1 else 0) - (if b = c then 1 else 0))) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · intro j
    simpa using isWeightedHomogeneous_coeff_one_rw1 (n := n) c _ j
  · intro v t hv ih j
    rw [Finset.prod_insert hv, Finset.sum_insert hv]
    exact isWeightedHomogeneous_coeff_mul_rw1 c _ _ _ _ _ (isWeightedHomogeneous_coeff_pow_rw1 c _ _ _ (isWeightedHomogeneous_coeff_rowGen_X a b c v) (m v)) ih j
private theorem isWeightedHomogeneous_coeff_rowGen {r n : ℕ} (a b c : Fin r) (g : MvPolynomial (Fin r × Fin n) ℂ) (H : ℤ)
    (hg : IsWeightedHomogeneous (rw1 c) g H) (j : ℕ) :
    IsWeightedHomogeneous (rw1 c) ((rowGen ℂ a b g).coeff j)
      (H + j * ((if a = c then 1 else 0) - (if b = c then 1 else 0))) := by
  classical
  rw [g.as_sum, map_sum, Polynomial.finset_sum_coeff, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hw := hg (mem_support_iff.mp hm)
  have hC : rowGen ℂ a b (C (coeff m g) : MvPolynomial (Fin r × Fin n) ℂ) = Polynomial.C (C (coeff m g)) := by
    unfold rowGen
    rw [aeval_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
  simp only [map_pow]
  rw [hC, Polynomial.coeff_C_mul]
  have hp := isWeightedHomogeneous_coeff_prod_rowGen_X_pow a b c m m.support j
  have hsum : (∑ v ∈ m.support, (m v : ℤ) * rw1 c v) = H := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl (fun v _ => by rw [nsmul_eq_mul])
  rw [hsum] at hp
  rw [MvPolynomial.C_mul', ← mem_weightedHomogeneousSubmodule]
  exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp)
end Fock6
end PI.WGL
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial
open PI.WGL.Fock6
namespace PI.WGL.Fock6
theorem _root_.solution {r n : ℕ} (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : ∀ c : Fin r, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) f H) :
    ∀ c : Fin r, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) (applyWord ℂ w f) H := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    intro c
    obtain ⟨H, hH⟩ := ih c
    exact ⟨_, isWeightedHomogeneous_coeff_rowGen x.1 x.2.1 c (applyWord ℂ w f) H hH x.2.2⟩
end PI.WGL.Fock6
