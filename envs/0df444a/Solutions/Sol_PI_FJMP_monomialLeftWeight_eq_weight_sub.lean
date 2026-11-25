-- Prove2me | solution 1 for PI.FJMP.monomialLeftWeight_eq_weight_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:53:40.935075+00:00
-- url     : https://prove2.me/submissions/e15163eb-662b-4b85-b0fa-dcfe8edbe692

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_eig_of_mem_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
namespace PI.FJMP
theorem _root_.solution (hW : FormWt1) {p q r s : ℕ} {μ : Ix p q → ℚ} {P : Pol p q r s}
    (hP : P ∈ hwSub (fockAct1 p q r s) μ) (e : Ln p q r s →₀ ℕ) (he : e ∈ P.support) (a : Ix p q) :
    ((wt1 e a : ℤ) : ℚ) = nu1 p q r s μ a := by
  have h1 : P ∈ wtSub (fockAct1 p q r s) μ := by
    unfold hwSub at hP
    exact (Submodule.mem_inf.mp hP).1
  have h2 : fockAct1 p q r s (Eab a a) P = (((μ a : ℚ) : ℂ)) • P := by
    unfold wtSub at h1
    have h3 := (Submodule.mem_iInf _).mp h1 a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h3
    exact h3
  have h4 : ((((wt1 e a : ℤ) : ℚ) + sh1 p q r s a : ℚ) : ℂ) = (((μ a : ℚ)) : ℂ) :=
    eig_of_mem_support (fockAct1 p q r s (Eab a a))
      (fun m => ((((wt1 m a : ℤ) : ℚ) + sh1 p q r s a : ℚ) : ℂ)) (fun m => hW p q r s a m) P _ h2 e he
  have h5 : ((wt1 e a : ℤ) : ℚ) + sh1 p q r s a = μ a := by exact_mod_cast h4
  rcases a with i | j
  · simp only [nu1, shiftNu]
    simp only [sh1, Sum.elim_inl] at h5
    linarith
  · simp only [nu1, shiftNu]
    simp only [sh1, Sum.elim_inr] at h5
    linarith
end PI.FJMP
