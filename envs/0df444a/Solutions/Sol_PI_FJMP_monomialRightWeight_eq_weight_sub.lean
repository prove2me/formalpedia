-- Prove2me | solution 1 for PI.FJMP.monomialRightWeight_eq_weight_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:58:58.415374+00:00
-- url     : https://prove2.me/submissions/833d290d-ac17-4026-807c-0817ab050052

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
theorem _root_.solution (hW : FormWt2) {p q r s : ℕ} {μ' : Ix r s → ℚ} {P : Pol p q r s}
    (hP : P ∈ hwSub (fockAct2 p q r s) μ') (e : Ln p q r s →₀ ℕ) (he : e ∈ P.support) (c : Ix r s) :
    ((wt2 e c : ℤ) : ℚ) = nu2 p q r s μ' c := by
  have h1 : P ∈ wtSub (fockAct2 p q r s) μ' := by
    unfold hwSub at hP
    exact (Submodule.mem_inf.mp hP).1
  have h2 : fockAct2 p q r s (Eab c c) P = (((μ' c : ℚ) : ℂ)) • P := by
    unfold wtSub at h1
    have h3 := (Submodule.mem_iInf _).mp h1 c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h3
    exact h3
  have h4 : ((((wt2 e c : ℤ) : ℚ) + sh2 p q r s c : ℚ) : ℂ) = (((μ' c : ℚ)) : ℂ) :=
    eig_of_mem_support (fockAct2 p q r s (Eab c c))
      (fun m => ((((wt2 m c : ℤ) : ℚ) + sh2 p q r s c : ℚ) : ℂ)) (fun m => hW p q r s c m) P _ h2 e he
  have h5 : ((wt2 e c : ℤ) : ℚ) + sh2 p q r s c = μ' c := by exact_mod_cast h4
  rcases c with i | j
  · simp only [nu2, shiftNu]
    simp only [sh2, Sum.elim_inl] at h5
    linarith
  · simp only [nu2, shiftNu]
    simp only [sh2, Sum.elim_inr] at h5
    linarith
end PI.FJMP
