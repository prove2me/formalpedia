-- Prove2me | solution 1 for PI.WFJM.hc_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:53.898387+00:00
-- url     : https://prove2.me/submissions/af7f1cd9-a94c-4e5e-8c73-e0ba0bfd2308

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix FockH1Action
namespace PI.WFJM
end PI.WFJM
namespace PI.WFJM
open MvPolynomial
open PI.FJM
section Grade
open MvPolynomial
variable {σ : Type*}
private theorem isHomogeneous_X_one (k : σ) : (X k : MvPolynomial σ ℂ).IsHomogeneous 1 := by
  first
  | exact isHomogeneous_X ℂ k
  | exact isHomogeneous_X k
private theorem homogeneousComponent_monomial_of_isHomogeneous {v : σ →₀ ℕ} {b : ℂ} {N : ℕ}
    (h : (monomial v b).IsHomogeneous N) (e : ℕ) :
    homogeneousComponent e (monomial v b) = if e = N then monomial v b else 0 :=
  homogeneousComponent_of_mem ((mem_homogeneousSubmodule N _).mpr h)
private theorem homogeneousComponent_pderiv_monomial_eq_pderiv_succ (l : σ) (e : ℕ) (u : σ →₀ ℕ) (c : ℂ) :
    homogeneousComponent e (pderiv l (monomial u c)) =
      pderiv l (homogeneousComponent (e + 1) (monomial u c)) := by
  by_cases hu : u l = 0
  · have h0 : pderiv l (monomial u c) = 0 := by
      rw [pderiv_monomial, hu]
      simp
    rw [h0, map_zero, homogeneousComponent_monomial_of_isHomogeneous (isHomogeneous_monomial c rfl)]
    split_ifs <;> simp [h0]
  · have hle : Finsupp.single l 1 ≤ u :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hu)
    have hsplit : monomial u c = X l * monomial (u - Finsupp.single l 1) c := by
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    have hv := isHomogeneous_monomial (R := ℂ) (d := u - Finsupp.single l 1) c rfl
    have hU : (monomial u c).IsHomogeneous (1 + Finsupp.degree (u - Finsupp.single l 1)) := by
      rw [hsplit]
      exact (isHomogeneous_X_one l).mul hv
    rw [pderiv_monomial, homogeneousComponent_monomial_of_isHomogeneous (isHomogeneous_monomial _ rfl),
      homogeneousComponent_monomial_of_isHomogeneous hU]
    split_ifs <;> first | omega | rw [pderiv_monomial] | simp
end Grade
section Lap
variable {p q r s : ℕ}
end Lap
section HW
variable {p q r s : ℕ}
open MvPolynomial
end HW
end PI.WFJM
namespace PI.FJM
end PI.FJM
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
open MvPolynomial
variable {σ : Type*}
namespace PI.WFJM
theorem _root_.solution (l : σ) (e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent e (pderiv l P) = pderiv l (homogeneousComponent (e + 1) P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u c => exact homogeneousComponent_pderiv_monomial_eq_pderiv_succ l e u c
  | add P Q hP hQ => simp only [map_add, hP, hQ]
end PI.WFJM
