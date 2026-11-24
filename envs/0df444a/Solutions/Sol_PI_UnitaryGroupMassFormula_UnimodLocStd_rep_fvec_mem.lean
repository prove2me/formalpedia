-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_fvec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:52.578995+00:00
-- url     : https://prove2.me/submissions/a1f4c73b-f143-4afb-a595-52d335255dcf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_omega1
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_omega2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
variable (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (x y : ℤ) (i₀ : m) : fvec a b d lam x y i₀ ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup]
  intro i
  by_cases h : i = i₀
  · subst h
    simp only [fvec, Pi.single_eq_same]
    exact PeriodPair.mem_lattice.2 ⟨x, y, by rw [rep_omega1, rep_omega2]; ring⟩
  · simp only [fvec, Pi.single_eq_of_ne h]
    exact zero_mem _
end PI.UnitaryGroupMassFormula.UnimodLocStd
