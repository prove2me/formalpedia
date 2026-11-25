-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.FK.der_fock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:00:24.512158+00:00
-- url     : https://prove2.me/submissions/c947466b-eb8f-43c8-808c-4f3d4c113d31

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivComm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_pderiv_cr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_FK_fock_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.FK
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.FK
theorem _root_.solution (hB : FockBasic) (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (sw k) (fock c p) = (2 * c : ℂ) • fock c (pderiv k p) := by
  classical
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  induction p using MvPolynomial.induction_on with
  | C a => rw [fock_C hB c hc]; simp [hL.map_zero]
  | add p q hp hq => rw [hL.map_add, map_add, hp, hq, map_add, hL.map_add, smul_add]
  | mul_X p k0 hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, ← hX, pderiv_mul, pderiv_X, hL.map_add, smul_add]
    by_cases h : k0 = k
    · subst h
      simp only [Pi.single_eq_same, if_true, mul_comm (X k0) (pderiv k0 p)]
      rw [one_mul, add_comm]
    · simp only [Pi.single_apply, h, if_false, add_zero, zero_smul, mul_comm (X k0) (pderiv k p)]
      rw [zero_mul, hL.map_zero, smul_zero, zero_add]
end PositivityTheory.Rg.Sw.LC.FK
