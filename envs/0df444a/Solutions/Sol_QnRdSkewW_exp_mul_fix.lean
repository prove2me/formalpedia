-- Prove2me | solution 1 for QnRdSkewW.exp_mul_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:12:38.618718+00:00
-- url     : https://prove2.me/submissions/64165c88-9346-4dbf-91c8-c45d3e87e768

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_SkewReductionGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace QnRdSkewW
theorem _root_.solution {n : ℕ} (X E : Matrix (Fin n) (Fin n) ℂ) (hXE : X * E = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) * E = E := by
  have hd : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E)
      (NormedSpace.exp ((s : ℂ) • X) * X * E) s := by
    intro s
    have h := hasDerivAt_exp_smul_const' (𝕂 := ℂ) X (s : ℂ)
    have h2 := h.scomp (x := s) Complex.ofRealCLM.hasDerivAt
    have h3 : HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • X))
        (NormedSpace.exp ((s : ℂ) • X) * X) s := by
      have hcomm : X * NormedSpace.exp ((s : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * X :=
        (((Commute.refl X).smul_right (s : ℂ)).exp_right).eq
      exact h2.congr_deriv (by simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]; exact hcomm)
    exact h3.mul_const E
  have hc := is_const_of_deriv_eq_zero (f := fun u : ℝ => NormedSpace.exp ((u : ℂ) • X) * E)
    (fun s => (hd s).differentiableAt) (fun s => by rw [(hd s).deriv, Matrix.mul_assoc, hXE, Matrix.mul_zero])
  have := hc t 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
  exact this
end QnRdSkewW
