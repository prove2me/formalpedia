-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_periodic_411cd6442807
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:51.331251+00:00
-- url     : https://prove2.me/submissions/7f276e32-4624-4473-86b5-16bb110037a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_cusp_ne_10e65f158bd3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution (j : Fin a) (w : Fin n → ℂ) (hw : w ∈ logCover P.a_le) :
    P.tau0 (w + Pi.single (Fin.castLE P.a_le j) (2 * Real.pi * Complex.I)) = P.tau0 w := by
  have key : ∀ i : Fin a,
      ((w + Pi.single (Fin.castLE P.a_le j) (2 * Real.pi * Complex.I) : Fin n → ℂ) (Fin.castLE P.a_le i) /
          (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ) =
        (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) • (P.B i).map (Int.cast : ℤ → ℂ) +
          (Pi.single j ((P.B j).map (Int.cast : ℤ → ℂ)) : Fin a → Matrix (Fin g) (Fin g) ℂ) i := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [Pi.add_apply, Pi.single_eq_same, add_div, div_self two_pi_I_ne_zero, add_smul,
        one_smul]
    · simp [cusp_ne P hij, hij]
  simp only [PeriodPolydisc.tau0, P.periodic j w hw]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_pi_single']
  simp only [Finset.mem_univ, if_true]
  abel
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
