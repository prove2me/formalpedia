-- Prove2me | solution 1 for PI.WGB.fockF_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:52.89517+00:00
-- url     : https://prove2.me/submissions/5c52fd77-a9df-444d-bab5-55b30ec49365

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFRowActRight
import Theorems.Thm_PI_WGB_fockF_smul_left
import Theorems.Thm_PI_WGB_fockF_smul_right
import Theorems.Thm_PI_WGB_fockF_sum_left
import Theorems.Thm_PI_WGB_fockF_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)
namespace PI.WGB
theorem _root_.solution {σ ι : Type} (s : Finset ι) (a : ι → ℂ) (x : ι → MvPolynomial σ ℂ) :
    fockF (∑ i ∈ s, a i • x i) (∑ j ∈ s, a j • x j) =
      ∑ i ∈ s, ∑ j ∈ s, a i * star (a j) * fockF (x i) (x j) := by
  rw [fockF_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fockF_smul_left, fockF_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fockF_smul_right]
  ring
end PI.WGB
