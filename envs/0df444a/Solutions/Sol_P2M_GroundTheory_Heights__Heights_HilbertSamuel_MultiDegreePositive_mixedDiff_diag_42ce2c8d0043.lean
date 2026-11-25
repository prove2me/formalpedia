-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_diag_42ce2c8d0043
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:20.086864+00:00
-- url     : https://prove2.me/submissions/c288549d-a361-415e-8e48-81c7d22487f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMultiDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegrePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegreDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultiDegreePositive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultiDegreePositive_mixedDiff_succ_d48a8a9f08fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive
theorem _root_.solution {K : Type} [DecidableEq K] (h : (K → ℤ) → ℤ) (g : (Unit → ℤ) → ℤ)
    (hg : ∀ n : ℤ, g (fun _ => n) = h (fun _ => n)) (r : ℕ) (n : ℤ) :
    mixedDiff (fun _ : Fin r => fun _ : Unit => (1 : ℤ)) g (fun _ => n) =
      mixedDiff (fun _ : Fin r => fun _ : K => (1 : ℤ)) h (fun _ => n) := by
  induction r generalizing n with
  | zero => simpa [mixedDiff] using hg n
  | succ r ih =>
    rw [mixedDiff_succ, mixedDiff_succ]
    have e1 : ∀ (L : Type), ((fun _ : L => n) - fun _ : L => (1 : ℤ)) = fun _ => n - 1 :=
      fun L => funext fun _ => rfl
    simp only [diffStep, e1, ih]
end GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive
