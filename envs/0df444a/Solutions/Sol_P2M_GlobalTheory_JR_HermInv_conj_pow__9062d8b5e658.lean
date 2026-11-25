-- Prove2me | solution 1 for P2M_GlobalTheory_JR_HermInv_conj_pow__9062d8b5e658
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:09.999785+00:00
-- url     : https://prove2.me/submissions/61ac62f7-d4aa-4f6d-81ba-32f7306b5e05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (h h' M : Matrix (Fin r) (Fin r) E) (hh : h' * h = 1) (hh' : h * h' = 1) (k : ℕ) :
    (h * M * h') ^ k = h * M ^ k * h' := by
  induction k with
  | zero => simp [hh']
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc h' h, hh, one_mul]
end GlobalTheory.JR.HermInv
