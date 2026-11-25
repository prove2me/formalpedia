-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.modM_tr_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:13.109554+00:00
-- url     : https://prove2.me/submissions/9a32b66b-db50-44c8-adef-dfe5725e778f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Theorems.Thm_PI_VolSemiDirect_W_Cj_trG_val
import Theorems.Thm_PI_VolSemiDirect_W_Cj_trG_mul
import Theorems.Thm_PI_VolSemiDirect_W_Cj_trG_one
import Theorems.Thm_PI_VolSemiDirect_W_Cj_trG_inv
import Theorems.Thm_PI_VolSemiDirect_W_Cj_modM_transv
import Theorems.Thm_PI_VolSemiDirect_W_Cj_transvection_transpose
import Theorems.Thm_PI_VolSemiDirect_W_Cj_modM_inv
import Theorems.Thm_PI_VolSemiDirect_W_Cj_modM_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Measure
open scoped NNReal
variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
  [BorelSpace A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (hT : TransvHaar) (X : GL (Fin k) A)
    (hX : X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})) :
    modM (trG X) = modM X := by
  induction hX using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, c, hij, hx⟩ | ⟨d, hx⟩
    · rw [modM_transv hT x i j hij c hx, modM_transv hT (trG x) j i hij.symm c
        (by rw [trG_val, hx, transvection_transpose])]
    · have : trG x = x := by
        ext1
        rw [trG_val, hx, Matrix.diagonal_transpose]
      rw [this]
  | one => rw [trG_one]
  | mul x y _ _ hx hy => rw [trG_mul, modM_mul, modM_mul, hx, hy, mul_comm]
  | inv x _ hx => rw [trG_inv, modM_inv, modM_inv, hx]
end PI.VolSemiDirect.W.Cj
