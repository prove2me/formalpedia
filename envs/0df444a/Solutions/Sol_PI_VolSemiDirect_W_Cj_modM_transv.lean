-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.modM_transv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:02:51.440291+00:00
-- url     : https://prove2.me/submissions/08440e33-264f-4c54-ba20-a415c9f62c6e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_MapPhiOfModM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_NnrealEqOneOfMulSelf
import Theorems.Thm_PI_VolSemiDirect_W_Cj_modM_of_map
import Theorems.Thm_PI_VolSemiDirect_W_Cj_phi_apply


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
theorem _root_.solution (hT : TransvHaar) (X : GL (Fin k) A) (i j : Fin k) (hij : i ≠ j) (c : A)
    (hX : (X : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c) : modM X = 1 := by
  have h := hT A k i j hij c (addHaar : Measure (Fin k → A)) inferInstance
  have e : (phi X : (Fin k → A) → (Fin k → A)) = Matrix.mulVec (Matrix.transvection i j c) := by
    funext v
    rw [phi_apply, hX]
  apply modM_of_map X (addHaar : Measure (Fin k → A))
  rw [e]
  exact h
end PI.VolSemiDirect.W.Cj
