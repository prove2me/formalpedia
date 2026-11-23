-- Prove2me | solution 1 for PI.VolStabW.FiniteFieldSplitting.linInd_cols_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:31.362948+00:00
-- url     : https://prove2.me/submissions/6437d0b4-6b18-4e2b-b76c-a9ddc1a62fcc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensFFS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.FiniteFieldSplitting
open Matrix
variable {k : Type} [Field k] [Finite k]
namespace PI.VolStabW.FiniteFieldSplitting
theorem _root_.solution {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have h : ∀ v : Fin a → k, ∑ j, v j • cols P j = P *ᵥ v := by
    intro v
    ext i
    simp [cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  simp_rw [h]
  constructor
  · intro H v hv
    funext j
    exact H v hv j
  · intro H v hv j
    rw [H v hv]
    rfl
end PI.VolStabW.FiniteFieldSplitting
