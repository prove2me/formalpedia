-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.QRG.H_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:39.524482+00:00
-- url     : https://prove2.me/submissions/911ff6f6-9fdf-4388-8abf-92f2b481317d

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.QRG
open Matrix Formalism.UG
variable {K : Type} [Field K] {n : ℕ}
variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG
theorem _root_.solution (g : GL (Fin n) K) (hg : g ∈ UJ σ J) (x y : Fin n → K) :
    H σ J ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) = H σ J x y := by
  have hg' : cT σ (g : Matrix (Fin n) (Fin n) K) * J * (g : Matrix (Fin n) (Fin n) K) = J := hg
  rw [H_mulVec, hg']
end PI.UnitaryGroupMassFormula.AdIndexEq.QRG
