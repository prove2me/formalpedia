-- Prove2me | solution 1 for PI.SymDistWork.kset_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:02.20509+00:00
-- url     : https://prove2.me/submissions/bc5c9803-2152-46b8-9795-40e13745aa1e

import Definitions.Def_Formalism_PeriodIntegrals_SymDist
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.SymDistWork
open Formalism.REAL
variable {n : ℕ}
namespace PI.SymDistWork
theorem _root_.solution {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  have hJ : (Jm ε)ᴴ = Jm ε := by
    unfold Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases hεa : ε a = true <;> simp [hεa]
  have h2 := congrArg Matrix.conjTranspose hk.2
  simp only [Matrix.conjTranspose_mul, hJ] at h2
  exact ⟨Unitary.star_mem hk.1, h2.symm⟩
end PI.SymDistWork
