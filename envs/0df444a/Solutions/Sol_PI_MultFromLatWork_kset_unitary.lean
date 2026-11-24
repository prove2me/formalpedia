-- Prove2me | solution 1 for PI.MultFromLatWork.kset_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:16:33.832541+00:00
-- url     : https://prove2.me/submissions/65e44aa5-1a68-4a72-9b5a-b9d30872f06a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatCountG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Matrix
open scoped ENNReal
noncomputable section
open PI PI.MultFromLatWork
open Formalism.REAL
namespace PI.MultFromLatWork
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ * k = 1 ∧ k * kᴴ = 1 := by
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  exact ⟨by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk'.1,
    by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk'.1⟩
end PI.MultFromLatWork
