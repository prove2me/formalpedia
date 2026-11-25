-- Prove2me | solution 1 for PI.SymDistWork.symD_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:05.152906+00:00
-- url     : https://prove2.me/submissions/b701a077-b1d9-4cc1-b936-038bf0cb6d0b

import Definitions.Def_Formalism_PeriodIntegrals_SymDist
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Theorems.Thm_Formalism_REAL_polar_decomposition_unique


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
theorem _root_.solution {ε : Fin n → Bool} (g : UJ ε) {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hX : inP ε X)
    (hg : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X) :
    PI.symD ε g = Real.sqrt (hs X) := by
  unfold PI.symD
  have hset : {t | ∃ k' X' : Matrix (Fin n) (Fin n) ℂ, k' ∈ Kset ε ∧ inP ε X' ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k' * NormedSpace.exp X' ∧
      t = Real.sqrt (hs X')} = {Real.sqrt (hs X)} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k', X', hk', hX', hg', rfl⟩
      have := polar_decomposition_unique k' k X' X hk' hk hX' hX (hg'.symm.trans hg)
      rw [this.2]
    · rintro rfl
      exact ⟨k, X, hk, hX, hg, rfl⟩
  rw [hset]
  exact csInf_singleton _
end PI.SymDistWork
