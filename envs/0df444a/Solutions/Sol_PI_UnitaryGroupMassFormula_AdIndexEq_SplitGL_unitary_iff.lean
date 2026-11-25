-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.unitary_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:47:16.669792+00:00
-- url     : https://prove2.me/submissions/c96c402e-8631-433d-8320-5f73e7b4c8ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_mat_ext_p
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_map_conjTranspose_fst
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_map_conjTranspose_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
open Matrix
variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
variable (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap)
include hπ
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
theorem _root_.solution (J M : Matrix n n R) :
    Formalism.UG.cT σ M * J * M = J ↔
      (M.map (p2 π))ᵀ * J.map (p1 π) * M.map (p1 π) = J.map (p1 π) ∧
      (M.map (p1 π))ᵀ * J.map (p2 π) * M.map (p2 π) = J.map (p2 π) := by
  have e1 : (Formalism.UG.cT σ M * J * M).map (p1 π) = (M.map (p2 π))ᵀ * J.map (p1 π) * M.map (p1 π) := by
    rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_fst σ π hπ]
  have e2 : (Formalism.UG.cT σ M * J * M).map (p2 π) = (M.map (p1 π))ᵀ * J.map (p2 π) * M.map (p2 π) := by
    rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_snd σ π hπ]
  constructor
  · intro h
    rw [← e1, ← e2, h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact mat_ext_p π (by rw [e1, h1]) (by rw [e2, h2])
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
