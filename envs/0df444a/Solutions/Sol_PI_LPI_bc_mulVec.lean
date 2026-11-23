-- Prove2me | solution 1 for PI.LPI.bc_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:19.999986+00:00
-- url     : https://prove2.me/submissions/78c3e1fc-f71d-48fe-8b43-82190d01d48c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LevelProdIdx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.LPI
open Formalism.UG
namespace PI.LPI
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B)
    (g : GL (Fin n) A) (y : Fin n → A) :
    (fun j => φ (((g : Matrix (Fin n) (Fin n) A) *ᵥ y) j)) =
      ((bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) *ᵥ (fun j => φ (y j)) := by
  unfold bc
  funext j
  rw [RingHom.map_mulVec]
  rfl
end PI.LPI
