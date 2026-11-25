-- Prove2me | solution 1 for P2M_GlobalTheory_CayleyUnitary_cT_add__d8bc2b81d278
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:51.760056+00:00
-- url     : https://prove2.me/submissions/b3ffa4df-7541-4abf-af1c-1f4be94a6ce3

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CayleyTransformSkewMemUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.CayleyUnitary
open Formalism.UG
namespace GlobalTheory.CayleyUnitary
theorem _root_.solution {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A + B) = cT σ A + cT σ B := by
  unfold cT; rw [Matrix.map_add _ (map_add σ), Matrix.transpose_add]
end GlobalTheory.CayleyUnitary
