-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_map_conjTranspose__e871e98cff26
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:18.460797+00:00
-- url     : https://prove2.me/submissions/3f4054a1-9a3b-4c52-bb39-5a8f60ab1abb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
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
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {n d : ℕ}
    (E : Matrix (Fin n) (Fin d) K) (hE : ∀ i a, σ (star (E i a)) = starRingEnd ℂ (σ (E i a))) :
    (Eᴴ).map σ = (E.map σ)ᴴ := by
  ext a i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply]
  rw [hE i a]
  rfl
end Formalism.L2.DIV
