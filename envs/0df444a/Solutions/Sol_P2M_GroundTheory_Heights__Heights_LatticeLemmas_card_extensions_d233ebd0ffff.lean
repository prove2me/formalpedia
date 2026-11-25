-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_extensions_d233ebd0ffff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:32.990855+00:00
-- url     : https://prove2.me/submissions/1eb52601-f8cd-4838-a7cf-17cdd50b25c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_BaseChangeIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField TensorProduct
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
theorem _root_.solution (σ : K →+* ℂ) :
    Nat.card {τ : L →+* ℂ // τ.comp (algebraMap K L) = σ} = Module.finrank K L := by
  let _ : Algebra K ℂ := σ.toAlgebra
  rw [← AlgHom.natCard_of_splits K L ℂ (fun _ ↦ IsAlgClosed.splits _)]
  exact Nat.card_congr
    { toFun := fun τ ↦ (⟨τ.1, fun a ↦ RingHom.congr_fun τ.2 a⟩ : L →ₐ[K] ℂ)
      invFun := fun g ↦ ⟨g.toRingHom, by
        ext a
        exact g.commutes a⟩
      left_inv := fun τ ↦ rfl
      right_inv := fun g ↦ rfl }
end GroundTheory.Heights₂.Heights.LatticeLemmas
