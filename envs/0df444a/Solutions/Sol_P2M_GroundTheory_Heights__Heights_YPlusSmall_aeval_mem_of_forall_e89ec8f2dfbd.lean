-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_YPlusSmall_aeval_mem_of_forall_e89ec8f2dfbd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:08.992098+00:00
-- url     : https://prove2.me/submissions/47e9dbdd-cd0e-4cda-9a4f-46218298ae88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PYPlusSmall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.YPlusSmall
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.YPlusSmall
theorem _root_.solution {σ : Type*} {Ω : Type*} [CommRing Ω] (S : Subalgebra ℤ Ω) (w : σ → Ω)
    (hw : ∀ p, w p ∈ S) (F : MvPolynomial σ ℤ) : aeval w F ∈ S := by
  have := congrArg (fun φ : MvPolynomial σ ℤ →ₐ[ℤ] Ω ↦ φ F)
    (MvPolynomial.comp_aeval (R := ℤ) (f := fun p ↦ (⟨w p, hw p⟩ : S)) S.val)
  simp only [AlgHom.comp_apply, Subalgebra.coe_val] at this
  rw [← this]
  exact SetLike.coe_mem _
end GroundTheory.Heights₂.Heights.YPlusSmall
