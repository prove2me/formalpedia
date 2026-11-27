-- Prove2me | solution 1 for UpperTheory.V.Alg.act_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:02.297171+00:00
-- url     : https://prove2.me/submissions/4730733d-b33c-4f22-89a3-f60d32b1d446

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open UpperTheory UpperTheory.V UpperTheory.V.Alg
attribute [instance] IsCO.complete IsCO.isLocalHom
attribute [instance] WPres.fin
variable {O A X K : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup X] [DecidableEq X]
  (𝒜 : X → Submodule O A) [GradedAlgebra 𝒜] [CommRing K] [Algebra O K]
namespace UpperTheory.V.Alg
theorem _root_.solution (t : Multiplicative X →* Kˣ) (ξ : A →ₐ[O] K) {j : X} {f : A} (hf : f ∈ 𝒜 j) :
    act 𝒜 t ξ f = t (Multiplicative.ofAdd j) * ξ f := by
  have h : DirectSum.decompose 𝒜 f = DirectSum.of (fun j => 𝒜 j) j ⟨f, hf⟩ := DirectSum.decompose_of_mem 𝒜 hf
  simp [act, h, DirectSum.toAlgebra]
  erw [DirectSum.toSemiring_of]
  rfl
end UpperTheory.V.Alg
