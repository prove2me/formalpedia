-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_toH0_surjective_of_exact_384eb577a921
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:15.41322+00:00
-- url     : https://prove2.me/submissions/feff6626-e980-4d01-b136-37ca7540a367

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_toH0_db774a862a06

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w w'
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hC : CechExact.Statement.{u, w}) {S : Type u} [CommRing S]
    [IsNoetherianRing S] {N : ℕ} {K F M : Type w}
    [AddCommGroup K] [Module (Poly S N) K] [Module S K] [IsScalarTower S (Poly S N) K]
    [AddCommGroup F] [Module (Poly S N) F] [Module S F] [IsScalarTower S (Poly S N) F]
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    {𝓚 : GradedPMod S N K} {𝓕 : GradedPMod S N F} {𝓜 : GradedPMod S N M}
    (ι : GradedHom 𝓚 𝓕) (φ : GradedHom 𝓕 𝓜) (hι : Function.Injective ι.toLin)
    (hφ : Function.Surjective φ.toLin) (hex : Function.Exact ι.toLin φ.toLin) (c : ℤ)
    (hF : Function.Surjective (toH0 𝓕 c)) (hK : Subsingleton (cohom 𝓚 1 c)) :
    Function.Surjective (toH0 𝓜 c) := by
  obtain ⟨-, h⟩ := hC S N K F M 𝓚 𝓕 𝓜 ι φ hι hφ hex c
  obtain ⟨-, δ, hδ, -⟩ := h 0
  intro y
  obtain ⟨z, hz⟩ := (hδ y).mp (Subsingleton.elim _ _)
  obtain ⟨f, rfl⟩ := hF z
  exact ⟨⟨φ.toLin f, φ.map_piece c f f.2⟩, by rw [← cohomMap_toH0, hz]⟩
end GroundTheory.Heights₂.Heights.Kleiman
