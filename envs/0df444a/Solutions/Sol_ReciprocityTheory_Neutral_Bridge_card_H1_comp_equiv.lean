-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.card_H1_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:26:09.373978+00:00
-- url     : https://prove2.me/submissions/58741fc1-38a7-4b9b-a1be-6547773379bd

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_Transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H1 (rho.comp (e : G →* G'))) = Nat.card (H1 rho) := by
  let φ : (G' → M) ≃ₗ[R] (G → M) := LinearEquiv.funCongrLeft R M e.toMulEquiv.toEquiv
  have hd : ∀ m, d0 (rho.comp (e : G →* G')) m = φ (d0 rho m) := fun m => rfl
  have hZ : (Z1 rho).map φ.toLinearMap = Z1 (rho.comp (e : G →* G')) := by
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, ⟨hyc, hy⟩, rfl⟩
      refine ⟨hyc.comp (map_continuous e), fun g h => ?_⟩
      show y (e (g * h)) = y (e g) + rho (e g) (y (e h))
      rw [map_mul]
      exact hy (e g) (e h)
    · rintro ⟨hfc, hf⟩
      refine ⟨f ∘ e.symm, ⟨hfc.comp (map_continuous e.symm), fun g h => ?_⟩, ?_⟩
      · have h2 := hf (e.symm g) (e.symm h)
        simp only [Function.comp_apply, map_mul]
        simpa [MonoidHom.comp_apply] using h2
      · funext g
        show f (e.symm (e g)) = f g
        simp
  have hB : (B1 rho).map φ.toLinearMap = B1 (rho.comp (e : G →* G')) := by
    unfold B1
    rw [← LinearMap.range_comp]
    congr 1
  let fZ : Z1 rho ≃ₗ[R] Z1 (rho.comp (e : G →* G')) :=
    (φ.submoduleMap (Z1 rho)).trans (LinearEquiv.ofEq _ _ hZ)
  unfold H1
  refine (Nat.card_congr (Submodule.Quotient.equiv _ _ fZ ?_).toEquiv).symm
  ext w
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hB]
    exact ⟨z, hz, rfl⟩
  · intro hw
    rw [← hB] at hw
    obtain ⟨y, hy, hyw⟩ := hw
    refine ⟨fZ.symm w, ?_, fZ.apply_symm_apply w⟩
    have h3 : ((fZ.symm w : Z1 rho) : G' → M) = y := by
      apply φ.injective
      rw [show φ y = (w : G → M) from hyw]
      exact congrArg Subtype.val (fZ.apply_symm_apply w)
    rw [h3]
    exact hy
end ReciprocityTheory.Neutral.Bridge
