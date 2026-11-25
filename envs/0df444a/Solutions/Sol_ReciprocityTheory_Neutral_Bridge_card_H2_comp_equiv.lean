-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.card_H2_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:38:10.671933+00:00
-- url     : https://prove2.me/submissions/e9a93d00-db4e-4cb7-ab89-e8435398676b

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
    Nat.card (H2 (rho.comp (e : G →* G'))) = Nat.card (H2 rho) := by
  let φ1 : (G' → M) ≃ₗ[R] (G → M) := LinearEquiv.funCongrLeft R M e.toMulEquiv.toEquiv
  let φ : (G' × G' → M) ≃ₗ[R] (G × G → M) :=
    LinearEquiv.funCongrLeft R M (e.toMulEquiv.toEquiv.prodCongr e.toMulEquiv.toEquiv)
  have hZ : (Z2 rho).map φ.toLinearMap = Z2 (rho.comp (e : G →* G')) := by
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, ⟨hyc, hy⟩, rfl⟩
      refine ⟨hyc.comp ((map_continuous e).prodMap (map_continuous e)), fun g h k => ?_⟩
      show rho (e g) (y (e h, e k)) - y (e (g * h), e k) + y (e g, e (h * k)) - y (e g, e h) = 0
      rw [map_mul, map_mul]
      exact hy (e g) (e h) (e k)
    · rintro ⟨hfc, hf⟩
      refine ⟨fun q => f (e.symm q.1, e.symm q.2),
        ⟨hfc.comp (((map_continuous e.symm).comp continuous_fst).prodMk
          ((map_continuous e.symm).comp continuous_snd)), fun g h k => ?_⟩, ?_⟩
      · have h2 := hf (e.symm g) (e.symm h) (e.symm k)
        simp only [map_mul]
        simpa [MonoidHom.comp_apply] using h2
      · funext q
        show f (e.symm (e q.1), e.symm (e q.2)) = f q
        simp
  have hC : (contMaps R M G').map φ1.toLinearMap = contMaps R M G := by
    ext f
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (show Continuous y from hy).comp (map_continuous e)
    · intro hf
      refine ⟨f ∘ e.symm, (show Continuous f from hf).comp (map_continuous e.symm), ?_⟩
      funext g
      show f (e.symm (e g)) = f g
      simp
  have hcomm : φ.toLinearMap ∘ₗ d1 rho = d1 (rho.comp (e : G →* G')) ∘ₗ φ1.toLinearMap := by
    refine LinearMap.ext fun c => funext fun p => ?_
    show rho (e p.1) (c (e p.2)) - c (e p.1 * e p.2) + c (e p.1) =
      rho (e p.1) (c (e p.2)) - c (e (p.1 * p.2)) + c (e p.1)
    rw [map_mul]
  have hB : (B2 rho).map φ.toLinearMap = B2 (rho.comp (e : G →* G')) := by
    unfold B2
    rw [← Submodule.map_comp, hcomm, Submodule.map_comp, hC]
  let fZ : Z2 rho ≃ₗ[R] Z2 (rho.comp (e : G →* G')) :=
    (φ.submoduleMap (Z2 rho)).trans (LinearEquiv.ofEq _ _ hZ)
  unfold H2
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
    have h3 : ((fZ.symm w : Z2 rho) : G' × G' → M) = y := by
      apply φ.injective
      rw [show φ y = (w : G × G → M) from hyw]
      exact congrArg Subtype.val (fZ.apply_symm_apply w)
    rw [h3]
    exact hy
end ReciprocityTheory.Neutral.Bridge
