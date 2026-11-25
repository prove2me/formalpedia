-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_graph_equiv_e1c5601114d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:32.83206+00:00
-- url     : https://prove2.me/submissions/6c62987b-e270-4847-bc0e-271a2f3e14b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.CechDouble
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair
attribute [instance] DblData.gD DblData.mD DblData.gA DblData.mA DblData.gC DblData.mC
variable {R : Type u} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair
theorem _root_.solution {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (dM : M →ₗ[R] M') (dN : N →ₗ[R] N') (BM : Submodule R M) (BN : Submodule R N)
    (G : Submodule R (M × N))
    (hZ : ∀ x y, (x, y) ∈ G → dM x = 0 ∧ dN y = 0)
    (hM : ∀ x, dM x = 0 → ∃ y, (x, y) ∈ G)
    (hN : ∀ y, dN y = 0 → ∃ x, (x, y) ∈ G)
    (hBM : ∀ x ∈ BM, (x, (0 : N)) ∈ G) (hBN : ∀ y ∈ BN, ((0 : M), y) ∈ G)
    (hKM : ∀ x, (x, (0 : N)) ∈ G → x ∈ BM) (hKN : ∀ y, ((0 : M), y) ∈ G → y ∈ BN) :
    Nonempty ((LinearMap.ker dM ⧸ BM.comap (LinearMap.ker dM).subtype) ≃ₗ[R]
      (LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype)) := by
  classical
  choose f hf using fun x : LinearMap.ker dM => hM x.1 (LinearMap.mem_ker.mp x.2)
  have hfz : ∀ x, f x ∈ LinearMap.ker dN := fun x => LinearMap.mem_ker.mpr (hZ _ _ (hf x)).2
  let g : LinearMap.ker dM → LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype :=
    fun x => Submodule.Quotient.mk ⟨f x, hfz x⟩
  have key : ∀ (x : LinearMap.ker dM) (y : LinearMap.ker dN), ((x : M), (y : N)) ∈ G →
      g x = Submodule.Quotient.mk y := by
    intro x y hxy
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [Submodule.mem_comap]
    apply hKN
    have := G.sub_mem (hf x) hxy
    rw [Prod.mk_sub_mk, sub_self] at this
    exact this
  let F : LinearMap.ker dM →ₗ[R] LinearMap.ker dN ⧸ BN.comap (LinearMap.ker dN).subtype :=
    { toFun := g
      map_add' := fun x₁ x₂ => by
        rw [key (x₁ + x₂) (⟨f x₁, hfz x₁⟩ + ⟨f x₂, hfz x₂⟩) (G.add_mem (hf x₁) (hf x₂))]
        rfl
      map_smul' := fun r x => by
        rw [key (r • x) (r • ⟨f x, hfz x⟩) (G.smul_mem r (hf x))]
        rfl }
  have hQ : BM.comap (LinearMap.ker dM).subtype ≤ LinearMap.ker F := by
    intro x hx
    rw [LinearMap.mem_ker]
    change g x = 0
    rw [key x 0 (hBM x.1 hx)]
    rfl
  let Φ := (BM.comap (LinearMap.ker dM).subtype).liftQ F hQ
  have inj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker] at hq
    change g x = 0 at hq
    have hq' : f x ∈ BN := by
      have := (Submodule.Quotient.mk_eq_zero _).mp hq
      exact this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    apply hKM
    have := G.sub_mem (hf x) (hBN _ hq')
    rw [Prod.mk_sub_mk, sub_zero, sub_self] at this
    exact this
  have surj : Function.Surjective Φ := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, hx⟩ := hN y.1 (LinearMap.mem_ker.mp y.2)
    refine ⟨Submodule.Quotient.mk ⟨x, LinearMap.mem_ker.mpr (hZ _ _ hx).1⟩, ?_⟩
    exact key _ y hx
  exact ⟨LinearEquiv.ofBijective Φ ⟨inj, surj⟩⟩
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble.Stair
