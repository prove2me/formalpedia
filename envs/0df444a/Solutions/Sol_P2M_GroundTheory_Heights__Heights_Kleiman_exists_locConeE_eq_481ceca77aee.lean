-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_locConeE_eq_481ceca77aee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:58:57.438688+00:00
-- url     : https://prove2.me/submissions/317fadd4-b7f0-4340-90e1-4e9c8058f586

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_eq_3d2fa305b23b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_tildeE_le_span_afc358cb0b1e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_singleE_6f24e5511d10


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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {y : E}
    (hy : y ∈ M.tilde c ⟨I.1, I.2.1, hI⟩) :
    ∃ z ∈ degLoc M.coneGradedE c I, locConeE M I.1 hI z = singleE S x E c y := by
  refine Submodule.span_induction (p := fun y _ => ∃ z ∈ degLoc M.coneGradedE c I,
    locConeE M I.1 hI z = singleE S x E c y) ?_ ?_ ?_ ?_ (tildeE_le_span M c _ hy)
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    refine ⟨LocalizedModule.mk ⟨singleE S x E a m, M.singleE_mem_coneSubE hm⟩ ⟨s, hs⟩,
      Submodule.subset_span ⟨_, ⟨s, hs⟩, a, e, M.singleE_mem_conePieceE hm, hse, hae, rfl⟩,
      locConeE_mk_eq M hI ?_⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI hs
    change s • singleE S x E c ((aeval x s)⁻¹ • m) = singleE S x E a m
    rw [smul_singleE hse, smul_smul, mul_inv_cancel₀ hs0, one_smul, show c + (e : ℤ) = a by omega]
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨z, hz, hzy⟩ ⟨z', hz', hzy'⟩
    exact ⟨z + z', add_mem hz hz', by rw [map_add, map_add, hzy, hzy']⟩
  · rintro t _ _ ⟨z, hz, hzy⟩
    exact ⟨t • z, Submodule.smul_mem _ t hz, by rw [LinearMap.map_smul_of_tower, hzy, map_smul]⟩
end GroundTheory.Heights₂.Heights.Kleiman
