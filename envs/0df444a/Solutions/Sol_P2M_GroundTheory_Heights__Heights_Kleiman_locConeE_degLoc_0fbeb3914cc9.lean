-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_degLoc_0fbeb3914cc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:02.694615+00:00
-- url     : https://prove2.me/submissions/3218c315-388f-4bbf-9483-dcf64c0edc88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_eq_3d2fa305b23b
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
theorem _root_.solution (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSubE I.1}
    (hz : z ∈ degLoc M.coneGradedE c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locConeE M I.1 hI z = singleE S x E c v := by
  refine Submodule.span_induction (p := fun z _ => ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩,
    locConeE M I.1 hI z = singleE S x E c v) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, s, a, e, hm, hse, hae, rfl⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI s.2
    refine ⟨(aeval x (s : Poly S N))⁻¹ • coeffE S x E a (m : ConeE S x E),
      Submodule.subset_span ⟨coeffE S x E a m, s, a, e, s.2, hse, m.2 a, hae, rfl⟩, locConeE_mk_eq M hI ?_⟩
    rw [smul_singleE hse, smul_smul, mul_inv_cancel₀ hs0, one_smul, show c + (e : ℤ) = a by omega]
    exact (M.eq_singleE_of_mem_conePieceE hm).symm
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨v, hv, hzv⟩ ⟨v', hv', hzv'⟩
    exact ⟨v + v', add_mem hv hv', by rw [map_add, map_add, hzv, hzv']⟩
  · rintro s _ _ ⟨v, hv, hzv⟩
    refine ⟨s • v, ?_, by rw [LinearMap.map_smul_of_tower, hzv, map_smul]⟩
    rw [← algebraMap_smul Ω s v]
    exact (M.tilde c _).smul_mem (algebraMap S (chartRing S x ⟨I.1, I.2.1, hI⟩) s) hv
end GroundTheory.Heights₂.Heights.Kleiman
