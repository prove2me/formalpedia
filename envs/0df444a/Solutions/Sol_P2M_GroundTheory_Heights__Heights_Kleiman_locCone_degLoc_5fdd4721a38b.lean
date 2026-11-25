-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locCone_degLoc_5fdd4721a38b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:20:39.986078+00:00
-- url     : https://prove2.me/submissions/f6a8b46b-7cc9-45ac-84b7-08f256be9e15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_mk_eq_99b34d9786d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneLaurent_smul_a6c484f2d236
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_smul_coneSingle_4b1ab4277a3e


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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (I : StdCell N) (hI : I.1 ⊆ support x) {z : LocMod S N M.coneSub I.1}
    (hz : z ∈ degLoc M.coneGraded c I) :
    ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩, locCone M I.1 hI z = coneSingle S x c v := by
  refine Submodule.span_induction (p := fun z _ => ∃ v ∈ M.tilde c ⟨I.1, I.2.1, hI⟩,
    locCone M I.1 hI z = coneSingle S x c v) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, s, a, e, hm, hse, hae, rfl⟩
    have hs0 := aeval_ne_zero_of_mem_monos_support hI s.2
    refine ⟨(aeval x (s : Poly S N))⁻¹ • coeffAt S x a (m : ConeLaurent S x),
      Submodule.subset_span ⟨coeffAt S x a m, s, a, e, s.2, hse, m.2 a, hae, rfl⟩, locCone_mk_eq M hI ?_⟩
    rw [← coneLaurent_smul, smul_coneSingle hse, smul_eq_mul, mul_inv_cancel_left₀ hs0,
      show c + (e : ℤ) = a by omega]
    exact (M.eq_coneSingle_of_mem_conePiece hm).symm
  · exact ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro _ _ _ _ ⟨v, hv, hzv⟩ ⟨v', hv', hzv'⟩
    exact ⟨v + v', add_mem hv hv', by rw [map_add, map_add, hzv, hzv']⟩
  · rintro s _ _ ⟨v, hv, hzv⟩
    exact ⟨s • v, (M.tilde c _).smul_of_tower_mem s hv, by rw [LinearMap.map_smul_of_tower, hzv, map_smul]⟩
end GroundTheory.Heights₂.Heights.Kleiman
