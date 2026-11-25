-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_isSubvar_comap_a7c2d693c28e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:23:25.31402+00:00
-- url     : https://prove2.me/submissions/c7478e54-666d-4c01-8eb7-222554974f5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefExtendIsoSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefExtendIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_homogeneousComponent_36e904623d63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_NefExtendIso_map_pre_2d52bc105c55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cone_eq_619a623144ca


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
variable {S : Type} [CommRing S] {F : Type} [Field F] [Algebra S F] {Ω : Type} [Field Ω] [Algebra S Ω]
  [Algebra F Ω] [IsScalarTower S F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
theorem _root_.solution (hφ : Function.Bijective (algebraMap S F)) {p' : Ideal (Kleiman.Poly F N)} {e : ℕ}
    (hp' : Kleiman.IsSubvar x p' e) : Kleiman.IsSubvar x (p'.comap (map (algebraMap S F))) e where
  isPrime := by have := hp'.isPrime; exact Ideal.comap_isPrime _ _
  homog f hf d := by
    rw [Ideal.mem_comap, map_homogeneousComponent]
    exact hp'.homog _ hf d
  le f hf := by
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen] at hf
    apply hp'.le
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen, aeval_map_algebraMap]
    exact hf
  relevant := by
    obtain ⟨i, hi⟩ := hp'.relevant
    exact ⟨i, fun h => hi (by rwa [Ideal.mem_comap, map_X] at h)⟩
  dim := by
    let e' : Kleiman.Poly S N ≃+* Kleiman.Poly F N := mapEquiv _ (RingEquiv.ofBijective _ hφ)
    have he : (e' : Kleiman.Poly S N →+* Kleiman.Poly F N) = map (algebraMap S F) := RingHom.ext fun _ => rfl
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ p' e' ?_)).trans hp'.dim
    rw [he, Ideal.map_comap_of_surjective _ (fun f => ⟨_, map_pre hφ f⟩)]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.NefExtendIso
