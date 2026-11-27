-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_proof_9be93552920a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:05:46.775372+00:00
-- url     : https://prove2.me/submissions/7250958d-4c93-4b9a-88c9-deb1c3030af0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinPointIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinPointIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_cone_comp_9222df78dfc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointIdeal_rename_liftVar_eq_fac4b3379de2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar joinCoord mcIdeal mcMap)
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace JoinPointIdeal
theorem _root_.solution : JoinPointIdeal.Statement := by
  intro R _ Ω _ _ K _ ι _ y
  set φ : MRing ι R →+* MvPolynomial K Ω :=
    ((pointConeMap R y : MRing ι R →ₐ[R] MvPolynomial K Ω) : MRing ι R →+* MvPolynomial K Ω) with hφ
  have h1 : mcIdeal R (joinCoord y (ptCoord (Ω := Ω))) =
      Ideal.comap (JoinPointIdeal.srcEquiv (ι := ι) R :
          MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) R →+* MvPolynomial Unit (MRing ι R))
        (RingHom.ker (MvPolynomial.map (σ := Unit) φ)) := by
    ext f
    have hc := RingHom.congr_fun (JoinPointIdeal.cone_comp R Ω y) f
    simp only [RingHom.comp_apply] at hc
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hc]
    simp only [RingHom.coe_coe, EmbeddingLike.map_eq_zero_iff]
    exact RingHom.mem_ker
  rw [h1, pointIdeal, show RingHom.ker (pointConeMap R y) = RingHom.ker φ from rfl, ← Ideal.map_coe, JoinPointIdeal.rename_liftVar_eq, ← Ideal.map_map, Ideal.map_coe, Ideal.map_symm, ← MvPolynomial.ker_map]
  rfl
end JoinPointIdeal
end GroundTheory.Heights₂.Heights.NumbersDVR
