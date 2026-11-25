-- Prove2me | solution 1 for P2M_GlobalTheory_ConeImage_map_eval___93a91e452ef8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:44.992042+00:00
-- url     : https://prove2.me/submissions/b3bb19bc-6fb6-4033-a260-47fb5afa5d53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
import Theorems.Thm_P2M_GlobalTheory_ConeImage_map_eval__3b0ac179800a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage
namespace GlobalTheory.ConeImage
theorem _root_.solution {σ A : Type*} [CommRing A] [Algebra ℂ A] (j : MvPolynomial σ ℂ →ₐ[ℂ] A)
    (φ : A →ₐ[ℂ] ℂ) (a : A) (r : Polynomial (MvPolynomial σ ℂ)) :
    φ (r.eval₂ j.toRingHom a) =
      r.eval₂ (MvPolynomial.eval (fun i => φ (j (MvPolynomial.X i)))) (φ a) := by
  have := Polynomial.hom_eval₂ r j.toRingHom (φ : A →+* ℂ) a
  rw [show φ (r.eval₂ j.toRingHom a) = _ from this]
  congr 1
  exact RingHom.ext fun x => map_eval₂ j φ x
end GlobalTheory.ConeImage
