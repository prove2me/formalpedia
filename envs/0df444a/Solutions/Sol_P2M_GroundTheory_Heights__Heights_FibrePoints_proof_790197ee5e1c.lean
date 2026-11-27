-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibrePoints_proof_790197ee5e1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:54.135011+00:00
-- url     : https://prove2.me/submissions/6bb4f5f3-2df9-48fd-963a-fe7fdebc7011

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsArithVarOfRingKrullDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_isArithVar_of_ringKrullDim_af9eacdfcf1b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
namespace GroundTheory.Heights₂.Heights
namespace FibrePoints
theorem _root_.solution (hG : GeometricArithmeticNumbers.Statement) : FibrePoints.Statement := by
  intro hDeg ι _ _ _ n P D hdim L hL
  have hP : Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) := P.isArithVar_of_ringKrullDim hdim
  have hfin := Geo.divSupp_finite (ι := blockIdx n) P.ideal (C ((2 : ℕ) : ℤ))
  rw [hDeg ι (blockIdx n) P.ideal D L 2 hP hL Nat.prime_two,
    hG ι n P D hdim (fun j ↦ (L j).a) 2]
  have hcast := (Int.castAddHom ℝ).map_finsum_mem
    (fun V ↦ (Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C ((2 : ℕ) : ℤ)}) V : ℤ) *
      Geo.geoNum (ι := blockIdx n) D V (fun j ↦ (L j).a)) hfin
  simp only [Int.coe_castAddHom, Int.cast_mul, Int.cast_natCast] at hcast
  exact hcast.symm
end FibrePoints
end GroundTheory.Heights₂.Heights
