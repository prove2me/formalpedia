-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_ker_flagMinorMap_eq_bff51324077a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:09:46.652722+00:00
-- url     : https://prove2.me/submissions/b0302427-4717-4514-875d-2bf6a1290ce5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_toUpper_flagMinorMap_X_200458d87616
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_fromUpper_flagMinor_1e63f757d0b6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution :
    RingHom.ker (flagMinorMap F n) = RingHom.ker ((toUpper F n).comp (flagMinorMap F n)) := by
  ext f
  simp only [RingHom.mem_ker]
  constructor
  · intro h
    rw [AlgHom.comp_apply, h, map_zero]
  · intro h
    have key : (fromUpper F n).comp ((toUpper F n).comp (flagMinorMap F n)) =
        (IsScalarTower.toAlgHom F (MvPolynomial (Fin n × Fin n) F) (GenField F n)).comp
          (flagMinorMap F n) := by
      apply MvPolynomial.algHom_ext
      intro q
      rw [AlgHom.comp_apply, toUpper_flagMinorMap_X, fromUpper_flagMinor, AlgHom.comp_apply,
        flagMinorMap, aeval_X]
      rfl
    have h2 := congrArg (fun g : MRingOver F (PluckerBlocks n n) →ₐ[F] GenField F n => g f) key
    simp only [AlgHom.comp_apply] at h2 h
    rw [h, map_zero, IsScalarTower.coe_toAlgHom'] at h2
    exact IsFractionRing.injective (MvPolynomial (Fin n × Fin n) F) (GenField F n)
      (h2.symm.trans (map_zero _).symm)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
