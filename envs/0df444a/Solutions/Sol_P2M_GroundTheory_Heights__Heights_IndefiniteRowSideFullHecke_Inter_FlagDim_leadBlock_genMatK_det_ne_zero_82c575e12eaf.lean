-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_leadBlock_genMatK_det_ne_zero_82c575e12eaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:33.316261+00:00
-- url     : https://prove2.me/submissions/feb4b327-e518-43e1-b89a-2bf22df012bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim

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
theorem _root_.solution (i : Fin n) : (leadBlock (genMatK F n) i).det ≠ 0 := by
  have e : leadBlock (genMatK F n) i =
      (leadBlock (genMat F n) i).map (algebraMap _ (GenField F n)) := rfl
  rw [e]
  change ((algebraMap _ (GenField F n)).mapMatrix (leadBlock (genMat F n) i)).det ≠ 0
  rw [← RingHom.map_det]
  intro h
  have h2 := IsFractionRing.injective (MvPolynomial (Fin n × Fin n) F) (GenField F n)
    (h.trans (map_zero _).symm)
  have h3 := congrArg (MvPolynomial.eval fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0) h2
  rw [RingHom.map_det, map_zero] at h3
  have e2 : (MvPolynomial.eval fun p : Fin n × Fin n => if p.1 = p.2 then (1 : F) else 0).mapMatrix
      (leadBlock (genMat F n) i) = 1 := by
    ext a b
    simp [leadBlock, genMat, Matrix.one_apply, Fin.ext_iff]
  rw [e2, Matrix.det_one] at h3
  exact one_ne_zero h3
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
