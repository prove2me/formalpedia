-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_rename_inlV_2f22a6c9fac6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:18.635307+00:00
-- url     : https://prove2.me/submissions/1a030ed7-48e7-4f1e-ada0-0de3cbff5726

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleDim

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (g : MRing ι) :
    projBundleMap P B (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) g) =
      C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P g)) := by
  have key : (projBundleMap P B).comp
      (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom =
      (C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
        ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · have hC := RingHom.ext_int
        (((projBundleMap P B).comp
          (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom).comp C)
        (((C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
          ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P))).comp C)
      exact RingHom.congr_fun hC r
    · obtain ⟨k, i⟩ := p
      simp [projBundleMap, inlV, genPt]
  exact RingHom.congr_fun key g
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
