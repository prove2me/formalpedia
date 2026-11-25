-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_aeval_flagMap_X_2c846709d619
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:59:56.301219+00:00
-- url     : https://prove2.me/submissions/298db584-c3a3-488e-92a4-9bb5d18e8701

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTrdegAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagConeTrdeg

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    ((aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) :
      MRing (FlagBundleBlocks ι N1 n) →+* MvPolynomial (Fin n × Fin n) (FnField P)) = flagMap P B :=
  MvPolynomial.ringHom_ext (fun r => by
    rw [← RingHom.comp_apply _ C r, ← RingHom.comp_apply _ C r, eq_intCast, eq_intCast]) fun q => by
    simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
