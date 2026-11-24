-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_homMap_monomial_be73811eb40e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:49.740474+00:00
-- url     : https://prove2.me/submissions/d9dbe91d-94d4-424c-aa0b-e82ddc39b08a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (mConeMap mCoordIdeal mcPts)
noncomputable section
variable (K : Type) [Field K] (r : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (s : Fin (r + 1) →₀ ℕ) (c : K) :
    homMap K r (monomial s c) = monomial (homExp r s) c := by
  rw [← single_eq_monomial, ← single_eq_monomial]
  exact AddMonoidAlgebra.mapDomain_single
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
