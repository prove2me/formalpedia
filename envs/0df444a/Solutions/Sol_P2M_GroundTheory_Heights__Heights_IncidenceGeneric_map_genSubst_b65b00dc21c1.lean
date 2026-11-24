-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_map_genSubst_b65b00dc21c1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:50:59.418179+00:00
-- url     : https://prove2.me/submissions/76917f53-eb31-4182-83fb-4f9c92d5050f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceGeneric
namespace GroundTheory.Heights₂.Heights.IncidenceGeneric
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n k : ℕ}
    (ζ c : Fin n → R) (ij : Fin k × Fin n) :
    map φ (genSubst ζ c ij) = genSubst (fun l => φ (ζ l)) (fun l => φ (c l)) ij := by
  simp [genSubst, map_sum]
end GroundTheory.Heights₂.Heights.IncidenceGeneric
