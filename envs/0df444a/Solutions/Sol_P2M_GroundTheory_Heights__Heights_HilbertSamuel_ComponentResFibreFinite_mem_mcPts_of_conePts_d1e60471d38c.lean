-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_mem_mcPts_of_conePts_d1e60471d38c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:25:39.615336+00:00
-- url     : https://prove2.me/submissions/4eb65ffd-cd09-4411-897e-4285fca7d5ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComponentResFibreFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
theorem _root_.solution {P : Ideal (MRing ι)}
    (hW : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ ReciprocityTheory.AnForm.R.conePts W) : z ∈ mcPts P :=
  ⟨hz.1, fun _ hf => hz.2 _ (hW (Ideal.mem_map_of_mem _ hf))⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
