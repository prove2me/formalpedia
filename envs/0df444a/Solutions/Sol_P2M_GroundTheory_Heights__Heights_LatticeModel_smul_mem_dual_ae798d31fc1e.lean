-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_smul_mem_dual_ae798d31fc1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:02:37.189798+00:00
-- url     : https://prove2.me/submissions/8cc70263-f9a1-4f61-b9fe-8fff42d87177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (c : 𝓞 K) {u : Fin m → K} (hu : u ∈ latticeDual L) :
    algebraMap (𝓞 K) K c • u ∈ latticeDual L := by
  intro v hv
  obtain ⟨b, hb⟩ := hu v hv
  exact ⟨c * b, by rw [map_mul, hb, smul_dotProduct, smul_eq_mul]⟩
end GroundTheory.Heights₂.Heights.LatticeModel
