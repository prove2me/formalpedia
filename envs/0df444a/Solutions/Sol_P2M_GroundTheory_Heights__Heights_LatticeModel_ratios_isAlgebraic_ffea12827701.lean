-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_ratios_isAlgebraic_ffea12827701
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:56.670773+00:00
-- url     : https://prove2.me/submissions/8a75c7c3-20c6-445e-b43f-175bef269106

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_dehom_9258b8c7abab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeCoord_eq_665c52b880b5


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
variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution (s : LatticeField K r)
    (hs : s ∈ coneRatios (latticeCoord φ) (fun _ : Unit ↦ (0 : Fin (N + 1)))) :
    IsAlgebraic (IntermediateField.adjoin ℚ (Set.range (genericT K r))) s := by
  obtain ⟨p, rfl⟩ := hs
  have h0 := isAlgebraic_dehom (r := r) (φ 0)
  have hp := isAlgebraic_dehom (r := r) (φ p.2)
  have e : latticeCoord φ p / latticeCoord φ ⟨p.1, 0⟩ =
      dehom K r (latticeForm (φ p.2)) * (dehom K r (latticeForm (φ 0)))⁻¹ := by
    rw [latticeCoord_eq, latticeCoord_eq, div_eq_mul_inv]
  change IsAlgebraic _ (latticeCoord φ p / latticeCoord φ ⟨p.1, 0⟩)
  rw [e]
  exact hp.mul h0.inv
end GroundTheory.Heights₂.Heights.LatticeModel
