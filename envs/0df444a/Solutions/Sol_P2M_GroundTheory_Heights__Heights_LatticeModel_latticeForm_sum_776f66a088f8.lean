-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_sum_776f66a088f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:09.631973+00:00
-- url     : https://prove2.me/submissions/423a7ab7-3437-45d9-a282-fb31d55bc119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_latticeForm_add_ff76c8df2829

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
variable {K : Type} [Field K] [NumberField K]
variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}
namespace GroundTheory.Heights₂.Heights.LatticeModel
theorem _root_.solution {ι : Type*} (s : Finset ι) (u : ι → Fin m → K) :
    latticeForm (∑ i ∈ s, u i) = ∑ i ∈ s, latticeForm (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [latticeForm_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, latticeForm_add, ih]
end GroundTheory.Heights₂.Heights.LatticeModel
