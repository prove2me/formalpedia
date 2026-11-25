-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_prod_mem_prodSpan_0cba948c4940
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:48.465361+00:00
-- url     : https://prove2.me/submissions/7d91593f-622f-4bdd-9b4a-853ba0490fa9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_one_mem_prodSpan_zero_c23367664238
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_mul_mem_prodSpan_f0c3d551bff6

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
theorem _root_.solution {ι : Type*} (t : Finset ι) (g : ι → MvPolynomial (Fin m) K) (e : ι → ℕ)
    (h : ∀ i ∈ t, g i ∈ prodSpan L (e i)) : ∏ i ∈ t, g i ∈ prodSpan L (∑ i ∈ t, e i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using one_mem_prodSpan_zero
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_prodSpan (h i (Finset.mem_insert_self i t))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
end GroundTheory.Heights₂.Heights.LatticeModel
