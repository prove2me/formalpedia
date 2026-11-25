-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_dehom_9258b8c7abab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:13.343226+00:00
-- url     : https://prove2.me/submissions/aafde6a7-b3cb-43dd-b14a-83e9ff5ab4ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_dehom_latticeForm_apply_7734b2f3c555


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
theorem _root_.solution (u : Fin (r + 1) → K) :
    IsAlgebraic (IntermediateField.adjoin ℚ (Set.range (genericT K r))) (dehom K r (latticeForm u)) := by
  set E := IntermediateField.adjoin ℚ (Set.range (genericT K r))
  rw [← Subalgebra.mem_algebraicClosure, dehom_latticeForm_apply]
  refine sum_mem fun j _ ↦ mul_mem ?_ ?_
  · rw [Subalgebra.mem_algebraicClosure]
    have h : IsAlgebraic ℚ (algebraMap K (LatticeField K r) (u j)) := by
      simpa using (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (u j)).algHom
        (IsScalarTower.toAlgHom ℚ K (LatticeField K r))
    exact h.tower_top E
  · rw [Subalgebra.mem_algebraicClosure]
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simpa [genericVal] using isAlgebraic_one (R := E) (A := LatticeField K r)
    · have hi : genericT K r i ∈ E := IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
      simpa [genericVal, genericT] using isAlgebraic_algebraMap (R := E) (A := LatticeField K r) ⟨_, hi⟩
end GroundTheory.Heights₂.Heights.LatticeModel
