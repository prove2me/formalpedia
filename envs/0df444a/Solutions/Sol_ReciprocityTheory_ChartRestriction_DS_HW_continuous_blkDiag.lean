-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.continuous_blkDiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:34.540914+00:00
-- url     : https://prove2.me/submissions/ed7e1e3e-657c-4473-8626-038bb33e7871

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) : Continuous (blkDiag ε) := by
  let L : (∀ s : Bool, Matrix (Fin (blkP ε s)) (Fin (blkP ε s)) ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := blkDiag ε
      map_add' := map_add _
      map_smul' := fun c v => by
        ext i j
        obtain ⟨x, rfl⟩ := (blkSig ε).surjective i
        obtain ⟨y, rfl⟩ := (blkSig ε).surjective j
        rcases x with ⟨s, a⟩
        rcases y with ⟨t, b⟩
        simp only [RingHom.id_apply, Matrix.smul_apply, blkDiag_apply]
        by_cases hst : s = t
        · subst hst
          simp [Matrix.blockDiagonal'_apply_eq]
        · simp [Matrix.blockDiagonal'_apply_ne _ _ _ hst] }
  exact L.continuous_of_finiteDimensional
end ReciprocityTheory.ChartRestriction.DS.HW
