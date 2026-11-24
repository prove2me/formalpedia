-- Prove2me | solution 1 for PI.FJMS.sum_range_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:06.253846+00:00
-- url     : https://prove2.me/submissions/2a360ceb-469a-41b8-9711-57f86f04d604

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Lemmata_B1959r_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PosIffLtNP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMS
open PI.FJM PI.FJMP
variable {σ κ : Type*} [Fintype κ]
namespace PI.FJMS
theorem _root_.solution {M : Type*} [AddCommMonoid M] {m : ℕ} (j : Fin m → κ) (hj : Function.Injective j)
    (f : κ → M) (hf : ∀ c, c ∉ Set.range j → f c = 0) : ∑ c, f c = ∑ k, f (j k) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨j, hj⟩))
    (fun c _ hc => hf c (fun ⟨k, hk⟩ => hc (Finset.mem_map.2 ⟨k, Finset.mem_univ _, hk⟩))), Finset.sum_map]
  rfl
end PI.FJMS
