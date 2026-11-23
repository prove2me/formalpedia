-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.sum_fun_eq_sum_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:53.533349+00:00
-- url     : https://prove2.me/submissions/fe6c076e-db8d-4a67-8437-8f1b8cd51820

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin n → Fin n) → M)
    (hf : ∀ c, ¬ Function.Injective c → f c = 0) :
    ∑ c, f c = ∑ π : Equiv.Perm (Fin n), f π := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.map ⟨fun π : Equiv.Perm (Fin n) => (π : Fin n → Fin n), DFunLike.coe_injective⟩))]
  · rw [Finset.sum_map]
    rfl
  · intro c _ hc
    apply hf
    intro hinj
    apply hc
    rw [Finset.mem_map]
    exact ⟨Equiv.ofBijective c hinj.bijective_of_finite, Finset.mem_univ _, rfl⟩
end PI.UnitaryGroupMassFormula.DSIC
