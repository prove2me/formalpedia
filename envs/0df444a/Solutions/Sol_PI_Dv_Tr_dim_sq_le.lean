-- Prove2me | solution 1 for PI.Dv.Tr.dim_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:42.03083+00:00
-- url     : https://prove2.me/submissions/0d2bb317-fe44-482b-9e06-5d0db958fb4d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFiniteOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s : T.S) :
    finrank K (T.W s) * finrank K (T.W s) ≤ Fintype.card G := by
  have hall : ∀ a : MonoidAlgebra K G,
      (T.tau s).asAlgebraHom a ∈ Submodule.span K (Set.range (T.tau s)) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => rw [Representation.asAlgebraHom_of]; exact Submodule.subset_span ⟨y, rfl⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have htop : Submodule.span K (Set.range (T.tau s)) = ⊤ := by
    rw [eq_top_iff]
    intro X _
    obtain ⟨a, rfl⟩ := T.irr s X
    exact hall a
  have h1 := finrank_range_le_card (R := K) (T.tau s : G → Module.End K (T.W s))
  rw [Set.finrank, htop, finrank_top, Module.finrank_linearMap] at h1
  exact h1
end PI.Dv.Tr
