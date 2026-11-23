-- Prove2me | solution 1 for PI.Dv.ProjGramW.linIndep_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:22.320087+00:00
-- url     : https://prove2.me/submissions/c87e29c7-f6d6-4637-9aca-e6971e241830

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {d : ℕ} {b : Fin d → V} (hb : LinearIndependent K b) (C : Matrix (Fin d) (Fin d) K)
    (hC : C.det ≠ 0) : LinearIndependent K (fun j => ∑ i, C i j • b i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : ∑ i, (∑ j, C i j * g j) • b i = 0 := by
    rw [← hg]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have h2 := (Fintype.linearIndependent_iff.mp hb) _ h1
  have h3 : Matrix.mulVec C g = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct] using h2 i
  have h4 := Matrix.eq_zero_of_mulVec_eq_zero hC h3
  intro j
  simpa using congrFun h4 j
end PI.Dv.ProjGramW
