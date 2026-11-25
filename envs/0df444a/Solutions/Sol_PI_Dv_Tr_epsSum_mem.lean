-- Prove2me | solution 1 for PI.Dv.Tr.epsSum_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:03.06619+00:00
-- url     : https://prove2.me/submissions/3a74abd5-ef2d-4139-98a2-b2842a4359c8

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
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_MemRangeIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSLat
import Theorems.Thm_PI_Dv_Tr_chi_pow
import Theorems.Thm_PI_Dv_Tr_phi_apply


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
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
open Classical
namespace PI.Dv.Tr
theorem _root_.solution (A : Formalism.BasicNotions.HLat K) (ρ : Representation K G A.V) (hA : IsGLat A ρ) (Q : Pair K G) (g : G)
    (y : A.V) (hy : y ∈ A.L) : ρ.asAlgebraHom (epsSum Q * MonoidAlgebra.of K G g) y ∈ A.L := by
  rw [phi_apply]
  refine A.L.sum_mem fun h _ => ?_
  have hint : IsIntegral ℤ ((((Q.chi h)⁻¹ : Kˣ) : K)) :=
    IsIntegral.of_pow Fintype.card_pos (by rw [chi_pow]; exact isIntegral_one)
  have hmem : ρ (h : G) (ρ g y) ∈ A.L := hA.2.1 _ _ (hA.2.1 _ _ hy)
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (((Q.chi h)⁻¹ : Kˣ) : K) := ⟨⟨_, hint⟩, rfl⟩
  rw [← hr, algebraMap_smul]
  exact A.L.smul_mem r hmem
end PI.Dv.Tr
