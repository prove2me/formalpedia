-- Prove2me | solution 1 for PI.Dv.Tr.span_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:11.674213+00:00
-- url     : https://prove2.me/submissions/f25715bd-bede-4f1e-ba04-f180cd16190d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Theorems.Thm_PI_Dv_Tr_exists_den
import Theorems.Thm_UpperTheory_Reformulated_B_KudlaSiegelWeil_exists_den


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
open PI.Dv Module
open NumberField
variable {K : Type} [Field K] [NumberField K]
namespace PI.Dv.Tr
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (hL : Submodule.span K (L : Set V) = ⊤) (R : Submodule K V) :
    Submodule.span K ((L ⊓ R.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = R := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro y hy
    have hy' : y ∈ Submodule.span K (L : Set V) := by rw [hL]; exact Submodule.mem_top
    obtain ⟨d, hd, hm⟩ := exists_den L hy'
    have hdy : d • y ∈ R := by rw [← algebraMap_smul K d y]; exact R.smul_mem _ hy
    have hmem : d • y ∈ (L ⊓ R.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := Submodule.mem_inf.mpr ⟨hm, hdy⟩
    have hd' : algebraMap (𝓞 K) K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd
    have hyy : y = (algebraMap (𝓞 K) K d)⁻¹ • (d • y) := by
      rw [← algebraMap_smul K d y, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hyy]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end PI.Dv.Tr
