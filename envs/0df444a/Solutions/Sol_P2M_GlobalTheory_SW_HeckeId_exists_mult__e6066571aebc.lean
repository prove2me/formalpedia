-- Prove2me | solution 1 for P2M_GlobalTheory_SW_HeckeId_exists_mult__e6066571aebc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:48.081243+00:00
-- url     : https://prove2.me/submissions/32ab3e13-e8d7-4240-b8a5-3731b95aec45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_Base_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_TwistAdm_exists_mult
import Theorems.Thm_GlobalTheory_SW_TwistAdm_nat_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
omit [IsCMField E]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {M R q : ℕ} (hR : 0 < R) (hq : q.Coprime (R * M)) {𝔛 : Lt E N}
    (h : Agree (R * M) 𝔛 (stdL E N)) :
    ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ stdL E N, ∃ ξ ∈ 𝔛, (s : E) • v = (q : E) • ξ := by
  obtain ⟨s, hs, h1⟩ := TwistAdm.exists_mult hR h
  have hc' : q.Coprime (R ^ 2) := (Nat.Coprime.coprime_mul_right_right hq).pow_right 2
  refine ⟨q ^ (R ^ 2).totient * s, by simpa using (Nat.ModEq.pow_totient hc').mul hs,
    fun v hv => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.totient_pos.2 (pow_pos hR 2)).ne'
  refine ⟨_, TwistAdm.nat_smul_mem _ (q ^ k) (h1 v hv), ?_⟩
  rw [hk, smul_smul, smul_smul]
  congr 1
  push_cast
  rw [pow_succ]
  ring
end GlobalTheory.SW.HeckeId
