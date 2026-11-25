-- Prove2me | solution 1 for P2M_GlobalTheory_SW_HeckeId_sum_ite__fd2c2018495e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:51.103939+00:00
-- url     : https://prove2.me/submissions/c8b2a7ce-42c4-4a47-b8ad-5f759b1857f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_finsum_ite

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
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {A : ℕ} (p : Fin A → Prop) [DecidablePred p] (c : ℂ) (f : Fin A → ℂ)
    (hf : ∀ i, f i = if p i then c else 0) : ∑ i, f i = ({i | p i}.ncard : ℂ) * c := by
  have := finsum_ite Set.finite_univ p c f fun i _ => hf i
  rw [finsum_mem_univ, finsum_eq_sum_of_fintype] at this
  simpa using this
end GlobalTheory.SW.HeckeId
