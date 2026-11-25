-- Prove2me | solution 1 for P2M_GlobalTheory_SW_ShortStep_li_of_mul__9c3b39fbd582
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:05.177391+00:00
-- url     : https://prove2.me/submissions/b2b8eb58-f484-426c-8aa7-7467fdd41d5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_li_of_mul


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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution {m n : ℕ} {B : Matrix (Fin m) (Fin n) E} (h : LinearIndependent E fun i => B i)
    {k : E} (hk : k ≠ 0) : LinearIndependent E fun i => (k • B) i := by
  refine li_of_mul (R := k⁻¹ • (1 : Matrix (Fin n) (Fin n) E)) ?_
  rwa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hk, one_smul, Matrix.mul_one]
end GlobalTheory.SW.ShortStep
