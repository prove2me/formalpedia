-- Prove2me | solution 1 for P2M_GlobalTheory_NormCompat_RatioClose_norm_one_tmul__0e587e6c05b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:48.489799+00:00
-- url     : https://prove2.me/submissions/012e99e3-f5d8-4145-b5d3-b97e58c04a7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTensorIdempotentOfAlgHomToBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqMulNormIdempotentCornerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationLeOneOfSqSubSelfIntegralBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGlobalElementNearIdempotentAdicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDivLocalEmbeddingCloseToOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.RatioClose
namespace GlobalTheory.NormCompat.RatioClose
theorem _root_.solution {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    [Module.Finite F E] (y : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] y) = algebraMap F K (Algebra.norm F y) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
end GlobalTheory.NormCompat.RatioClose
