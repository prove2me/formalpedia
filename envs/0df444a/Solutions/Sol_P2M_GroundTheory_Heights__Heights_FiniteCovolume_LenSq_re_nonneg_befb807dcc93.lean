-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_re_nonneg_befb807dcc93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:15.611044+00:00
-- url     : https://prove2.me/submissions/0674a5aa-43a5-477c-8300-3b31c6f8fc93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace LenSq
theorem _root_.solution {P : Matrix ι ι ℂ} (hP : P.PosDef) (y : ι → ℂ) :
    0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re :=
  (Complex.nonneg_iff.mp (hP.posSemidef.dotProduct_mulVec_nonneg y)).1
end LenSq
end GroundTheory.Heights₂.Heights.FiniteCovolume
