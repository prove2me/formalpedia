-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_LocalCovolumeBasis_mem_locP__ad3a70047646
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:24.466349+00:00
-- url     : https://prove2.me/submissions/48fe47a3-a9ba-4a7d-9cbd-5aa3c120b460

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.DivisionValues Formalism.DivisionValues.LocalCovolumeBasis
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
namespace Formalism.DivisionValues.LocalCovolumeBasis
theorem _root_.solution (p : Ideal (𝓞 K)) [p.IsPrime] (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl
end Formalism.DivisionValues.LocalCovolumeBasis
