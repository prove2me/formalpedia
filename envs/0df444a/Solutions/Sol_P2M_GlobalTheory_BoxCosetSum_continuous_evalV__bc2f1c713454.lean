-- Prove2me | solution 1 for P2M_GlobalTheory_BoxCosetSum_continuous_evalV__bc2f1c713454
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:26.689875+00:00
-- url     : https://prove2.me/submissions/b8592442-f8e5-4f41-a48a-744aa730b6b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalingOpenSubgroupsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.BoxCosetSum
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.BoxCosetSum
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) :=
  RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v
end GlobalTheory.BoxCosetSum
