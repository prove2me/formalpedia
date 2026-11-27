-- Prove2me | solution 1 for PositivityTheory.UnitarySelfGeneration.Mend.spectralNorm_le_one_iff_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:27.677187+00:00
-- url     : https://prove2.me/submissions/2ad5c7cf-913b-4ec2-9335-1eed0173e782

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HomogeneousNonvanishing_SpectralNormIntegrality_SpecInt
import Theorems.Thm_PositivityTheory_UnitarySelfGeneration_Mend_specInt_norm_le_one_iff_mem
import Theorems.Thm_PositivityTheory_UnitarySelfGeneration_Mend_specInt_isIntegral_iff_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.UnitarySelfGeneration PositivityTheory.UnitarySelfGeneration.Mend
namespace PositivityTheory.UnitarySelfGeneration.Mend
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (y : AlgebraicClosure (v.adicCompletion F)) :
    spectralNorm (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) y ≤ 1 ↔
      IsIntegral (v.adicCompletionIntegers F) y := by
  have hy : IsIntegral (v.adicCompletion F) y := Algebra.IsIntegral.isIntegral y
  rw [specInt_isIntegral_iff_coeff (v.adicCompletionIntegers F) y hy, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic hy)]
  simp only [specInt_norm_le_one_iff_mem]
end PositivityTheory.UnitarySelfGeneration.Mend
