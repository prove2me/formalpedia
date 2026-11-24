-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.nM_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:49.704144+00:00
-- url     : https://prove2.me/submissions/2ef98564-384f-40f5-a8a3-7353d4512f9d

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_pm_mul
import Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_hform_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (w w' : Fin M → K) (z z' : K) :
    nM s J w z * nM s J w' z' = nM s J (w + w') (z + z' - hform s J w w') := by
  have e : (s : K → K) ∘ (w + w') = s ∘ w + s ∘ w' := funext fun _ => map_add s _ _
  simp only [nM, pm_mul, hform_eq, e, add_vecMul]
  congr 1 <;> simp <;> ring
end PositivityTheory.PlacePermOperatorBicommutantSpan
