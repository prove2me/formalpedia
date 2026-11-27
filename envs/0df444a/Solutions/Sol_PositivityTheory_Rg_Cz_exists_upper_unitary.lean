-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.exists_upper_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:09.220058+00:00
-- url     : https://prove2.me/submissions/7eec1771-2030-4d18-a2fd-ea250a824bc1

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_ArchimedeanWhittakerDerivatives_ExistsUpperUnitary
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_exists_upper_mul_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open Matrix
namespace PositivityTheory.Rg.Cz
theorem _root_.solution {ι : Type} {n : ℕ} (y : GL (Fin n) (ι → ℂ)) :
    ∃ (b : GL (Fin n) (ι → ℂ)) (k : Matrix.unitaryGroup (Fin n) (ι → ℂ)),
      (∀ i j : Fin n, j < i → b.val i j = 0) ∧ y = b * Unitary.toUnits k := by
  exact GlobalTheory.CompanionTheory.Iwasawa.exists_upper_mul_unitary y
end PositivityTheory.Rg.Cz
