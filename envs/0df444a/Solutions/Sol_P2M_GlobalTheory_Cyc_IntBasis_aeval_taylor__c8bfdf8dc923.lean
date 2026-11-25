-- Prove2me | solution 1 for P2M_GlobalTheory_Cyc_IntBasis_aeval_taylor__c8bfdf8dc923
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:32:04.493027+00:00
-- url     : https://prove2.me/submissions/ec1fe176-6718-4325-a1a6-56e44415aca1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.IntBasis
theorem _root_.solution {R : Type} [CommRing R] [Algebra R (Om l)] (p : R[X]) (r : R) (w : Om l) :
    aeval w (taylor r p) = aeval (w + algebraMap R _ r) p := by
  rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
  simp
end GlobalTheory.Cyc.IntBasis
