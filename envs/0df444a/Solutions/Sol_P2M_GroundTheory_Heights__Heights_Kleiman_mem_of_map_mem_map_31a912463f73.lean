-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_of_map_mem_map_31a912463f73
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:08:34.346936+00:00
-- url     : https://prove2.me/submissions/531476b5-ba30-450c-98ec-29e819e2bd91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDedekindFibreRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
open scoped Pointwise
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {S : Type u} [CommRing S] [IsDomain S] {F : Type u} [Field F] [Algebra S F]
    [IsFractionRing S F] {N : ℕ} {qq : Ideal (Poly S N)} (hq : qq.IsPrime)
    (hconst : ∀ s : S, (C s : Poly S N) ∈ qq → s = 0) {p : Poly S N}
    (hp : MvPolynomial.map (algebraMap S F) p ∈ qq.map (MvPolynomial.map (algebraMap S F))) : p ∈ qq := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin (N + 1)) (R := S) (S := F)
  have hdisj : Disjoint (((nonZeroDivisors S).map (C : S →+* Poly S N) : Submonoid (Poly S N)) : Set (Poly S N))
      (qq : Set (Poly S N)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsq
    exact nonZeroDivisors.ne_zero hs (hconst s hsq)
  have h := IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors S).map (C : S →+* Poly S N))
    (Poly F N) hq hdisj
  rw [← h]
  exact hp
end GroundTheory.Heights₂.Heights.Kleiman
