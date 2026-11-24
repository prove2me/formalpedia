-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_coeff_rename_prodCongrRight_58c6c769a27c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:33:51.945704+00:00
-- url     : https://prove2.me/submissions/ad46b053-6203-46a7-82af-bcf494b1edf5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagEq
variable {f N : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagEq
theorem _root_.solution {R : Type*} [CommSemiring R] (w : Fin f → Equiv.Perm (Fin N))
    (P : MvPolynomial (Fin f × Fin N) R) (d : Fin f × Fin N →₀ ℕ) :
    coeff d (rename (Equiv.prodCongrRight w) P) =
      coeff (Finsupp.equivFunOnFinite.symm fun v => d (Equiv.prodCongrRight w v)) P := by
  rw [← coeff_rename_mapDomain (Equiv.prodCongrRight w) (Equiv.injective _) P]
  congr 1
  ext v
  obtain ⟨u, rfl⟩ := (Equiv.prodCongrRight w).surjective v
  rw [Finsupp.mapDomain_apply (Equiv.injective _)]
  simp
end GroundTheory.Heights₂.Heights.RestTerms.FlagEq
