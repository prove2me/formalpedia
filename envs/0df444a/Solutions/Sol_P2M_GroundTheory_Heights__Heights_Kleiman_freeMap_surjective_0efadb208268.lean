-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_surjective_0efadb208268
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:42.648472+00:00
-- url     : https://prove2.me/submissions/fb5d1198-7f8d-4938-8972-2e5097c222e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_apply_d4ac1e5ea45a

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
open MvPolynomial
noncomputable section
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
omit [Module S M] [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {r : ℕ} {g : Fin r → M} (hg : Submodule.span (Poly S N) (Set.range g) = ⊤) :
    Function.Surjective (freeMap S N g) := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine ⟨Pi.single j 1, ?_⟩
  rw [freeMap_apply, Finset.sum_eq_single j (fun j' _ h => by rw [Pi.single_eq_of_ne h, zero_smul])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
end GroundTheory.Heights₂.Heights.Kleiman
