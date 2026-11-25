-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_mem_9c019e288fdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:17.545014+00:00
-- url     : https://prove2.me/submissions/fdd61f84-eb08-4180-8286-57ff8222b12b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_smul_mem_int_382e083d6e10
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
omit [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {r : ℕ} (𝓜 : GradedPMod S N M) {g : Fin r → M} {deg : Fin r → ℤ}
    (hg : ∀ j, g j ∈ 𝓜.piece (deg j)) (c : ℤ) {f : Fin r → Poly S N}
    (hf : f ∈ (freeGraded S N deg).piece c) : freeMap S N g f ∈ 𝓜.piece c := by
  rw [freeMap_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : f j ∈ (polyGraded S N).piece (c - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
  have := 𝓜.smul_mem_int hj (hg j)
  rwa [add_sub_cancel] at this
end GroundTheory.Heights₂.Heights.Kleiman
