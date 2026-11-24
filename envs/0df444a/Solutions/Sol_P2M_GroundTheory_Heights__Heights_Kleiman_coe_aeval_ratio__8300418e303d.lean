-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio__8300418e303d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:55.75456+00:00
-- url     : https://prove2.me/submissions/01872757-4ee3-4b80-b14f-16fb7f6c7a08

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coe_aeval_ratio_3a0d7bd51278

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
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hj : x j ≠ 0) {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    ((aeval (ratio (S := S) hj) f : chartRing S x (singleChart hj)) : Ω) =
      aeval x f / aeval x (X j ^ e : Poly S N) := by
  rw [coe_aeval_ratio hj hf, map_pow, aeval_X]
end GroundTheory.Heights₂.Heights.Kleiman
