-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_notMem_of_mem_monos_single_81fb4626dda4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:10.342475+00:00
-- url     : https://prove2.me/submissions/8141267c-c3f2-410f-afe1-d723cb080885

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_X_pow_of_mem_monos_single_54014fef5774

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
theorem _root_.solution {pp : Ideal (Poly S N)} [hpp : pp.IsPrime]
    (hX : (X j : Poly S N) ∉ pp) {s : Poly S N} (hs : s ∈ monos {j}) : s ∉ pp := by
  obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
  exact fun h => hX (hpp.mem_of_pow_mem n h)
end GroundTheory.Heights₂.Heights.Kleiman
