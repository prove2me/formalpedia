-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionMulInj_not_mem_of_mem_monos_0bf0f5564de5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:50.94259+00:00
-- url     : https://prove2.me/submissions/0e340f5c-69ac-4532-890c-90a6a7cae281

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionMulInjSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionMulInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3


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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
omit [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
theorem _root_.solution {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) {I : Chart x}
    (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {m : Poly S N} (hm : m ∈ monos I.1) : m ∉ pp := by
  induction hm using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    exact hX j (by exact_mod_cast hj)
  | one => exact fun h => hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  | mul a b _ _ ha hb => exact fun h => (hpp.mem_or_mem h).elim ha hb
end GroundTheory.Heights₂.Heights.Kleiman.SectionMulInj
