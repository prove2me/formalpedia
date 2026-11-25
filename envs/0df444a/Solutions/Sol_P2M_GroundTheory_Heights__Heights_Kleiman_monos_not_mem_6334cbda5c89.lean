-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_monos_not_mem_6334cbda5c89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:28:09.595111+00:00
-- url     : https://prove2.me/submissions/ee526cae-7a38-407f-a8a5-08db0e2df67e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {pp : Ideal (Poly S N)} [hp : pp.IsPrime] {I : Finset (Fin (N + 1))}
    (hI : ∀ i ∈ I, (X i : Poly S N) ∉ pp) {s : Poly S N} (hs : s ∈ monos I) : s ∉ pp := by
  induction hs using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    exact hI i hi
  | one => exact (Ideal.ne_top_iff_one pp).mp hp.ne_top
  | mul a b _ _ ha hb => exact fun hab => (hp.mem_or_mem hab).elim ha hb
end GroundTheory.Heights₂.Heights.Kleiman
