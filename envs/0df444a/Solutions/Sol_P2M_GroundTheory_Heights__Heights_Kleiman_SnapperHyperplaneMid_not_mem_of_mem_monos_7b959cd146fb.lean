-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_not_mem_of_mem_monos_7b959cd146fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:20:25.980348+00:00
-- url     : https://prove2.me/submissions/f8c55d21-ac6a-4f38-bb7f-a438476088d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
theorem _root_.solution {pp : Ideal (Poly k N)} (hp : pp.IsPrime) {I : Finset (Fin (N + 1))}
    (hI : ∀ l ∈ I, (X l : Poly k N) ∉ pp) {s : Poly k N} (hs : s ∈ monos I) : s ∉ pp := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨l, hl, rfl⟩ := ha
    exact hI l hl
  | one => exact fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  | mul a b _ _ ha hb => exact fun h => (hp.mem_or_mem h).elim ha hb
end GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
