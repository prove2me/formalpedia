-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_one_mem_idealMod_30c22dbb3514
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:27.023858+00:00
-- url     : https://prove2.me/submissions/cb86baaa-e7cf-4dc8-815d-5473c4cd8f4f

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
theorem _root_.solution {pp : Ideal (Poly k N)} {I : Chart x} {l : Fin (N + 1)} (hl : l ∈ I.1)
    (hX : (X l : Poly k N) ∈ pp) : (1 : Ω) ∈ idealMod pp I :=
  Submodule.subset_span ⟨X l, X l, 1, hX, X_mem_monos hl, isHomogeneous_X _ _, isHomogeneous_X _ _, by
    rw [aeval_X, div_self ((mem_support x).mp (I.2.2 hl))]⟩
end GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
