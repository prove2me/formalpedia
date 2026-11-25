-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.emb_pairAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:58:31.669812+00:00
-- url     : https://prove2.me/submissions/4c570fb6-ec0a-40c2-8897-8b16622c9eb5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_emb_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} {ε : Fin m → Bool}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (β : Bool) {p : PV (Rw ε β) (Fin n) (Fin n)} (hp : p ∈ pairAlg (Rw ε β) (Fin n) (Fin n)) :
    emb ε β p ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) := by
  have h1 : emb ε β p ∈ (pairAlg (Rw ε β) (Fin n) (Fin n)).map (emb ε β) := Subalgebra.mem_map.2 ⟨p, hp, rfl⟩
  rw [pairAlg, AlgHom.map_adjoin] at h1
  refine Algebra.adjoin_mono ?_ h1
  rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
  exact ⟨(β, b, a), (emb_pair β a b).symm⟩
end PositivityTheory.Rg.Sw.FFTSteps.CycF
