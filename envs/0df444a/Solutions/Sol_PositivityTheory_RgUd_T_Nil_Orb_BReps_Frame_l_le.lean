-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.Frame.l_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:44.158293+00:00
-- url     : https://prove2.me/submissions/cda29837-202e-46fe-b189-0574746be166

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ExistsEquivLs
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_Frame_card_index

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}
variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
namespace Frame
theorem _root_.solution [∀ m, Nonempty (L m)] {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k}
    (F : Frame Z M L R o N v) (m : M) (a : F.ι m) : F.l m a ≤ n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (L m))
  have hinj : Function.Injective (fun i : Fin (F.l m a) =>
      (⟨m, (p, ⟨a, i⟩)⟩ : Σ m, L m × (Σ a : F.ι m, Fin (F.l m a)))) := by
    intro i j h
    have h1 := sigma_mk_injective h
    have h2 := sigma_mk_injective (Prod.ext_iff.mp h1).2
    exact h2
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin, F.card_index] at this
  exact this
end Frame
end PositivityTheory.RgUd.T.Nil.Orb.BReps
