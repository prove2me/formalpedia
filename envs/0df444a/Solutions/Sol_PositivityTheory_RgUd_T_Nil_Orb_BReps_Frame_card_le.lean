-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.Frame.card_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:51.763834+00:00
-- url     : https://prove2.me/submissions/d9356845-8255-4bc4-b98e-b9f115a99337

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
    (F : Frame Z M L R o N v) (m : M) : Nat.card (F.ι m) ≤ n := by
  obtain ⟨p⟩ := (inferInstance : Nonempty (L m))
  have hinj : Function.Injective (fun a : F.ι m =>
      (⟨m, (p, ⟨a, ⟨0, F.hl m a⟩⟩)⟩ : Σ m, L m × (Σ a : F.ι m, Fin (F.l m a)))) := by
    intro a b h
    have h1 := sigma_mk_injective h
    have h2 := (Prod.ext_iff.mp h1).2
    exact congrArg Sigma.fst h2
  have := Fintype.card_le_of_injective _ hinj
  rw [F.card_index] at this
  rw [Nat.card_eq_fintype_card]
  exact this
end Frame
end PositivityTheory.RgUd.T.Nil.Orb.BReps
