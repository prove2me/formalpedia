-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_equiv_ls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:37.29386+00:00
-- url     : https://prove2.me/submissions/79b7186e-c257-4ad0-9ffb-31702dc51e26

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ExistsEquivLs
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_Frame_l_le

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
theorem _root_.solution [∀ m, Nonempty (L m)] {N₁ N₂ : Matrix (Fin n) (Fin n) k} {v₁ v₂ : Fin n → k}
    (F₁ : Frame Z M L R o N₁ v₁) (F₂ : Frame Z M L R o N₂ v₂)
    (h : ∀ m (ℓ σ : ℕ), ℓ ≤ n → σ ≤ n → Nat.card {a : F₁.ι m // F₁.l m a = ℓ ∧ F₁.s m a = σ} =
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) (m : M) :
    ∃ e : F₁.ι m ≃ F₂.ι m, ∀ a, F₂.l m (e a) = F₁.l m a ∧ F₂.s m (e a) = F₁.s m a := by
  have hf : ∀ c : ℕ × ℕ, Nonempty ({a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} ≃
      {b : F₂.ι m // (F₂.l m b, F₂.s m b) = c}) := by
    intro c
    rw [← Finite.card_eq]
    by_cases hc : c.1 ≤ n ∧ c.2 ≤ n
    · have e1 : {a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} ≃ {a : F₁.ι m // F₁.l m a = c.1 ∧ F₁.s m a = c.2} :=
        Equiv.subtypeEquivRight (fun a => Prod.ext_iff)
      have e2 : {a : F₂.ι m // (F₂.l m a, F₂.s m a) = c} ≃ {a : F₂.ι m // F₂.l m a = c.1 ∧ F₂.s m a = c.2} :=
        Equiv.subtypeEquivRight (fun a => Prod.ext_iff)
      rw [Nat.card_congr e1, Nat.card_congr e2]
      exact h m c.1 c.2 hc.1 hc.2
    · have hE1 : IsEmpty {a : F₁.ι m // (F₁.l m a, F₁.s m a) = c} := by
        refine ⟨fun ⟨a, ha⟩ => hc ?_⟩
        rw [← ha]
        exact ⟨F₁.l_le m a, (F₁.hs m a).trans (F₁.l_le m a)⟩
      have hE2 : IsEmpty {a : F₂.ι m // (F₂.l m a, F₂.s m a) = c} := by
        refine ⟨fun ⟨a, ha⟩ => hc ?_⟩
        rw [← ha]
        exact ⟨F₂.l_le m a, (F₂.hs m a).trans (F₂.l_le m a)⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]
  let e := fun c => (hf c).some
  refine ⟨Equiv.ofFiberEquiv (fun c => e c), fun a => ?_⟩
  have := Equiv.ofFiberEquiv_map (f := fun a => (F₁.l m a, F₁.s m a)) (g := fun b => (F₂.l m b, F₂.s m b))
    (fun c => e c) a
  exact Prod.ext_iff.mp this
end PositivityTheory.RgUd.T.Nil.Orb.BReps
