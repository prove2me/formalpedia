-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.conj_of_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:35.675285+00:00
-- url     : https://prove2.me/submissions/e198a1c5-5fd8-46ed-85e1-d7f33cc47202

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ExistsEquivLs
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_exists_equiv_ls

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
      Nat.card {a : F₂.ι m // F₂.l m a = ℓ ∧ F₂.s m a = σ}) :
    ∃ g : GL (Fin n) k, (∀ a ∈ Z, a * g.val = g.val * a) ∧ g.val * N₁ = N₂ * g.val ∧ g.val *ᵥ v₁ = v₂ := by
  choose σ hσ using exists_equiv_ls F₁ F₂ h
  let ψ : ∀ m, (Σ a : F₁.ι m, Fin (F₁.l m a)) ≃ (Σ b : F₂.ι m, Fin (F₂.l m b)) := fun m =>
    Equiv.sigmaCongr (σ m) (fun a => finCongr (hσ m a).1.symm)
  have hψ : ∀ m (a : F₁.ι m) (i : Fin (F₁.l m a)), ψ m ⟨a, i⟩ = ⟨σ m a, Fin.cast (hσ m a).1.symm i⟩ := by
    intro m a i
    rfl
  let Φ : (Σ m, L m × (Σ a : F₁.ι m, Fin (F₁.l m a))) ≃ (Σ m, L m × (Σ b : F₂.ι m, Fin (F₂.l m b))) :=
    Equiv.sigmaCongrRight (fun m => Equiv.prodCongr (Equiv.refl _) (ψ m))
  have hΦ : ∀ m (p : L m) j, Φ ⟨m, (p, j)⟩ = ⟨m, (p, ψ m j)⟩ := fun m p j => rfl
  let g : (Fin n → k) ≃ₗ[k] (Fin n → k) := F₁.β.equiv F₂.β Φ
  have hg : ∀ j, g (F₁.β j) = F₂.β (Φ j) := fun j => Module.Basis.equiv_apply _ _ _ _
  let G : GL (Fin n) k := ⟨LinearMap.toMatrix' (g : (Fin n → k) →ₗ[k] (Fin n → k)),
    LinearMap.toMatrix' (g.symm : (Fin n → k) →ₗ[k] (Fin n → k)),
    by rw [← LinearMap.toMatrix'_comp]; convert LinearMap.toMatrix'_id; ext x; simp,
    by rw [← LinearMap.toMatrix'_comp]; convert LinearMap.toMatrix'_id; ext x; simp⟩
  have hGv : ∀ x, G.val *ᵥ x = g x := fun x => LinearMap.toMatrix'_mulVec _ x

  have hext : ∀ X Y : Matrix (Fin n) (Fin n) k, (∀ j, X *ᵥ F₁.β j = Y *ᵥ F₁.β j) → X = Y := by
    intro X Y hXY
    apply Matrix.toLin'.injective
    apply F₁.β.ext
    intro j
    simp only [Matrix.toLin'_apply]
    exact hXY j
  refine ⟨G, ?_, ?_, ?_⟩
  · intro a ha
    apply hext
    rintro ⟨m, p, j⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGv, hg, hΦ]
    have h1 := F₂.hZ ⟨a, ha⟩ m p (ψ m j)
    have h2 := F₁.hZ ⟨a, ha⟩ m p j
    simp only at h1 h2
    rw [h1, h2, hGv, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, hg, hΦ]
  · apply hext
    rintro ⟨m, p, a, i⟩
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F₁.hN]
    simp only [hGv]
    rw [hg, hΦ, hψ, F₂.hN]
    simp only [Fin.val_cast]
    by_cases hi : (i : ℕ) + 1 < F₁.l m a
    · have hi2 : (i : ℕ) + 1 < F₂.l m (σ m a) := by rw [(hσ m a).1]; exact hi
      rw [dif_pos hi, dif_pos hi2, hg, hΦ, hψ]
      rfl
    · have hi2 : ¬ (i : ℕ) + 1 < F₂.l m (σ m a) := by rw [(hσ m a).1]; exact hi
      rw [dif_neg hi, dif_neg hi2, map_zero]
  · rw [hGv, F₁.hv, F₂.hv, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum, ← Equiv.sum_comp (σ m)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : F₁.s m a < F₁.l m a
    · have ha2 : F₂.s m (σ m a) < F₂.l m (σ m a) := by rw [(hσ m a).1, (hσ m a).2]; exact ha
      rw [dif_pos ha, dif_pos ha2, map_smul, hg, hΦ, hψ]
      have hc : (Fin.cast (hσ m a).1.symm ⟨F₁.s m a, ha⟩ : Fin (F₂.l m (σ m a))) = ⟨F₂.s m (σ m a), ha2⟩ :=
        Fin.ext (by simp [(hσ m a).2])
      rw [hc]
    · have ha2 : ¬ F₂.s m (σ m a) < F₂.l m (σ m a) := by rw [(hσ m a).1, (hσ m a).2]; exact ha
      rw [dif_neg ha, dif_neg ha2, map_zero]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
