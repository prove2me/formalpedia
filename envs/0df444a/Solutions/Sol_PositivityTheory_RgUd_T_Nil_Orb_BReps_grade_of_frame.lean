-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_of_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:50.714418+00:00
-- url     : https://prove2.me/submissions/67853198-94b9-4fe1-b216-6d438e44364e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_grade_of_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Submodule
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {M : Type} [Fintype M] {L : M → Type}
    [∀ m, Fintype (L m)] {R : Z → (m : M) → L m → L m → k} {o : (m : M) → L m → k}
    {N : Matrix (Fin n) (Fin n) k} {v : Fin n → k} (F : Frame Z M L R o N v) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  let ω : (Σ m, L m × (Σ a : F.ι m, Fin (F.l m a))) → ℤ := fun j => ((j.2.2.2 : ℕ) : ℤ) - (F.s j.1 j.2.2.1 : ℤ)
  apply grade_of_basis F.β ω Z N v
  · rintro z hz ⟨m, p, jj⟩
    rw [show (z : Matrix (Fin n) (Fin n) k) = ((⟨z, hz⟩ : Z) : Matrix (Fin n) (Fin n) k) from rfl, F.hZ]
    refine sum_mem fun q _ => smul_mem _ _ (subset_span ⟨⟨m, q, jj⟩, rfl, rfl⟩)
  · rintro ⟨m, p, a, i⟩
    rw [F.hN]
    split_ifs with h
    · exact subset_span ⟨_, by simp only [Set.mem_ofPred_eq, ω]; push_cast; ring, rfl⟩
    · exact zero_mem _
  · suffices h : (∑ m, ∑ p, ∑ a, if h : F.s m a < F.l m a then o m p • F.β ⟨m, (p, ⟨a, ⟨F.s m a, h⟩⟩)⟩ else 0) ∈
        span k (F.β '' {j | ω j = 0}) by rw [← F.hv] at h; exact h
    refine sum_mem fun m _ => sum_mem fun p _ => sum_mem fun a _ => ?_
    split_ifs with h
    · exact smul_mem _ _ (subset_span ⟨_, by simp [ω], rfl⟩)
    · exact zero_mem _
  · rintro A hA hAN ⟨m, p, a, i⟩ hi
    exact F.hA A hA hAN m p a i (by simp only [ω] at hi; omega)
end PositivityTheory.RgUd.T.Nil.Orb.BReps
