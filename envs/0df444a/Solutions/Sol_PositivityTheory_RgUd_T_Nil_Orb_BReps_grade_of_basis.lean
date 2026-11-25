-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:58.416808+00:00
-- url     : https://prove2.me/submissions/b7836466-fe0a-4244-8a82-c8304db1cc1a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_grade_fin

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
theorem _root_.solution {κ : Type} [Fintype κ] (β : Module.Basis κ k (Fin n → k)) (ω : κ → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ β j ∈ span k (β '' {j' | ω j' = ω j}))
    (hN : ∀ j, N *ᵥ β j ∈ span k (β '' {j' | ω j' = ω j + 1}))
    (hv : v ∈ span k (β '' {j | ω j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, ω j < 0 → β.repr (a *ᵥ v) j = 0) :
    ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  have hcard : Fintype.card κ = n := by
    rw [← Module.finrank_eq_card_basis β, Module.finrank_fin_fun]
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b := β.reindex e
  let w : Fin n → ℤ := fun i => ω (e.symm i)
  have hb : ∀ j, β j = b (e j) := fun j => by simp [b]
  have himg : ∀ c : ℤ, β '' {j | ω j = c} = b '' {i | w i = c} := by
    intro c
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e j, by simpa [w] using hj, (hb j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e.symm i, hi, by simp [b]⟩
  refine ⟨gradeBasisGL b, w, grade_fin b w Z N v ?_ ?_ ?_ ?_⟩
  · intro z hz i
    have := hZ z hz (e.symm i)
    rw [himg] at this
    simpa [b, w] using this
  · intro i
    have := hN (e.symm i)
    rw [himg] at this
    simpa [b, w] using this
  · rw [← himg]; exact hv
  · intro a ha haN i hi
    have := hA a ha haN (e.symm i) hi
    simpa [b] using this
end PositivityTheory.RgUd.T.Nil.Orb.BReps
