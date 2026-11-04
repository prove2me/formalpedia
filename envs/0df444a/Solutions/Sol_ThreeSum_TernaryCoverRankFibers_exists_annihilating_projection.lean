-- Prove2me | solution 1 for ThreeSum.TernaryCoverRankFibers.exists_annihilating_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:46.35678+00:00
-- url     : https://prove2.me/submissions/e40a9b26-c588-4d87-b065-d18f3a78ec87

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRankFibers
open Finset
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryCoverRankFibers
theorem _root_.solution (V : Submodule K (K × K)) (hV : V ≠ ⊤) :
    ∃ β γ : K, (β ≠ 0 ∨ γ ≠ 0) ∧ ∀ v ∈ V, β * v.1 + γ * v.2 = 0 := by
  have hAnn : V.dualAnnihilator ≠ ⊥ := by
    intro h
    exact hV (Submodule.dualAnnihilator_eq_bot_iff.mp h)
  obtain ⟨φ, hφ, hφne⟩ := V.dualAnnihilator.ne_bot_iff.mp hAnn
  have heval (v : K × K) : φ v = v.1 * φ (1,0) + v.2 * φ (0,1) := by
    have heq : v = v.1 • (1,0) + v.2 • (0,1) := by ext <;> simp
    rw [heq, map_add, map_smul, map_smul]
    simp
  refine ⟨φ (1,0), φ (0,1), ?_, ?_⟩
  · by_contra! hz
    apply hφne
    apply LinearMap.ext
    intro v
    change φ v = 0
    rw [heval v, hz.1, hz.2]
    simp
  · intro v hv
    have hz := (Submodule.mem_dualAnnihilator φ).mp hφ v hv
    rw [heval] at hz
    simpa [mul_comm] using hz
end ThreeSum.TernaryCoverRankFibers
