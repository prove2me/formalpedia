-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplMinExists_proof_dc6b510fb395
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:39:45.715632+00:00
-- url     : https://prove2.me/submissions/2ff984a3-7946-4127-9ce6-d87a066ddcb0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinExists_exists_lower_735580152940

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace SymplMinExists
theorem _root_.solution (h1 : SymplQuadDiag.Statement) : SymplMinExists.Statement := by
  intro ι _ _ _ G hG
  obtain ⟨μ, hμ, hlow⟩ := PSymplMinExists.exists_lower G hG
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set v₀ : ι → ℤ := Pi.single i₀ 1 with hv₀def
  set M₀ : ℝ := qf G (intVec v₀) with hM₀
  set R : ℤ := ⌈M₀ / μ⌉ with hR
  set S : Set (ι → ℤ) := {v | v ≠ 0 ∧ qf G (intVec v) ≤ M₀} with hS
  have hbox : S ⊆ Set.Icc (fun _ => -R) (fun _ => R) := by
    rintro v ⟨-, hq⟩
    have hb : ∀ i, |(v i : ℝ)| ≤ M₀ / μ := by
      intro i
      have hi : |(v i : ℝ)| ≤ ‖intVec v‖ := by
        have := norm_le_pi_norm (intVec v) i
        simpa [intVec, Real.norm_eq_abs] using this
      have hsq : |(v i : ℝ)| ≤ |(v i : ℝ)| ^ 2 := by
        rcases eq_or_ne (v i) 0 with h | h
        · simp [h]
        · have h' : (1 : ℝ) ≤ |(v i : ℝ)| := by
            rw [← Int.cast_abs]
            exact_mod_cast Int.one_le_abs h
          nlinarith
      have hsq2 : |(v i : ℝ)| ^ 2 ≤ ‖intVec v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hi 2
      rw [le_div_iff₀ hμ]
      calc |(v i : ℝ)| * μ ≤ μ * ‖intVec v‖ ^ 2 := by nlinarith
        _ ≤ qf G (intVec v) := hlow _
        _ ≤ M₀ := hq
    have hc : ∀ i, |v i| ≤ R := by
      intro i
      have : ((|v i| : ℤ) : ℝ) ≤ (R : ℝ) := by
        rw [Int.cast_abs]
        exact (hb i).trans (Int.le_ceil _)
      exact_mod_cast this
    refine ⟨fun i => ?_, fun i => ?_⟩
    · exact (abs_le.mp (hc i)).1
    · exact (abs_le.mp (hc i)).2
  have hfin : S.Finite := (Set.finite_Icc _ _).subset hbox
  have hv₀ : v₀ ∈ S := by
    refine ⟨fun h => ?_, le_rfl⟩
    have := congrFun h i₀
    simp [v₀] at this
  obtain ⟨w, hwS, hwmin⟩ := Set.exists_min_image S (fun v => qf G (intVec v)) hfin ⟨v₀, hv₀⟩
  refine ⟨qf G (intVec w), ⟨w, hwS.1, rfl⟩, ?_⟩
  rintro t ⟨v, hv, rfl⟩
  by_cases hvS : qf G (intVec v) ≤ M₀
  · exact hwmin v ⟨hv, hvS⟩
  · exact hwS.2.trans (le_of_lt (not_le.mp hvS))
end SymplMinExists
end GroundTheory.Heights₂.Heights
