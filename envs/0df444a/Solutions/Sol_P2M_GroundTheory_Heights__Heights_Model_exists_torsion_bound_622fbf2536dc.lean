-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_torsion_bound_622fbf2536dc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:42.661078+00:00
-- url     : https://prove2.me/submissions/94c91882-a566-47e8-890f-b9f7e94fff83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (A : Type*) [CommRing A] [IsNoetherianRing A] :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℤ) (a : A), n ≠ 0 → (n : A) * a = 0 → (N : A) * a = 0 := by
  let I : ℕ →o Ideal A :=
    ⟨fun j => LinearMap.ker (LinearMap.mulLeft A ((j.factorial : ℕ) : A)), by
      intro i j hij a ha
      simp only [LinearMap.mem_ker, LinearMap.mulLeft_apply] at ha ⊢
      obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hij
      rw [hc, Nat.cast_mul, mul_right_comm, ha, zero_mul]⟩
  obtain ⟨N₀, hN₀⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian A A) I
  refine ⟨N₀.factorial, Nat.factorial_pos _, fun n a hn ha => ?_⟩
  have hM : a ∈ I (max N₀ n.natAbs) := by
    have hd : n ∣ (((max N₀ n.natAbs).factorial : ℕ) : ℤ) := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      exact Nat.dvd_factorial (Int.natAbs_pos.mpr hn) (le_max_right _ _)
    obtain ⟨c, hc⟩ := hd
    have hc' : (((max N₀ n.natAbs).factorial : ℕ) : A) = (n : A) * (c : A) := by
      exact_mod_cast congrArg (Int.cast : ℤ → A) hc
    show LinearMap.mulLeft A _ a = 0
    rw [LinearMap.mulLeft_apply, hc', mul_right_comm, ha, zero_mul]
  rw [← hN₀ _ (le_max_left _ _)] at hM
  exact hM
end GroundTheory.Heights₂.Heights.Model
