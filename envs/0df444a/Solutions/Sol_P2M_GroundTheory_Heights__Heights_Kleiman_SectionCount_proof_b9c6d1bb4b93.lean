-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_proof_b9c6d1bb4b93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:56:10.861886+00:00
-- url     : https://prove2.me/submissions/0b0c5325-d857-4e77-8902-97176a51bd34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SectionCount
theorem _root_.solution (hT : SectionCount.Top.Statement.{u, w})
    (hD : SectionCount.Drop.Statement.{u, w}) : SectionCount.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨C₁, h₁⟩ := hT k Ω N x d Nb hZ hN
  obtain ⟨C₂, h₂⟩ := hD k Ω N x d Nb b hZ hN hb
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n hn₁ hn₂ hn
  set f : ℕ → ℝ := fun i =>
    (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) with hf
  set Y : ℝ := (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) with hY
  set X : ℝ := (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω)
    (twistSys k x (b : ℤ)) (fun _ : Fin d => Nb.toSubSystem)) : ℝ) with hX
  have h0 : f 0 = (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) :=
    congrArg (fun m : ℤ => (Module.finrank k (twistMul Nb.toSubSystem n m).secs : ℝ)) (by simp)
  have htel : f 0 - f n = ∑ i ∈ Finset.range n, (f i - f (i + 1)) := by
    rw [Finset.sum_range_sub']
  have hsum : ∑ i ∈ Finset.range n, (f i - f (i + 1)) ≤
      ∑ _i ∈ Finset.range n, (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) :=
    Finset.sum_le_sum fun i hi => hn₂ i (Finset.mem_range.mp hi)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : ((d + 1).factorial : ℝ) = ((d : ℝ) + 1) * (d.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have key : (n : ℝ) * (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) =
      ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) + C₂ * (n : ℝ) ^ d := by
    rw [hfac]; field_simp; ring
  rw [key] at hsum
  rw [← h0] at hn₁
  have hgoal : f n = (Module.finrank k (twistMul Nb.toSubSystem n (-((n : ℤ) * b))).secs : ℝ) := rfl
  rw [← hgoal]
  push_cast
  have e1 : (Y - ((d : ℝ) + 1) * X) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) =
      Y * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) -
        ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by ring
  rw [e1]
  linarith
end SectionCount
end GroundTheory.Heights₂.Heights.Kleiman
