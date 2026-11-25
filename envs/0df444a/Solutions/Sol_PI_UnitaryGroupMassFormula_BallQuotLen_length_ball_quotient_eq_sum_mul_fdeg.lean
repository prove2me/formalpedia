-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BallQuotLen.length_ball_quotient_eq_sum_mul_fdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:10.329345+00:00
-- url     : https://prove2.me/submissions/7649f278-71d6-410a-9842-d483515a3684

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Formalism_PeriodIntegrals_BallQuotLen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EfRankSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BallQuotientLength_LengthBallQuotientEqSumMulFdeg
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_length_quot_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_length_zero_of_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_ballO_mono
import Theorems.Thm_PI_UnitaryGroupMassFormula_BallQuotLen_length_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BallQuotLen
open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {A : Type*} [CommRing A] [Algebra O A] {ϖ : O}
variable {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [IsScalarTower O A V] {e : V}
namespace PI.UnitaryGroupMassFormula.BallQuotLen
theorem _root_.solution (K : Type*) [Field K] [Algebra K A] [FiniteDimensional K A]
    [Fintype (Pts O A)] [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ)
    (hfin : Module.Finite O ↥(As O A)) (he : IsGen A e) :
    ∀ (n : ℕ) (c : Pts O A → ℤ) (m : Pts O A → ℕ), ∑ ζ, m ζ = n →
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ ζ, m ζ * fdeg ζ : ℕ) : ℕ∞) := by
  classical
  intro n
  induction n with
  | zero =>
    intro c m hm
    have hm0 : ∀ ζ, m ζ = 0 := fun ζ => (Finset.sum_eq_zero_iff.mp hm) ζ (Finset.mem_univ _)
    simp only [hm0, Nat.cast_zero, add_zero, zero_mul, Finset.sum_const_zero]
    exact length_zero_of_le (ballO_mono h he (fun ζ => by simp [hm0 ζ]))
  | succ n ih =>
    intro c m hm
    obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀, m ζ₀ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      simp [hcon] at hm
    let m' : Pts O A → ℕ := fun ζ => if ζ = ζ₀ then m ζ - 1 else m ζ
    have hmm : ∀ ζ, m ζ = m' ζ + if ζ = ζ₀ then 1 else 0 := by
      intro ζ
      by_cases hz : ζ = ζ₀
      · subst hz
        show m ζ = (if ζ = ζ then m ζ - 1 else m ζ) + if ζ = ζ then 1 else 0
        rw [if_pos rfl, if_pos rfl]
        omega
      · show m ζ = (if ζ = ζ₀ then m ζ - 1 else m ζ) + if ζ = ζ₀ then 1 else 0
        rw [if_neg hz, if_neg hz, add_zero]
    have hsum : ∑ ζ, m ζ = ∑ ζ, m' ζ + 1 := by
      rw [Finset.sum_congr rfl (fun ζ _ => hmm ζ), Finset.sum_add_distrib]
      simp
    have hm' : ∑ ζ, m' ζ = n := by omega
    have hle1 : ballO ϖ e c ≤ ballO ϖ e (fun ζ => c ζ + (m' ζ : ℤ)) :=
      ballO_mono h he (fun ζ => le_add_of_nonneg_right (Nat.cast_nonneg _))
    have hle2 : ballO ϖ e (fun ζ => c ζ + (m' ζ : ℤ)) ≤ ballO ϖ e (fun ζ => c ζ + (m ζ : ℤ)) :=
      ballO_mono h he (fun ζ => show c ζ + (m' ζ : ℤ) ≤ c ζ + (m ζ : ℤ) by
        have h5 : (m' ζ : ℤ) ≤ (m ζ : ℤ) :=
          Nat.cast_le.mpr (le_trans (Nat.le_add_right _ _) (hmm ζ).symm.le)
        linarith)
    have hd : ∀ ζ, (fun ζ => c ζ + (m ζ : ℤ)) ζ =
        (fun ζ => c ζ + (m' ζ : ℤ)) ζ + if ζ = ζ₀ then 1 else 0 := by
      intro ζ
      beta_reduce
      rw [hmm ζ]
      split_ifs <;> push_cast <;> ring
    have hs : ∑ ζ, m ζ * fdeg ζ = ∑ ζ, m' ζ * fdeg ζ + fdeg ζ₀ := by
      rw [Finset.sum_congr rfl (fun ζ _ => by rw [hmm ζ, add_mul]), Finset.sum_add_distrib]
      congr 1
      simp [ite_mul]
    rw [length_quot_add hle1 hle2, ih c m' hm', length_step K h hfin he _ _ ζ₀ hd, hs, Nat.cast_add]
end PI.UnitaryGroupMassFormula.BallQuotLen
