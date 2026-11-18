-- Prove2me | solution 1 for TwoStageRnQ.paper_rule_follows_rand
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T00:27:21.091922+00:00
-- url     : https://prove2.me/submissions/466429ee-2b7d-457d-9d50-604884c32a58

import Definitions.Def_TwoStageRnQ_RuleRand
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

open MeasureTheory

noncomputable section

namespace TwoStageRnQ

namespace Rule

open RuleRand

section Algebra

variable (c : ClassicalControls)

lemma qZ_pos : 0 < qZ c := by unfold qZ; exact_mod_cast c.1.2.2.1.pos

lemma rZ_nonneg : 0 ≤ rZ c := by unfold rZ; positivity

lemma rZ_lt : rZ c < qZ c := by unfold rZ qZ; exact_mod_cast c.2

end Algebra

lemma qZ_dvd_mZ (c : ClassicalControls) : qZ c ∣ mZ c := ⟨nZ c, by unfold mZ; ring⟩

lemma dvd_of_dvd_eq {q a b : ℤ} (h : q ∣ b) (e : a = b) : q ∣ a := e ▸ h

section Path

variable {P : Params} (S : DemandSpace P)

def FollowsAt (π : ShipmentPolicy P S) (c : ClassicalControls) (Ihat : ℝ → S.Ω → ℤ) (ω : S.Ω) :
    Prop :=
  qZ c ∣ (π.x2 ω + π.U2 0 ω - S.N 0 ω) - rZ c - Ihat 0 ω ∧
    ∀ t : ℝ, 0 ≤ t →
      qZ c ∣ (Ihat t ω + S.N t ω) - (Ihat 0 ω + S.N 0 ω) ∧
      mZ c ∣ π.U2 t ω - π.U2 0 ω ∧
      (c.1.2.1 < π.x2 ω + π.U2 t ω - S.N t ω ∧ π.x2 ω + π.U2 t ω - S.N t ω ≤ c.1.2.1 + mZ c) ∧
      (c.1.1 < Ihat t ω ∧ Ihat t ω ≤ c.1.1 + qZ c) ∧
      π.x1 ω + π.U1 t ω - S.N t ω
        = min (Ihat t ω) (π.x2 ω + π.U2 (t - P.L2) ω - S.N t ω - rZ c)

end Path

section Cov

variable {P : Params} (S : DemandSpace P)

theorem paper_follows_at (π : ShipmentPolicy P S) (c : ClassicalControls) (β : ℝ → S.Ω → ℤ)
    (ω : S.Ω)
    (hpipe : ∀ s : ℝ, -P.L2 ≤ s → s ≤ 0 → mZ c ∣ π.U2 0 ω - π.U2 s ω)
    (hrem : qZ c ∣ (π.x2 ω + π.U2 (-P.L2) ω - (π.x1 ω + π.U1 0 ω)) - rZ c)
    (hall : ∀ t : ℝ, 0 ≤ t →
      0 ≤ β t ω ∧
      (c.1.1 < π.x1 ω + π.U1 t ω - S.N t ω + qZ c * β t ω ∧
        π.x1 ω + π.U1 t ω - S.N t ω + qZ c * β t ω ≤ c.1.1 + qZ c) ∧
      qZ c ∣ π.U1 t ω - π.U1 0 ω ∧
      mZ c ∣ π.U2 t ω - π.U2 0 ω ∧
      (c.1.2.1 < π.x2 ω + π.U2 t ω - S.N t ω ∧ π.x2 ω + π.U2 t ω - S.N t ω ≤ c.1.2.1 + mZ c) ∧
      (0 < β t ω →
        (π.x2 ω + π.U2 (t - P.L2) ω - S.N t ω) - (π.x1 ω + π.U1 t ω - S.N t ω) < qZ c)) :
    FollowsAt S π c (fun t ω => π.x1 ω + π.U1 t ω - S.N t ω + qZ c * β t ω) ω := by
  unfold FollowsAt
  beta_reduce
  have hQ := qZ_pos c
  have hρ0 := rZ_nonneg c
  have hρQ := rZ_lt c
  have hL2 := P.L2_nonneg
  have hp0 : mZ c ∣ π.U2 0 ω - π.U2 (-P.L2) ω := hpipe (-P.L2) le_rfl (by linarith)

  have hW : ∀ t, 0 ≤ t →
      qZ c ∣ (π.x2 ω + π.U2 (t - P.L2) ω - (π.x1 ω + π.U1 t ω)) - rZ c := by
    intro t ht
    obtain ⟨-, -, hU1, -, -, -⟩ := hall t ht
    have hU2 : mZ c ∣ π.U2 (t - P.L2) ω - π.U2 (-P.L2) ω := by
      rcases le_or_gt 0 (t - P.L2) with h0 | h0
      · obtain ⟨-, -, -, h2, -, -⟩ := hall (t - P.L2) h0
        have := dvd_add h2 hp0
        exact dvd_of_dvd_eq this (by ring)
      · have h4 := hpipe (t - P.L2) (by linarith) h0.le
        have := dvd_sub hp0 h4
        exact dvd_of_dvd_eq this (by ring)
    have := dvd_add hrem (dvd_sub (dvd_trans (qZ_dvd_mZ c) hU2) hU1)
    exact dvd_of_dvd_eq this (by ring)
  refine ⟨?_, fun t ht => ?_⟩
  · have := dvd_sub (dvd_add hrem (dvd_trans (qZ_dvd_mZ c) hp0))
      (dvd_mul_right (qZ c) (β 0 ω))
    exact dvd_of_dvd_eq this (by ring)
  · obtain ⟨hβ0, hwin1, hU1, hU2, hwin2, hpend⟩ := hall t ht
    refine ⟨?_, hU2, hwin2, hwin1, ?_⟩
    · have := dvd_add hU1 (dvd_sub (dvd_mul_right (qZ c) (β t ω)) (dvd_mul_right (qZ c) (β 0 ω)))
      exact dvd_of_dvd_eq this (by ring)
    ·
      have hmat := π.material ω t ht
      obtain ⟨k, hk⟩ := hW t ht
      have hk0 : 0 ≤ k := by
        by_contra hneg
        push Not at hneg
        have : qZ c * k ≤ qZ c * (-1) := mul_le_mul_of_nonneg_left (by omega) hQ.le
        linarith
      rcases eq_or_lt_of_le hβ0 with hb | hb
      ·
        rw [← hb, mul_zero, add_zero]
        have : 0 ≤ qZ c * k := mul_nonneg hQ.le hk0
        rw [min_eq_left (by linarith)]
      ·
        have hlt := hpend hb
        have hk1 : k < 1 := by
          by_contra hge
          push Not at hge
          have : qZ c * 1 ≤ qZ c * k := mul_le_mul_of_nonneg_left hge hQ.le
          linarith
        have hk' : k = 0 := by omega
        rw [hk', mul_zero] at hk
        have : 0 < qZ c * β t ω := mul_pos hQ hb
        rw [min_eq_right (by linarith)]
        linarith

theorem follows_rand_of_follows (π : ShipmentPolicy P S) (c : ClassicalControls)
    (h : FollowsRnQ S π c) : FollowsRnQRand S π c.1.1 c.1.2.1 c.1.2.2.1 c.1.2.2.2.1 := by
  obtain ⟨Ihat, hgood⟩ := h
  exact ⟨fun _ => c.1.2.2.2.2, measurable_const, fun _ => c.2, Ihat, hgood⟩

theorem paper_follows_rand (π : ShipmentPolicy P S) (R1 R2 : ℤ) (Q n : ℕ+)
    (h : PaperRnQAll S π R1 R2 Q n) : FollowsRnQRand S π R1 R2 Q n := by
  obtain ⟨β, hβ⟩ := h
  set W0 : S.Ω → ℤ := fun ω => π.x2 ω + π.U2 (-P.L2) ω - (π.x1 ω + π.U1 0 ω) with hW0
  have hQ : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  set ρ : S.Ω → ℕ := fun ω => (W0 ω % ((Q : ℕ) : ℤ)).toNat with hρ
  have hρlt : ∀ ω, ρ ω < (Q : ℕ) := fun ω => by
    have h1 := Int.emod_nonneg (W0 ω) hQ.ne'
    have h2 := Int.emod_lt_of_pos (W0 ω) hQ
    simp only [hρ]
    omega
  have hρm : Measurable[S.𝓕 0] ρ := by
    have h2 : Measurable[S.𝓕 0] (π.U2 (-P.L2)) :=
      (π.U2_adapted _).mono (S.𝓕.mono (by linarith [P.L2_nonneg])) le_rfl
    have hW : Measurable[S.𝓕 0] W0 :=
      (π.x2_meas.add h2).sub (π.x1_meas.add (π.U1_adapted 0))
    exact (measurable_of_countable (fun z : ℤ => (z % ((Q : ℕ) : ℤ)).toNat)).comp hW
  refine ⟨ρ, hρm, hρlt, fun t ω => π.x1 ω + π.U1 t ω - S.N t ω + ((Q : ℕ) : ℤ) * β t ω, ?_⟩
  filter_upwards [hβ] with ω hω
  obtain ⟨hpipe, hall⟩ := hω
  have hrem : ((Q : ℕ) : ℤ) ∣ W0 ω - ((ρ ω : ℕ) : ℤ) := by
    have e : ((ρ ω : ℕ) : ℤ) = W0 ω % ((Q : ℕ) : ℤ) := by
      simp only [hρ]
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ hQ.ne')
    rw [e]
    exact ⟨W0 ω / ((Q : ℕ) : ℤ), by rw [Int.emod_def]; ring⟩
  exact paper_follows_at S π ⟨(R1, R2, Q, n, ρ ω), hρlt ω⟩ β ω hpipe hrem hall

theorem paper_rule_follows_rand_main :
    (∀ (P : Params) (S : DemandSpace P) (π : ShipmentPolicy P S) (R1 R2 : ℤ) (Q n : ℕ+),
      PaperRnQAll S π R1 R2 Q n → FollowsRnQRand S π R1 R2 Q n) ∧
    (∀ (P : Params) (S : DemandSpace P) (π : ShipmentPolicy P S) (c : ClassicalControls),
      FollowsRnQ S π c → FollowsRnQRand S π c.1.1 c.1.2.1 c.1.2.2.1 c.1.2.2.2.1) :=
  ⟨fun _ S π R1 R2 Q n h => paper_follows_rand S π R1 R2 Q n h,
    fun _ S π c h => follows_rand_of_follows S π c h⟩

end Cov

end Rule

end TwoStageRnQ

namespace TwoStageRnQ

theorem _root_.solution :
    (∀ (P : Params) (S : DemandSpace P) (π : ShipmentPolicy P S) (R1 R2 : ℤ) (Q n : ℕ+),
      RuleRand.PaperRnQAll S π R1 R2 Q n → RuleRand.FollowsRnQRand S π R1 R2 Q n) ∧
    (∀ (P : Params) (S : DemandSpace P) (π : ShipmentPolicy P S) (c : ClassicalControls),
      Rule.FollowsRnQ S π c → RuleRand.FollowsRnQRand S π c.1.1 c.1.2.1 c.1.2.2.1 c.1.2.2.2.1) :=
  Rule.paper_rule_follows_rand_main

end TwoStageRnQ
