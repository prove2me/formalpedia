-- Prove2me | solution 1 for RefDemandLearning.SlowMoving.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:38:36.578992+00:00
-- url     : https://prove2.me/submissions/08113a8d-83e0-45e8-8c5e-441c852093eb

import Definitions.Def_RefDemandLearning_SlowMoving_Mechanism
set_option autoImplicit false
namespace RefDemandLearning.SlowMoving

theorem rd_err_geom (I : PriceInterval) (ρ : Mechanism I) (ζ : ℝ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1)
    (hES : ∀ (p : ℕ → Price I) (n : ℕ),
      reference ρ p (n + 1) = ζ * reference ρ p n + (1 - ζ) * (p n : ℝ))
    (s : ℕ) (h : Fin s → Price I) (p : Price I) (k : ℕ) :
    |reference ρ (heldPath s h p) (s + k) - (p : ℝ)| ≤ ζ ^ k * (I.hi - I.lo) := by
  induction k with
  | zero =>
    have h1 : (I.lo : ℝ) ≤ reference ρ (heldPath s h p) s := (ρ.ref s _).2.1
    have h2 : reference ρ (heldPath s h p) s ≤ I.hi := (ρ.ref s _).2.2
    have h3 := p.2.1
    have h4 := p.2.2
    simp only [pow_zero, one_mul, add_zero]
    rw [abs_le]
    constructor <;> linarith
  | succ k ih =>
    have e1 := hES (heldPath s h p) (s + k)
    have e2 : ((heldPath s h p (s + k) : Price I) : ℝ) = p := by
      simp [heldPath]
    rw [e2] at e1
    have e3 : reference ρ (heldPath s h p) (s + (k + 1)) - (p : ℝ) =
        ζ * (reference ρ (heldPath s h p) (s + k) - (p : ℝ)) := by
      rw [← add_assoc, e1]; ring
    rw [e3, abs_mul, abs_of_nonneg hζ0, pow_succ]
    calc ζ * |reference ρ (heldPath s h p) (s + k) - (p : ℝ)| ≤ ζ * (ζ ^ k * (I.hi - I.lo)) :=
          mul_le_mul_of_nonneg_left ih hζ0
      _ = ζ ^ k * ζ * (I.hi - I.lo) := by ring

end RefDemandLearning.SlowMoving

open RefDemandLearning.SlowMoving

theorem solution (I : PriceInterval) (ρ : Mechanism I) (hρ : IsES ρ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ s t : ℕ, 1 ≤ s → s < t →
      ∀ (h : Fin s → Price I) (p : Price I), trackingError ρ s t h p ≤ c₂ := by
  obtain ⟨ζ, hζ0, hζ1, hES⟩ := hρ
  have hw : 0 < I.hi - I.lo := sub_pos.2 I.lt
  have h1z : 0 < 1 - ζ := sub_pos.2 hζ1
  refine ⟨(I.hi - I.lo) / (1 - ζ) + 1, by positivity, ?_⟩
  intro s t _ hst h p
  unfold trackingError
  have hsum : ∑ n ∈ Finset.Ico s t, |reference ρ (heldPath s h p) n - (p : ℝ)| ≤
      ∑ k ∈ Finset.range (t - s), ζ ^ k * (I.hi - I.lo) := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_le_sum (fun k _ => RefDemandLearning.SlowMoving.rd_err_geom I ρ ζ hζ0 hζ1 hES s h p k)
  have hgeo : ∑ k ∈ Finset.range (t - s), ζ ^ k * (I.hi - I.lo) ≤ (I.hi - I.lo) / (1 - ζ) := by
    rw [← Finset.sum_mul]
    have hg : (∑ k ∈ Finset.range (t - s), ζ ^ k) * (1 - ζ) = 1 - ζ ^ (t - s) := by
      rw [mul_comm]; exact mul_neg_geom_sum ζ (t - s)
    have hz : 0 ≤ ζ ^ (t - s) := pow_nonneg hζ0 _
    have : ∑ k ∈ Finset.range (t - s), ζ ^ k ≤ 1 / (1 - ζ) := by
      rw [le_div_iff₀ h1z]; linarith
    calc (∑ k ∈ Finset.range (t - s), ζ ^ k) * (I.hi - I.lo) ≤ (1 / (1 - ζ)) * (I.hi - I.lo) :=
          mul_le_mul_of_nonneg_right this hw.le
      _ = (I.hi - I.lo) / (1 - ζ) := by ring
  linarith

