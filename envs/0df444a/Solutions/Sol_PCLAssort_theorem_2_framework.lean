-- Prove2me | solution 1 for PCLAssort.theorem_2_framework
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:06:03.818676+00:00
-- url     : https://prove2.me/submissions/9850085d-a96a-4fea-bb4f-e715f9c23923

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_DownwardClosed
import Definitions.Def_PCLAssort_revenue
import Definitions.Def_PCLAssort_hz
import Definitions.Def_PCLAssort_optRevenue
import Definitions.Def_PCLAssort_fValue

open PCLAssort in
theorem solution {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n)))
    (hF : DownwardClosed F) (g : ℝ → ℝ) (hg : ∀ z, fValue I F z ≤ g z)
    (zhat : ℝ) (hzhat : 0 ≤ zhat) (hfix : g zhat = I.v0 * zhat)
    (xhat : Finset (Fin n)) (hxhat : xhat ∈ F) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hstep3 : α * g zhat ≤ hz I zhat xhat) :
    α * zhat ≤ revenue I xhat ∧ α * optRevenue I F ≤ α * zhat ∧
      optRevenue I F ≤ zhat ∧ α * optRevenue I F ≤ revenue I xhat := by
  have hv0 := I.v0_pos
  have hw : ∀ S i j, 0 ≤ nestWeight I S i j := by
    intro S i j
    unfold nestWeight
    have a1 := Real.rpow_nonneg (I.v_nonneg i) (1 / I.γ i j)
    have a2 := Real.rpow_nonneg (I.v_nonneg j) (1 / I.γ i j)
    split_ifs <;> nlinarith
  have hD : ∀ S, 0 ≤ ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
      nestWeight I S p.1 p.2 ^ I.γ p.1 p.2 :=
    fun S => Finset.sum_nonneg (fun p _ => Real.rpow_nonneg (hw _ _ _) _)
  have hzeq : ∀ z S, hz I z S =
      (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        nestWeight I S p.1 p.2 ^ I.γ p.1 p.2 * nestRevenue I S p.1 p.2) -
      z * ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, nestWeight I S p.1 p.2 ^ I.γ p.1 p.2 := by
    intro z S
    unfold hz
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hrev : ∀ S, revenue I S =
      (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        nestWeight I S p.1 p.2 ^ I.γ p.1 p.2 * nestRevenue I S p.1 p.2) /
      (I.v0 + ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, nestWeight I S p.1 p.2 ^ I.γ p.1 p.2) :=
    fun S => rfl
  -- part (1)
  have p1 : α * zhat ≤ revenue I xhat := by
    rw [hrev, le_div_iff₀ (by linarith [hD xhat])]
    rw [hfix, hzeq] at hstep3
    have := hD xhat
    have h1 : α * zhat * (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        nestWeight I xhat p.1 p.2 ^ I.γ p.1 p.2) ≤ zhat * (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        nestWeight I xhat p.1 p.2 ^ I.γ p.1 p.2) := by
      have := mul_nonneg hzhat (hD xhat)
      nlinarith
    nlinarith
  -- part (3)
  have p3 : optRevenue I F ≤ zhat := by
    haveI : Nonempty F := ⟨⟨∅, hF.1⟩⟩
    unfold optRevenue
    apply ciSup_le
    rintro ⟨S, hS⟩
    have hbdd : BddAbove (Set.range fun S : F => hz I zhat S.1) := (Set.finite_range _).bddAbove
    have h1 : hz I zhat S ≤ fValue I F zhat := le_ciSup hbdd ⟨S, hS⟩
    have h2 := hg zhat
    rw [hfix] at h2
    rw [hzeq] at h1
    show revenue I S ≤ zhat
    rw [hrev, div_le_iff₀ (by linarith [hD S])]
    nlinarith
  have p2 : α * optRevenue I F ≤ α * zhat := mul_le_mul_of_nonneg_left p3 hα0
  exact ⟨p1, p2, p3, p2.trans p1⟩
