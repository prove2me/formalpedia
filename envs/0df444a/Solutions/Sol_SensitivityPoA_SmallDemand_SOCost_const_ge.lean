-- Prove2me | solution 1 for SensitivityPoA.SmallDemand.SOCost_const_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:59:32.006733+00:00
-- url     : https://prove2.me/submissions/cf60ef31-363f-45c9-ada4-f97a6b17d6e4

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting

set_option autoImplicit false

open SensitivityPoA.SmallDemand KellyStochasticNetworks

theorem solution (N : Network) (hN : N.Standing) (τ : Fin N.J → ℝ → ℝ)
    (hpos : ∀ j, 0 < τ j 0) (τmin : ℝ) (hτmin : IsLeast (Set.range fun j => τ j 0) τmin)
    (d : Fin N.Sd → ℝ) (hd : ∀ k, 0 ≤ d k) (hT : 0 < totalDemand d) :
    τmin ≤ SOCost (⟨fun j _ => τ j 0, fun k => d k / totalDemand d⟩ : Game N) := by
  classical
  obtain ⟨hA01, hAroute, -, -, hcard⟩ := hN
  have hAnn : ∀ j r, 0 ≤ N.A j r := fun j r => by rcases hA01 j r with h | h <;> simp [h]
  have hτm : 0 < τmin := by
    obtain ⟨⟨j, hj⟩, -⟩ := hτmin
    rw [← hj]; exact hpos j
  set Γ : Game N := ⟨fun j _ => τ j 0, fun k => d k / totalDemand d⟩ with hΓ
  unfold SOCost
  apply le_csInf
  · -- nonempty: a feasible flow
    have hrep : ∀ σ : Fin N.Sd, ∃ r, N.s r = σ := fun σ => by
      have := hcard σ
      have h0 : 0 < (Finset.univ.filter fun r => N.s r = σ).card := by omega
      obtain ⟨r, hr⟩ := Finset.card_pos.mp h0
      exact ⟨r, (Finset.mem_filter.mp hr).2⟩
    choose rep hrep using hrep
    refine ⟨cost Γ (fun r => if r = rep (N.s r) then d (N.s r) / totalDemand d else 0), ?_⟩
    refine ⟨_, ?_, rfl⟩
    show (fun r => if r = rep (N.s r) then d (N.s r) / totalDemand d else 0) ∈ wardropFeasible N.s Γ.d
    refine ⟨fun r => ?_, fun σ => ?_⟩
    · dsimp only
      split_ifs
      · exact div_nonneg (hd _) hT.le
      · exact le_rfl
    · have : ∀ r ∈ Finset.univ.filter (fun r => N.s r = σ),
          (if r = rep (N.s r) then d (N.s r) / totalDemand d else 0)
            = if r = rep σ then d σ / totalDemand d else 0 := by
        intro r hr
        have := (Finset.mem_filter.mp hr).2
        subst this
        rfl
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      simp [hrep σ, Γ]
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨hf0, hfs⟩ := hf
    have hy0 : ∀ j, 0 ≤ linkFlow N.A f j := fun j =>
      Finset.sum_nonneg fun r _ => mul_nonneg (hAnn j r) (hf0 r)
    have hsumf : ∑ r, f r = 1 := by
      have h1 : ∑ r, f r = ∑ σ, ∑ r ∈ Finset.univ.filter (fun r => N.s r = σ), f r :=
        (Finset.sum_fiberwise Finset.univ N.s f).symm
      rw [h1]
      have : ∀ σ ∈ (Finset.univ : Finset (Fin N.Sd)),
          ∑ r ∈ Finset.univ.filter (fun r => N.s r = σ), f r = d σ / totalDemand d :=
        fun σ _ => hfs σ
      rw [Finset.sum_congr rfl this, ← Finset.sum_div]
      exact div_self hT.ne'
    have hsumy : 1 ≤ ∑ j, linkFlow N.A f j := by
      unfold linkFlow
      rw [Finset.sum_comm]
      calc (1 : ℝ) = ∑ r, f r := hsumf.symm
        _ ≤ ∑ r, ∑ j, N.A j r * f r := by
          apply Finset.sum_le_sum
          intro r _
          obtain ⟨j0, hj0⟩ := hAroute r
          calc f r = N.A j0 r * f r := by rw [hj0, one_mul]
            _ ≤ ∑ j, N.A j r * f r :=
              Finset.single_le_sum (f := fun j => N.A j r * f r)
                (fun j _ => mul_nonneg (hAnn j r) (hf0 r)) (Finset.mem_univ j0)
    show τmin ≤ ∑ j, linkFlow N.A f j * τ j 0
    calc τmin = τmin * 1 := (mul_one _).symm
      _ ≤ τmin * ∑ j, linkFlow N.A f j := mul_le_mul_of_nonneg_left hsumy hτm.le
      _ = ∑ j, τmin * linkFlow N.A f j := Finset.mul_sum _ _ _
      _ ≤ ∑ j, linkFlow N.A f j * τ j 0 := by
        apply Finset.sum_le_sum
        intro j _
        have := hτmin.2 ⟨j, rfl⟩
        nlinarith [hy0 j]
