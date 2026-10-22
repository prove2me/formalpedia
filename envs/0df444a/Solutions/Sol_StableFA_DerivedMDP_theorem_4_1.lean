-- Prove2me | solution 1 for StableFA.DerivedMDP.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:28:51.72903+00:00
-- url     : https://prove2.me/submissions/e7bf83e7-9ac3-4704-b019-8dc7be63d35c

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting

set_option autoImplicit false

open StableFA.DerivedMDP

theorem qqd_key {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n) (γ : ℝ) (J : Fin n → ℝ) (i : Fin n) (u : C) :
    (derivedModel M A γ).g i u + γ * ∑ j, (derivedModel M A γ).p i u j * J j
      = M.g i u + γ * ∑ y, M.p i u y * A.apply J y := by
  simp only [derivedModel, Averager.apply]
  have h1 : ∑ j, (∑ y, M.p i u y * A.β y (some j)) * J j
      = ∑ y, M.p i u y * ∑ z, A.β y (some z) * J z := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring
  have h2 : ∑ y, M.p i u y * (A.βc y * A.k y + ∑ z, A.β y (some z) * J z)
      = ∑ y, M.p i u y * A.βc y * A.k y + ∑ y, M.p i u y * ∑ z, A.β y (some z) * J z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => by ring
  rw [h1, h2]; ring

theorem solution {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n) :
    (∀ γ : ℝ, BertsekasDiscountedBellmanOp (derivedModel M A γ) γ =
        BertsekasDiscountedBellmanOp M γ ∘ A.apply) ∧
      BertsekasSSPBellmanOp (derivedModel M A 1) = BertsekasSSPBellmanOp M ∘ A.apply := by
  constructor
  · intro γ
    funext J i
    simp only [BertsekasDiscountedBellmanOp, Function.comp]
    have hU : (derivedModel M A γ).U i = M.U i := rfl
    refine Finset.inf'_congr (M.hU i) rfl fun u _ => ?_
    exact qqd_key M A γ J i u
  · funext J i
    simp only [BertsekasSSPBellmanOp, Function.comp]
    refine Finset.inf'_congr (M.hU i) rfl fun u _ => ?_
    have := qqd_key M A 1 J i u
    simpa [one_mul] using this
