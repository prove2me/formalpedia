-- Prove2me | solution 1 for UnknownBudgetAdwords.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:23:06.099749+00:00
-- url     : https://prove2.me/submissions/ed1609b8-7a47-465d-923e-f5a448606af3

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_Spend
open MehtaOnlineAdAllocation.MSVV

theorem solution {N M : ℕ} (I : Instance N M) (τ : Allocation N M) (lamv : Fin M → ℝ) (thetav : Fin N → ℝ) (ALG α ε : ℝ) (hε : 0 < 1 + ε) (h1 : ∑ t, lamv t + ∑ i, thetav i ≤ (1 + ε) * ALG) (h2 : ∀ i, α * spend I τ i M ≤ thetav i + ∑ t ∈ Finset.univ.filter (fun t => τ t = some i), lamv t) (h3 : (∀ t, 0 ≤ lamv t) ∧ ∀ i, 0 ≤ thetav i) : α / (1 + ε) * revenue I τ ≤ ALG := by
  have key : ∑ i, ∑ t ∈ Finset.univ.filter (fun t => τ t = some i), lamv t ≤ ∑ t, lamv t := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t _
    cases h : τ t with
    | none => simp [h3.1 t]
    | some j => simp
  have hs : α * revenue I τ ≤ ∑ i, thetav i +
      ∑ i, ∑ t ∈ Finset.univ.filter (fun t => τ t = some i), lamv t := by
    unfold revenue
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => h2 i)
  rw [div_mul_eq_mul_div, div_le_iff₀ hε]
  linarith
