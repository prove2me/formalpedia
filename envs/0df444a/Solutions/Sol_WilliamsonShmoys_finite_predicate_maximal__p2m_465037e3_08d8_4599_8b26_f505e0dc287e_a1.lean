-- Prove2me | solution 1 for WilliamsonShmoys.finite_predicate_maximal__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:43:00.051746+00:00
-- url     : https://prove2.me/submissions/28cc3a30-584f-4765-bf1b-bb3f16029c38

import Mathlib

theorem solution
    {α : Type} [Fintype α]
    (R : α → α → Prop)
    (m : α → Nat)
    (hstrict : ∀ a b : α, R a b → a ≠ b → m a < m b)
    (P : α → Prop)
    (a₀ : α)
    (ha₀ : P a₀) :
    ∃ a : α, P a ∧ ∀ b : α, R a b → P b → b = a := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := ⟨a₀, by simp [s, ha₀]⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s m hs
  have hPa : P a := by simpa [s] using ha
  refine ⟨a, hPa, ?_⟩
  intro b hab hPb
  have hbm : m b ≤ m a := hmax b (by simp [s, hPb])
  by_cases hba : b = a
  · exact hba
  · have hlt : m a < m b := hstrict a b hab (Ne.symm hba)
    omega
