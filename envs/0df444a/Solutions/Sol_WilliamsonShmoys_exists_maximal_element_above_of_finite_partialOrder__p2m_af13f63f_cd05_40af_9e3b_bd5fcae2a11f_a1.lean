-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_element_above_of_finite_partialOrder__p2m_af13f63f_cd05_40af_9e3b_bd5fcae2a11f_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:17:33.879848+00:00
-- url     : https://prove2.me/submissions/af3aa663-6c66-4ee0-ac01-c11540f2bbfc

import Mathlib

theorem solution {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop)
    (a : α) (ha : P a) :
    ∃ m : α, a ≤ m ∧ P m ∧ ∀ n : α, m ≤ n → P n → n = m := by
  let p : α → Prop := fun x => a ≤ x ∧ P x
  have hpa : p a := ⟨le_rfl, ha⟩
  obtain ⟨m, ham, hmmax⟩ :=
    (Finite.exists_le_maximal (α := α) (p := p) (a := a) hpa)
  rcases hmmax with ⟨hmP, hmmax'⟩
  refine ⟨m, ham, hmP.2, ?_⟩
  intro n hmn hPn
  have hpn : p n := ⟨ham.trans hmn, hPn⟩
  exact (le_antisymm hmn (hmmax' hpn hmn)).symm
