-- Prove2me | solution 1 for WilliamsonShmoys.finite_property_maximal_extension__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:32:23.706593+00:00
-- url     : https://prove2.me/submissions/7934866c-97af-42c4-a5e1-ab45edf48d6a

-- ID: 6fac8935-626c-453a-b732-3699a8acdf35 | NAME: WilliamsonShmoys.finite_property_maximal_extension__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1 | 未本地编译验证
import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) (hsub : ∀ ⦃A B : SimpleGraph V⦄, P B → A ≤ B → P A) : ∃ T : SimpleGraph V, P T ∧ G ≤ T ∧ ∀ K : SimpleGraph V, P K → T ≤ K → K ≤ T := by
  classical
  let p : SimpleGraph V → Prop := fun H => P H ∧ G ≤ H
  have hpG : p G := ⟨hG, le_rfl⟩
  obtain ⟨T, hGT, hmax⟩ :=
    (Finite.exists_le_maximal (α := SimpleGraph V) (p := p) (a := G) hpG)
  rcases hmax with ⟨hpT, hmax'⟩
  refine ⟨T, hpT.1, hGT, ?_⟩
  intro K hPK hTK
  exact hmax' ⟨hPK, hGT.trans hTK⟩ hTK
