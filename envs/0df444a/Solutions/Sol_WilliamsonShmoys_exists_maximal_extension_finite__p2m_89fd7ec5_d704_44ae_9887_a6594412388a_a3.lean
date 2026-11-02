-- Prove2me | solution 1 for WilliamsonShmoys.exists_maximal_extension_finite__p2m_89fd7ec5_d704_44ae_9887_a6594412388a_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:26:20.256901+00:00
-- url     : https://prove2.me/submissions/1e1b3736-1c18-481e-8df3-39c3bbf50c79

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V -> Prop)
    (K : SimpleGraph V)
    (hK : P K) :
    Exists fun H : SimpleGraph V => And (LE.le K H)
      (And (P H) (∀ J : SimpleGraph V, LE.le H J -> P J -> LE.le J H)) := by
  classical
  let S : Set (SimpleGraph V) := {H | K ≤ H ∧ P H}
  have hSfinite : S.Finite := Set.finite_univ.subset (Set.subset_univ S)
  have hSnonempty : S.Nonempty := ⟨K, le_rfl, hK⟩
  obtain ⟨H, hHmem, hHmax⟩ := hSfinite.exists_maximal hSnonempty
  refine ⟨H, hHmem.1, hHmem.2, ?_⟩
  intro J hHJ hPJ
  exact hHmax ⟨hHmem.1.trans hHJ, hPJ⟩ hHJ