-- Prove2me | solution 1 for WilliamsonShmoys.finite_face_data_of_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:31:48.152524+00:00
-- url     : https://prove2.me/submissions/45c75f82-6b06-4e1e-96a7-83694797b69e

import Definitions.Def_WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hlo : Fintype.card V ≤ K.edgeSet.ncard + 1)
    (hhi : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6) :
    Nonempty (WilliamsonShmoys.PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 K) := by
  let n : ℕ := Fintype.card V
  let m : ℕ := K.edgeSet.ncard
  let f : ℕ := m + 2 - n
  let d : ℕ := 2 * m - 3 * f
  have hn : n ≤ m + 1 := by
    dsimp [n, m]
    exact hlo
  have hm : m + 6 ≤ 3 * n := by
    dsimp [n, m] at hhi ⊢
    omega
  have hf : 0 < f := by
    dsimp [f]
    omega
  have hd : 3 * f ≤ 2 * m := by
    dsimp [f]
    omega
  classical
  refine ⟨{
    Faces__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 := Fin f
    faceLength__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 :=
      fun i => 3 + if i.val = 0 then d else 0
    euler__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 := ?_
    incidence__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 := ?_
    lower__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 := ?_
  }⟩
  · change n + Fintype.card (Fin f) = m + 2
    simp only [Fintype.card_fin]
    dsimp [f]
    omega
  · have hdelta : (∑ i : Fin f, (if i.val = 0 then d else 0)) = d := by
      rw [Finset.sum_eq_single (⟨0, hf⟩ : Fin f)]
      · simp
      · intro b hb hne
        have hbzero : b.val ≠ 0 := by
          intro hzero
          apply hne
          apply Fin.ext
          exact hzero
        simp [hbzero]
      · simp
    calc
      (∑ i : Fin f, (3 + if i.val = 0 then d else 0)) =
          (∑ i : Fin f, 3) + d := by
            rw [Finset.sum_add_distrib, hdelta]
      _ = f * 3 + d := by simp
      _ = 2 * K.edgeSet.ncard := by
        dsimp [d, f, m, n]
        omega
  · intro i
    split <;> omega
