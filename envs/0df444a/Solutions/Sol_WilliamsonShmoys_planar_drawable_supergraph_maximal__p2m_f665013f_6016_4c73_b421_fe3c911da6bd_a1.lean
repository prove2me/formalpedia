-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_supergraph_maximal__p2m_f665013f_6016_4c73_b421_fe3c911da6bd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:15:05.072531+00:00
-- url     : https://prove2.me/submissions/555fa760-2966-43d7-b48f-98f1caee5506

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter fun K =>
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K
  have hGmem : G ∈ candidates := by
    simp [candidates, hG]
  let score : SimpleGraph V → ℕ :=
    fun K => Fintype.card {p : V × V // K.Adj p.1 p.2}
  obtain ⟨M, hMmem, hMmax⟩ :=
    Finset.exists_max_image candidates score ⟨G, hGmem⟩
  have hMcandidate : G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M :=
    (Finset.mem_filter.mp hMmem).2
  refine ⟨M, hMcandidate.1, hMcandidate.2, ?_⟩
  intro K hMK hKplanar
  have hKmem : K ∈ candidates := by
    simp [candidates, le_trans hMcandidate.1 hMK, hKplanar]
  have hKM : K ≤ M := by
    intro u v hKuv
    by_contra hMnot
    have hstrict : score M < score K := by
      let f : {p : V × V // M.Adj p.1 p.2} →
          {p : V × V // K.Adj p.1 p.2} :=
        fun p => ⟨p.1, hMK p.2⟩
      have hf : Function.Injective f := by
        intro a b hab
        have hab' : a.val = b.val :=
          congrArg (fun z : {p : V × V // K.Adj p.1 p.2} => z.val) hab
        exact Subtype.ext hab'
      have hns : ¬ Function.Surjective f := by
        intro hsurj
        obtain ⟨q, hq⟩ := hsurj ⟨(u, v), hKuv⟩
        have hval : q.val = (u, v) :=
          congrArg (fun z : {p : V × V // K.Adj p.1 p.2} => z.val) hq
        apply hMnot
        have hq' : M.Adj u v := by
          simpa [hval] using q.property
        exact hq'
      dsimp [score]
      exact Fintype.card_lt_of_injective_not_surjective f hf hns
    have hle := hMmax K hKmem
    exact (not_lt_of_ge hle) hstrict
  exact hKM
