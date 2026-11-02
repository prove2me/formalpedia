-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_supergraph_has_maximal_extension__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:11:42.585553+00:00
-- url     : https://prove2.me/submissions/7f9e31cd-981e-4784-993f-ffa9766f482c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      letI : DecidableRel G.Adj := dG
      letI : DecidableRel H.Adj := dH
      HasPlanarDrawingOn H ∧
      G.edgeFinset ⊆ H.edgeFinset ∧
      ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        letI : DecidableRel H.Adj := dH
        letI : DecidableRel K.Adj := dK
        HasPlanarDrawingOn K →
        H.edgeFinset ⊆ K.edgeFinset →
        K.edgeFinset = H.edgeFinset := by
  classical
  letI : DecidableRel G.Adj := dG
  let P : SimpleGraph V → Prop := fun X =>
    HasPlanarDrawingOn X ∧ G.edgeFinset ⊆ X.edgeFinset
  have hPG : P G := by
    refine ⟨hG, ?_⟩
    intro e he
    simpa using he
  let S := {X : SimpleGraph V // P X}
  letI : Nonempty S := ⟨⟨G, hPG⟩⟩
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset S)
      (fun y : S => y.val.edgeFinset.card) (by simp)
  let H := x.val
  let dH : DecidableRel H.Adj := Classical.decRel H.Adj
  have hPH : P H := x.property
  rcases hPH with ⟨hHdraw, hGH⟩
  refine ⟨H, dH, hHdraw, ?_, ?_⟩
  · intro e he
    simpa [H] using hGH (by simpa using he)
  · intro K dK
    letI : DecidableRel H.Adj := dH
    letI : DecidableRel K.Adj := dK
    intro hKdraw hHK
    have hHK' : H.edgeFinset ⊆ K.edgeFinset := by
      intro e he
      simpa using hHK he
    have hGK : G.edgeFinset ⊆ K.edgeFinset := by
      intro e he
      have heH : e ∈ H.edgeFinset := hGH (by simpa using he)
      have heK : e ∈ K.edgeFinset := hHK' heH
      simpa using heK
    have hPK : P K := by
      refine ⟨hKdraw, ?_⟩
      intro e he
      have heK : e ∈ K.edgeFinset := hGK he
      simpa using heK
    have hmaxK := hmax ⟨K, hPK⟩ (by simp)
    have hKedge :
        @SimpleGraph.edgeFinset V K
            (by
              letI : DecidableRel K.Adj := Classical.decRel K.Adj
              infer_instance) =
          @SimpleGraph.edgeFinset V K
            (by
              letI : DecidableRel K.Adj := dK
              infer_instance) := by
      ext e
      simp
    have hcardK : K.edgeFinset.card ≤ H.edgeFinset.card := by
      rw [← hKedge]
      simpa [H] using hmaxK
    have hsets : H.edgeFinset = K.edgeFinset :=
      Finset.eq_of_subset_of_card_le hHK' hcardK
    simpa using hsets.symm
