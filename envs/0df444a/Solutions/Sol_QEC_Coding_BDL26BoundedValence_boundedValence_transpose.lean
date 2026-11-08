-- Prove2me | solution 1 for QEC.Coding.BDL26BoundedValence.boundedValence_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:44:04.487499+00:00
-- url     : https://prove2.me/submissions/77d25eee-418d-45e6-b22e-8cd844586d31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValence

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26BoundedValence
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
namespace QEC.Coding.BDL26BoundedValence
theorem _root_.solution (P : TannerSquarePresentation)
    (h : BoundedValence P) : BoundedValence (transposePresentation P) := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro q
  obtain ⟨hx, hz, hsum⟩ := h.2.2 q
  refine ⟨hz, hx, ?_⟩
  change qZDegree P q + qXDegree P q ≤ 7
  omega
end QEC.Coding.BDL26BoundedValence
