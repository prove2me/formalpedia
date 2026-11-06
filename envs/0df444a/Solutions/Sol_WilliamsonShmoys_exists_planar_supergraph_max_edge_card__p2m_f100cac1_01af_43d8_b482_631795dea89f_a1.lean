-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:29:52.965878+00:00
-- url     : https://prove2.me/submissions/9af761eb-7379-4eff-ad07-b23aa7ba0b27

-- ID: 69ec58a5-aab3-4dc7-a449-f1759fd682d8 | NAME: WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1 | 未本地编译验证
import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option linter.unusedVariables false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ ∀ S : SimpleGraph V, Q ≤ S → HasPlanarDrawingOn S → Nat.card {e : Sym2 V // e ∈ S.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ R.edgeSet} := by
  classical
  let s : Set (SimpleGraph V) := {N | Q ≤ N ∧ HasPlanarDrawingOn N}
  have hsne : s.Nonempty := ⟨Q, by simp [s, hDraw]⟩
  have hsfinite : s.Finite := s.toFinite
  obtain ⟨R, hRs, hmax⟩ :=
    Set.exists_max_image s (fun N : SimpleGraph V => Nat.card {e : Sym2 V // e ∈ N.edgeSet}) hsfinite hsne
  have hRs' : Q ≤ R ∧ HasPlanarDrawingOn R := by simpa [s] using hRs
  refine ⟨R, hRs'.1, hRs'.2, ?_⟩
  intro S hQS hS
  exact hmax S (by simpa [s] using (show Q ≤ S ∧ HasPlanarDrawingOn S from ⟨hQS, hS⟩))
