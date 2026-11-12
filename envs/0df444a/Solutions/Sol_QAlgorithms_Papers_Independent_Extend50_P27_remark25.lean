-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P27.remark25
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:16:46.280862+00:00
-- url     : https://prove2.me/submissions/915e8f11-c480-4d0c-b8ea-c122dfa083d3

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

namespace Aux_P27_remark25

theorem colLen_le_card (μ : YoungDiagram) : μ.colLen 0 ≤ μ.card := by
  rw [YoungDiagram.colLen_eq_card]
  exact Finset.card_filter_le _ _

end Aux_P27_remark25

open QAlgorithms.Papers.Independent.Extend50.P27 in
theorem solution {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    ∃ (rows : Partition d (N-1) ↪ Partition N (N-1))
      (cols : Partition d N ↪ Partition N N),
      (∀ alpha, (rows alpha).val = alpha.val) ∧ (∀ mu, (cols mu).val = mu.val) ∧
      incidence d N = (incidence N N).submatrix rows cols := by
  refine ⟨⟨fun a => ⟨a.val, a.2.1, by
      have h1 := Aux_P27_remark25.colLen_le_card a.val
      have h2 := a.2.1
      omega⟩, ?_⟩,
    ⟨fun m => ⟨m.val, m.2.1, by
      have h1 := Aux_P27_remark25.colLen_le_card m.val
      have h2 := m.2.1
      omega⟩, ?_⟩, fun _ => rfl, fun _ => rfl, ?_⟩
  · intro a b h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  · intro a b h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  · ext a m
    rfl

end
