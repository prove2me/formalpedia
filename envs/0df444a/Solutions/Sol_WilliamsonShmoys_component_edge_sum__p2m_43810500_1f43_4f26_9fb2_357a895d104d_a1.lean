-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_sum__p2m_43810500_1f43_4f26_9fb2_357a895d104d_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-02T11:56:04.856139+00:00
-- url     : https://prove2.me/submissions/ac98969b-22ad-40c6-8288-0228e7c064f0

import Mathlib
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
        (C : Finset (Finset V)),
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
         (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
            Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) →
         (∀ v : V, ∃ B ∈ C, v ∈ B) →
         N.edgeFinset.card =
           ∑ B ∈ C,
             (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _;
              (N.induce (↑B : Set V)).edgeFinset.card))) := by
  intro h
  let N : SimpleGraph Bool := ⊤
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  let C : Finset (Finset Bool) := {{false}, {true}}
  have hdis : ∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
      Disjoint (↑B₁ : Set Bool) (↑B₂ : Set Bool) := by
    intro B₁ hB₁ B₂ hB₂ hne
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at hB₁ hB₂
    rcases hB₁ with hB₁ | hB₁ <;> rcases hB₂ with hB₂ | hB₂ <;>
      subst_vars <;> simp_all [Set.disjoint_left]
  have hcov : ∀ v : Bool, ∃ B ∈ C, v ∈ B := by
    intro v
    cases v <;> simp [C]
  have hEq := h N C hdis hcov
  have he : Sym2.mk false true ∈ N.edgeFinset := by
    simp [N, SimpleGraph.mem_edgeFinset]
  have hpos : 0 < N.edgeFinset.card := Finset.card_pos.mpr ⟨_, he⟩
  have hsingle (b : Bool) :
      (letI : Fintype {v // v ∈ (↑({b} : Finset Bool) : Set Bool)} := Fintype.ofFinite _; (N.induce (↑({b} : Finset Bool) : Set Bool)).edgeFinset.card) = 0 := by
    have hempty : N.induce (↑({b} : Finset Bool) : Set Bool) = ⊥ := by
      ext x y
      constructor
      · intro hadj
        have hx : x.val = b := Finset.mem_singleton.mp x.property
        have hy : y.val = b := Finset.mem_singleton.mp y.property
        have hxy : x = y := Subtype.ext (hx.trans hy.symm)
        subst y
        change N.Adj x.val x.val at hadj
        exact N.irrefl hadj
      · intro hadj
        exact hadj.elim
    simp [hempty]
  have hsum :
      (∑ B ∈ C,
        (letI : Fintype {v // v ∈ (↑B : Set Bool)} := Fintype.ofFinite _;
         (N.induce (↑B : Set Bool)).edgeFinset.card)) = 0 := by
    apply Finset.sum_eq_zero
    intro B hB
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with hB | hB
    case inl =>
      subst B
      exact hsingle false
    case inr =>
      subst B
      exact hsingle true
  rw [hsum] at hEq
  omega


