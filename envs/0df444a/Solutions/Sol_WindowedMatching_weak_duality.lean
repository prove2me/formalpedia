-- Prove2me | solution 1 for WindowedMatching.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:24:49.665642+00:00
-- url     : https://prove2.me/submissions/f0b5d17b-8768-41fc-a42b-47d55b610dfc

import Definitions.Def_ProphetMatchingEFGT_MatchingModel

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : ProphetMatchingEFGT.Edge G → ℝ) (lam : V → ℝ)
    (hlam : ∀ a, 0 ≤ lam a)
    (hfeas : ∀ (a b : V) (hab : G.Adj a b), w ⟨s(a, b), hab⟩ ≤ lam a + lam b) :
    ProphetMatchingEFGT.optWeight G w ≤ ∑ a, lam a := by
  classical
  unfold ProphetMatchingEFGT.optWeight
  apply Finset.sup'_le
  intro M hM
  have hMm : ProphetMatchingEFGT.IsMatching G M := by
    simpa [ProphetMatchingEFGT.matchings] using hM
  unfold ProphetMatchingEFGT.weightOf
  have hedge : ∀ e : ProphetMatchingEFGT.Edge G,
      w e ≤ ∑ x, if x ∈ (e : Sym2 V) then lam x else 0 := by
    rintro ⟨e, he⟩
    revert he
    refine Sym2.ind (fun a b => ?_) e
    intro he
    have hab : G.Adj a b := by simpa using he
    have hne : a ≠ b := G.ne_of_adj hab
    have hsum : (∑ x, if x ∈ s(a, b) then lam x else 0) = lam a + lam b := by
      rw [← Finset.sum_filter]
      have hf : Finset.univ.filter (fun x => x ∈ s(a, b)) = {a, b} := by
        ext x
        simp [Sym2.mem_iff]
      rw [hf, Finset.sum_pair hne]
    show w ⟨s(a, b), he⟩ ≤ ∑ x, if x ∈ s(a, b) then lam x else 0
    rw [hsum]
    exact hfeas a b hab
  have hx : ∀ x, ∑ e ∈ M, (if x ∈ (e : Sym2 V) then lam x else 0) ≤ lam x := by
    intro x
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : (M.filter fun e : ProphetMatchingEFGT.Edge G => x ∈ (e : Sym2 V)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro e he f hf
      simp only [Finset.mem_filter] at he hf
      by_contra hne
      exact hMm e he.1 f hf.1 hne x he.2 hf.2
    have hc' : ((M.filter fun e : ProphetMatchingEFGT.Edge G => x ∈ (e : Sym2 V)).card : ℝ)
        ≤ 1 := by exact_mod_cast hc
    exact mul_le_of_le_one_left (hlam x) hc'
  calc ∑ e ∈ M, w e
      ≤ ∑ e ∈ M, ∑ x, (if x ∈ (e : Sym2 V) then lam x else 0) :=
        Finset.sum_le_sum (fun e _ => hedge e)
    _ = ∑ x, ∑ e ∈ M, (if x ∈ (e : Sym2 V) then lam x else 0) := Finset.sum_comm
    _ ≤ ∑ x, lam x := Finset.sum_le_sum (fun x _ => hx x)
