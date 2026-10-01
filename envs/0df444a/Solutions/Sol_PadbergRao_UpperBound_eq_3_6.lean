-- Prove2me | solution 1 for PadbergRao.UpperBound.eq_3_6
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:55:43.904591+00:00
-- url     : https://prove2.me/submissions/60920e57-e620-4b2c-9617-6ca9cbb768a3

import Definitions.Def_PadbergRao_UpperBound_bMatchingSystem

namespace PadbergProof
open PadbergRao.UpperBound
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem incident_sum (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (W : Finset V) :
    (∑ i ∈ W, ∑ e ∈ incidentEdges G i, x e) =
      2*(∑ e ∈ edgesWithin G W, x e)+∑ e ∈ cutEdges G W, x e := by
  classical
  simp only [incidentEdges,edgesWithin,cutEdges,Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : u ≠ v := by
      have hadj : G.Adj u v := by simpa using he
      exact hadj.ne
    have hind (i : V) : (if i ∈ s(u,v) then x s(u,v) else 0) =
        (if i=u then x s(u,v) else 0)+(if i=v then x s(u,v) else 0) := by
      simp only [Sym2.mem_iff]
      by_cases hiu : i=u <;> by_cases hiv : i=v <;> simp_all
    simp_rw [hind]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq']
    by_cases hu : u ∈ W <;> by_cases hv : v ∈ W
    all_goals simp [Sym2.mem_iff,hu,hv,huv] <;> ring

theorem slack_sum (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ)
    (x : Sym2 V → ℝ) (W : Finset V) :
    (∑ i ∈ W, slack G b x i) = (∑ i ∈ W, (b i : ℝ))-
      (2*(∑ e ∈ edgesWithin G W, x e)+∑ e ∈ cutEdges G W, x e) := by
  simp only [slack,Finset.sum_sub_distrib,incident_sum]

theorem eq36 (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V)) :
    2*(∑ e ∈ edgesWithin G W, x e)+(∑ e ∈ cutEdges G W, x e)+(∑ e ∈ T, x e)+
      (∑ i ∈ W, slack G b x i)+(∑ e ∈ T, ((d e : ℝ)-x e)) =
      (∑ i ∈ W, (b i : ℝ))+∑ e ∈ T, (d e : ℝ) := by
  rw [slack_sum,Finset.sum_sub_distrib]
  ring

theorem eq37 (G : SimpleGraph V) [DecidableRel G.Adj] (b : V → ℕ) (d : Sym2 V → ℕ)
    (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V)) :
    ((∑ i ∈ W, (b i : ℝ))+(∑ e ∈ T, (d e : ℝ))-1)/2 <
        (∑ e ∈ edgesWithin G W, x e)+∑ e ∈ T, x e ↔
      (∑ e ∈ cutEdges G W, x e)+(∑ e ∈ T, (d e : ℝ))-2*(∑ e ∈ T, x e)+
        (∑ i ∈ W, slack G b x i)<1 := by
  rw [slack_sum]
  constructor <;> intro h <;> linarith

end PadbergProof

namespace PadbergRao.UpperBound

/-- Padberg–Rao (1982), p. 75, Eq. (3.6): adding the rows of `Ax + s = b` with index in `W`
and the rows of `x + t = d` with index in `T ⊆ (W : V − W)` gives
`2x(W) + x(W : V − W) + x(T) + s(W) + t(T) = b(W) + d(T)`. -/
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V → ℕ) (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V))
    (hT : T ⊆ cutEdges G W) :
    2 * (∑ e ∈ edgesWithin G W, x e) + (∑ e ∈ cutEdges G W, x e) + (∑ e ∈ T, x e)
        + (∑ i ∈ W, slack G b x i) + (∑ e ∈ T, ((d e : ℝ) - x e))
      = (∑ i ∈ W, (b i : ℝ)) + ∑ e ∈ T, (d e : ℝ) := by
  exact PadbergProof.eq36 G b d x W T

end PadbergRao.UpperBound
