-- Prove2me | solution 1 for PadbergRao.UpperBound.eq_3_7
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:55:44.675496+00:00
-- url     : https://prove2.me/submissions/4d545a9d-df86-4670-ae6b-cbe5d0c9a221

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

/-- Padberg–Rao (1982), p. 75, Eq. (3.7): for `T ⊆ (W : V − W)`, the point `x̄` violates the
blossom inequality (3.3), `x̄(W) + x̄(T) > ½(b(W) + d(T) − 1)`, if and only if
`x̄(W : V − W) + d(T) − 2x̄(T) + s̄(W) < 1`. -/
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V → ℕ) (d : Sym2 V → ℕ) (x : Sym2 V → ℝ) (W : Finset V) (T : Finset (Sym2 V))
    (hT : T ⊆ cutEdges G W) :
    ((∑ i ∈ W, (b i : ℝ)) + (∑ e ∈ T, (d e : ℝ)) - 1) / 2
        < (∑ e ∈ edgesWithin G W, x e) + ∑ e ∈ T, x e ↔
      (∑ e ∈ cutEdges G W, x e) + (∑ e ∈ T, (d e : ℝ)) - 2 * (∑ e ∈ T, x e)
        + (∑ i ∈ W, slack G b x i) < 1 := by
  exact PadbergProof.eq37 G b d x W T

end PadbergRao.UpperBound
