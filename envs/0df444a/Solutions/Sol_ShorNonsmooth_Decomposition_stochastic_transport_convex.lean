-- Prove2me | solution 1 for ShorNonsmooth.Decomposition.stochastic_transport_convex
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T20:06:16.178781+00:00
-- url     : https://prove2.me/submissions/f6c5d868-29f4-4b73-b139-c4bb93e688d2

import Mathlib
import Definitions.Def_ShorNonsmooth_Decomposition_StochasticTransport

-- Shared checked proof: ValueFnTransport

namespace ShorNonsmooth.Decomposition
open MeasureTheory Set
noncomputable section

lemma vf_shortage_integrable (p : ℝ → ℝ) (hp : IsDensity p)
    (hm : Integrable (fun z => z*p z)) (t : ℝ) :
    Integrable (fun z => max (z-t) 0*p z) := by
  have h := (hm.sub (hp.2.1.const_mul t)).pos_part
  convert h using 1
  funext z
  rw [max_mul_of_nonneg _ _ (hp.1 z),zero_mul]
  simp only [Pi.sub_apply]
  congr 1
  ring

lemma vf_shortage_convex (p : ℝ → ℝ) (hp : IsDensity p)
    (hm : Integrable (fun z => z*p z)) : ConvexOn ℝ univ (expectedShortage p) := by
  apply integral_convexOn_of_integrand_ae convex_univ
  · apply Filter.Eventually.of_forall
    intro z
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (z-x) 0) ha
    have h2 := mul_le_mul_of_nonneg_left (le_max_left (z-y) 0) hb
    have h0 : 0 ≤ a*max (z-x) 0+b*max (z-y) 0 :=
      add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
    have he := congrArg (fun t : ℝ => t*z) hab
    simp only [add_mul,one_mul] at he
    have hmax : max (z-(a*x+b*y)) 0 ≤ a*max (z-x) 0+b*max (z-y) 0 :=
      max_le (by nlinarith) h0
    have h := mul_le_mul_of_nonneg_right hmax (hp.1 z)
    nlinarith
  · intro t ht
    exact vf_shortage_integrable p hp hm t

lemma vf_transport_feasible_convex {m n : ℕ} (a : Fin m → ℝ) :
    Convex ℝ (stochTransportFeasible (n:=n) a) := by
  intro x hx y hy u v hu hv huv
  constructor
  · intro i
    change (∑ j, (u*x i j+v*y i j)) ≤ a i
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hx.1 i) hu
    have h2 := mul_le_mul_of_nonneg_left (hy.1 i) hv
    have he := congrArg (fun t : ℝ => t*a i) huv
    simp only [add_mul,one_mul] at he
    linarith
  · intro i j
    exact add_nonneg (mul_nonneg hu (hx.2 i j)) (mul_nonneg hv (hy.2 i j))

lemma vf_transport_convex {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (r : Fin n → ℝ) (hr : ∀ j, 0≤r j)
    (p : Fin n → ℝ → ℝ) (hp : ∀ j, IsDensity (p j))
    (hmean : ∀ j, Integrable (fun z => z*p j z)) :
    Convex ℝ (stochTransportFeasible (n:=n) a) ∧
    ConvexOn ℝ (stochTransportFeasible a) (stochTransportObjective c r p) := by
  have hset := vf_transport_feasible_convex (n:=n) a
  refine ⟨hset,hset,?_⟩
  intro x hx y hy u v hu hv huv
  have hsum : (∑ j, r j*expectedShortage (p j) (∑ i, (u*x i j+v*y i j))) ≤
      u*(∑ j, r j*expectedShortage (p j) (∑ i, x i j))+
      v*(∑ j, r j*expectedShortage (p j) (∑ i, y i j)) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left
      ((vf_shortage_convex (p j) (hp j) (hmean j)).2
        (mem_univ (∑ i,x i j)) (mem_univ (∑ i,y i j)) hu hv huv)
      (hr j)
    simp only [smul_eq_mul] at h
    nlinarith
  have hcost : (∑ i, ∑ j, c i j*(u*x i j+v*y i j))=
      u*(∑ i, ∑ j, c i j*x i j)+v*(∑ i, ∑ j, c i j*y i j) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
      apply Finset.sum_congr rfl <;> intro j hj <;> ring
  change (∑ i, ∑ j, c i j*(u*x i j+v*y i j))+
      (∑ j, r j*expectedShortage (p j) (∑ i, (u*x i j+v*y i j))) ≤
      u*((∑ i, ∑ j, c i j*x i j)+(∑ j, r j*expectedShortage (p j) (∑ i, x i j)))+
      v*((∑ i, ∑ j, c i j*y i j)+(∑ j, r j*expectedShortage (p j) (∑ i, y i j)))
  rw [hcost]
  linarith

end
end ShorNonsmooth.Decomposition

open ShorNonsmooth.Decomposition
open MeasureTheory Filter Topology

open MeasureTheory

/-- Shor (1985), **Lemma 4.3** (p. 132): the stochastic transportation problem (4.163)–(4.165) is a
convex programming problem — its feasible set is convex and its objective
`Σ c_ij x_ij + Σ r_j E(ξ_j − Σ_i x_ij)⁺` is convex on it. The demands `ξ_j` have probability densities
`p_j` with finite mean (so that the expectations are finite), and the penalty coefficients `r_j` are
nonnegative. -/
theorem solution {m n : ℕ}
    (c : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (p : Fin n → ℝ → ℝ) (hp : ∀ j, IsDensity (p j))
    (hmean : ∀ j, Integrable (fun z => z * p j z)) :
    Convex ℝ (stochTransportFeasible (n := n) a) ∧
      ConvexOn ℝ (stochTransportFeasible a) (stochTransportObjective c r p) := by
  exact vf_transport_convex c a r hr p hp hmean

#print axioms solution
