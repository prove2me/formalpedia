-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.multilinear_diagonal_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:37:46.598166+00:00
-- url     : https://prove2.me/submissions/6fb2cdb8-6d86-4ec3-813d-6b0d1e926760

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR
open Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR
theorem _root_.solution {n a : ℕ} (D : ContinuousMultilinearMap ℂ (fun _ : Fin a => V n) ℂ) :
    ∃ b : (Fin n → ℕ) → ℂ, ∀ u : V n,
      D (fun _ => u) = ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, u k ^ α k := by
  classical
  let cnt : (Fin a → Fin n) → Fin n → ℕ := fun r k => (Finset.univ.filter fun i => r i = k).card
  refine ⟨fun α => ∑ r ∈ Finset.univ.filter (fun r => cnt r = α),
    D (fun i => EuclideanSpace.single (r i) (1 : ℂ)), fun u => ?_⟩
  have hu : u = ∑ k, u k • EuclideanSpace.single k (1 : ℂ) := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr u).symm
  have h1 : D (fun _ => u) =
      ∑ r : Fin a → Fin n, (∏ i, u (r i)) * D (fun i => EuclideanSpace.single (r i) (1 : ℂ)) := by
    have e1 : (fun _ : Fin a => u) = fun _ => ∑ k, u k • EuclideanSpace.single k (1 : ℂ) := by
      rw [← hu]
    rw [e1, D.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [D.map_smul_univ (fun i => u (r i)) (fun i => EuclideanSpace.single (r i) (1 : ℂ)), smul_eq_mul]
  have h2 : ∀ r : Fin a → Fin n, ∏ i, u (r i) = ∏ k, u k ^ cnt r k := by
    intro r
    rw [← Finset.prod_fiberwise Finset.univ r (fun i => u (r i))]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => u k) fun i hi => by rw [(Finset.mem_filter.1 hi).2],
      Finset.prod_const]
  have hmap : ∀ r ∈ (Finset.univ : Finset (Fin a → Fin n)), cnt r ∈ Finset.Nat.antidiagonalTuple n a := by
    intro r _
    rw [Finset.Nat.mem_antidiagonalTuple]
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := r)
      (fun i _ => Finset.mem_univ (r i))
    simpa [cnt] using this.symm
  rw [h1, ← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [h2 r, (Finset.mem_filter.1 hr).2]
  exact mul_comm _ _
end ReciprocityTheory.ChartRestriction.G.AR
