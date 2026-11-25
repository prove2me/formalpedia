-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.multilinear_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:02.578521+00:00
-- url     : https://prove2.me/submissions/63f620bc-ff91-4b83-9f23-49fc61d787f9

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
theorem _root_.solution {n d : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin d => V n) ℂ)
    (L : V n ≃L[ℂ] V n) :
    ∃ a : (Fin n → ℕ) → ℂ, ∀ z, q (fun _ => z) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple n d, a α * ∏ k, (L z) k ^ α k := by
  classical
  let b : Fin n → V n := fun k => L.symm (EuclideanSpace.basisFun (Fin n) ℂ k)
  let cnt : (Fin d → Fin n) → (Fin n → ℕ) := fun f k => (Finset.univ.filter fun i => f i = k).card
  have hcnt : ∀ f, cnt f ∈ Finset.Nat.antidiagonalTuple n d := by
    intro f
    rw [Finset.Nat.mem_antidiagonalTuple]
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin d)))
      (t := (Finset.univ : Finset (Fin n))) (f := f) (fun i _ => Finset.mem_univ (f i))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have hprod : ∀ (f : Fin d → Fin n) (c : Fin n → ℂ), ∏ i, c (f i) = ∏ k, c k ^ cnt f k := by
    intro f c
    rw [← Finset.prod_fiberwise Finset.univ f (fun i => c (f i))]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.prod_congr rfl (fun i hi => congrArg c (Finset.mem_filter.mp hi).2), Finset.prod_const]
  refine ⟨fun α => ∑ f ∈ Finset.univ.filter (fun f => cnt f = α), q (fun i => b (f i)), fun z => ?_⟩
  have hz : z = ∑ k, (L z) k • b k := by
    have h1 := (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (L z)
    simp only [EuclideanSpace.basisFun_repr] at h1
    calc z = L.symm (L z) := (L.symm_apply_apply z).symm
      _ = L.symm (∑ k, (L z) k • EuclideanSpace.basisFun (Fin n) ℂ k) := by rw [h1]
      _ = ∑ k, (L z) k • b k := by simp only [map_sum, map_smul, b]
  have hL : q (fun _ => z) = ∑ f : Fin d → Fin n, q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k := by
    conv_lhs => rw [hz]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    congr 1
    have := hprod f (fun k => (L z) k)
    simpa using this
  rw [hL]
  symm
  calc ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        (∑ f ∈ Finset.univ.filter (fun f => cnt f = α), q (fun i => b (f i))) * ∏ k, (L z) k ^ α k
      = ∑ α ∈ Finset.Nat.antidiagonalTuple n d, ∑ f ∈ Finset.univ.filter (fun f => cnt f = α),
          q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : Fin d → Fin n, q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k :=
        Finset.sum_fiberwise_of_maps_to (fun f _ => hcnt f) _
end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
