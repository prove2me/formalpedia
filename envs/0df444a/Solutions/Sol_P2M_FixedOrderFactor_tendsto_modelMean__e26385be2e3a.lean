-- Prove2me | solution 1 for P2M_FixedOrderFactor_tendsto_modelMean__e26385be2e3a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:45.021304+00:00
-- url     : https://prove2.me/submissions/27bbb832-1649-4558-9156-7c5e880fd6da

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
public import Theorems.Thm_P2M_FixedOrderFactor_modelMean_eq__bf3f86029979
public import Theorems.Thm_P2M_FixedOrderFactor_hasProd_muAvg__1e4c6588144b
public import Theorems.Thm_FixedOrderFactor_mem_primesUpTo

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun Y => modelMean r (primesUpTo N Y)) atTop
      (𝓝 (zetaN N 2 * correctionFactor N r)) := by
  have hT : Tendsto (primesUpTo' N) atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro Y Z hYZ q hq
      simp only [primesUpTo', mem_subtype, mem_primesUpTo] at hq ⊢
      exact ⟨hq.1.trans hYZ, hq.2⟩
    · intro q
      refine ⟨q.1, ?_⟩
      simp only [primesUpTo', mem_subtype, mem_primesUpTo]
      exact ⟨le_rfl, q.2⟩
  have h := (hasProd_muAvg' N hr).comp hT
  refine h.congr (fun Y => ?_)
  simp only [Function.comp_apply]
  rw [modelMean_eq']
  unfold primesUpTo'
  refine (Finset.prod_subtype_eq_prod_filter (s := primesUpTo N Y) (p := (· ∉ N))
    (f := fun p : Nat.Primes => muAvg r (1 / (p : ℝ)))).trans ?_
  rw [Finset.filter_true_of_mem]
  intro q hq
  exact ((mem_primesUpTo N Y q).mp hq).2
end FixedOrderFactor
