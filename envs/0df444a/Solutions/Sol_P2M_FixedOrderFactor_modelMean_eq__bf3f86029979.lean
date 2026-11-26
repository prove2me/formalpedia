-- Prove2me | solution 1 for P2M_FixedOrderFactor_modelMean_eq__bf3f86029979
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:50:58.024812+00:00
-- url     : https://prove2.me/submissions/c22907e4-a5c9-41e4-91bc-14e3d20982da

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (r : ℕ) (S : Finset Nat.Primes) :
    modelMean r S = ∏ q ∈ S, muAvg r (1 / (q : ℝ)) := by
  unfold modelMean muAvg
  rw [← Finset.prod_coe_sort S (fun q => (1 / (r : ℝ)) * ∑ j ∈ range r,
      localTerm (rootOfUnity r j) (1 / (q : ℝ)))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  congr 1
  · rw [one_div_pow]
  · simp_rw [← Fin.sum_univ_eq_sum_range (fun j => localTerm (rootOfUnity r j) _) r]
    exact (Fintype.prod_sum (fun (q : S) (j : Fin r) =>
      localTerm (rootOfUnity r j) (1 / ((q : Nat.Primes) : ℝ)))).symm
end FixedOrderFactor
