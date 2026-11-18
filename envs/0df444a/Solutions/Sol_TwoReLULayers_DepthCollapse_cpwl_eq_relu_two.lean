-- Prove2me | solution 1 for TwoReLULayers.DepthCollapse.cpwl_eq_relu_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:05:34.010033+00:00
-- url     : https://prove2.me/submissions/c4f6c564-cd1d-45bd-b04e-697e6059b942
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TwoReLULayers_DepthCollapse_cpwl_signed_maxima
import Theorems.Thm_TwoReLULayers_DepthCollapse_max_rational_network
import Theorems.Thm_TwoReLULayers_DepthCollapse_rational_field_extension
import Theorems.Thm_TwoReLULayers_DepthCollapse_network_precomposition
import Theorems.Thm_TwoReLULayers_DepthCollapse_network_linear_combination
import Theorems.Thm_TwoReLULayers_DepthCollapse_network_geometric_cpwl

open TwoReLULayers.DepthCollapse

theorem solution {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ) :
    CPWL R n = ReLU2 R n := by
  apply Set.Subset.antisymm
  · intro f hf
    obtain ⟨k, σ, A, hσ, hsum⟩ := cpwl_signed_maxima hn R f hf
    have hσR : ∀ i, σ i ∈ R := by
      intro i
      rcases hσ i with h | h <;> rw [h]
      · exact R.one_mem
      · exact R.neg_mem R.one_mem
    let c : Fin k → R := fun i => ⟨σ i, hσR i⟩
    have hmax : (maxCoord : E (n + 1) → ℝ) ∈ ReLU2 R (n + 1) :=
      rational_field_extension (by omega) R _ (max_rational_network (by omega))
    have hnet := network_linear_combination hn R c
      (fun i x => maxCoord (affineEval (A i) x))
      (fun i => network_precomposition hn (by omega) R (A i) _ hmax)
    have heq : f = (fun x => ∑ i, (c i : ℝ) * maxCoord (affineEval (A i) x)) :=
      funext hsum
    rw [heq]
    exact hnet
  · rintro f ⟨N, hN⟩
    have heq : f = N.eval := funext hN
    rw [heq]
    exact network_geometric_cpwl hn R N
