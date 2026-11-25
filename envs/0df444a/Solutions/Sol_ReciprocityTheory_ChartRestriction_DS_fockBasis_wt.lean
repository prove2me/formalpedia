-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.fockBasis_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:19.445636+00:00
-- url     : https://prove2.me/submissions/258b50bb-724f-4a70-9782-1eed08646b51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_sg__Multi_6b63c33631c3
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Comm
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
end Comm
private theorem sum_orderEmbOfFin_eq_sum (s : Finset (Fin (n * n))) (f : Fin (n * n) → ℝ) :
    ∑ i : Fin s.card, f (s.orderEmbOfFin rfl i) = ∑ k ∈ s, f k := by
  rw [← Finset.sum_coe_sort s f]
  exact Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv _ _ (fun i => by simp)
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (s : Finset (Fin (n * n))) (c : Fin n) :
    sgE ε cpFock cmFock c c (fockBasis n s) = ((fockWt ε s c : ℝ) : ℂ) • fockBasis n s := by
  have hb : fockBasis n s = ExteriorAlgebra.ιMulti ℂ s.card
      (fun i => Pi.single (finProdFinEquiv.symm (s.orderEmbOfFin rfl i)) (1 : ℂ)) := by
    simp [fockBasis, Module.Basis.ExteriorAlgebra, ExteriorAlgebra.ιMulti_family,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
    congr 1
    funext i
    simp
    rfl
  rw [hb, sg_ιMulti]
  congr 2
  rw [fockWt, Finset.sum_apply]
  exact sum_orderEmbOfFin_eq_sum s (fun k => modeWt ε (finProdFinEquiv.symm k) c)
end ReciprocityTheory.ChartRestriction.DS
