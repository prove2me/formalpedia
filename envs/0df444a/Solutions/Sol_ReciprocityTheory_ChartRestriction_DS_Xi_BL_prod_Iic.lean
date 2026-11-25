-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.prod_Iic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:16.682319+00:00
-- url     : https://prove2.me/submissions/04317440-b6e5-4c88-9f5f-5bbf6c737191

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution {M : Type} [CommMonoid M] {n : ℕ} (l : Fin (n + 1)) (f : Fin (n + 1) → M) :
    ∏ j ∈ Finset.Iic l, f j = ∏ j : Fin (l.val + 1), f (Fin.castLE (by omega) j) := by
  apply Finset.prod_nbij' (fun a => (⟨min a.val l.val, by omega⟩ : Fin (l.val + 1))) (Fin.castLE (by omega))
  · intro a _; exact Finset.mem_univ _
  · intro a _; rw [Finset.mem_Iic, Fin.le_def]; simp; omega
  · intro a ha; rw [Finset.mem_Iic, Fin.le_def] at ha; ext; simp; omega
  · intro a _; ext; simp; omega
  · intro a ha; rw [Finset.mem_Iic, Fin.le_def] at ha; congr 1; ext; simp; omega
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
