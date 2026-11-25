-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.sum_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:32.20399+00:00
-- url     : https://prove2.me/submissions/7dc5a2dc-15a2-43af-b474-f1784b115a29

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
theorem _root_.solution {M : Type} [AddCommMonoid M] {n l : ℕ} (h : l + 1 ≤ n) (f : Fin n → M)
    (hf : ∀ b : Fin n, l < b.val → f b = 0) : ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE h)))]
  · rw [Finset.sum_image (fun a _ b _ e => Fin.castLE_injective h e)]
  · intro b _ hb; apply hf; by_contra hc; push Not at hc
    exact hb (Finset.mem_image.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩)
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
