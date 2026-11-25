-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.Iic_su
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:48.179925+00:00
-- url     : https://prove2.me/submissions/1cc963a6-5298-4405-8c2d-faf49d440e78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_exists_su

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
variable {k r' : ℕ}
variable (τ : Matrix (Fin (r' + 1)) (Fin (r' + 1)) ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (a : Fin (r' + 1)) : Finset.Iic (su a) = insert 0 ((Finset.Iic a).map suE) := by
  ext l
  simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_map]
  constructor
  · intro hl
    by_cases h0 : l.val = 0
    · exact Or.inl (Fin.ext h0)
    · obtain ⟨b, rfl⟩ := exists_su l h0
      refine Or.inr ⟨b, ?_, rfl⟩
      rw [Fin.le_iff_val_le_val] at hl ⊢
      rw [su_val, su_val] at hl
      omega
  · rintro (rfl | ⟨b, hb, rfl⟩)
    · exact Fin.zero_le _
    · show su b ≤ su a
      rw [Fin.le_iff_val_le_val] at hb ⊢
      rw [su_val, su_val]
      omega
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
