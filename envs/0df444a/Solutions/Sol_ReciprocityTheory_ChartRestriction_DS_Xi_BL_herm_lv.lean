-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.herm_lv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:57:25.528902+00:00
-- url     : https://prove2.me/submissions/af3c21c8-edb7-4165-9694-1609529f9d6b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_lv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace BL
section Lv2
variable {k r' : ℕ}
private lemma sum_eq_sum_sh_of_zero_at_edges (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hF : ∀ p : Fin (2 * (1 + r') + k + 1), (p.val = 0 ∨ p.val = 2 * (1 + r') + k) → F p = 0) :
    ∑ p, F p = ∑ q : Fin (2 * r' + k + 1), F (sh q) := by
  have hinj : Function.Injective (fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1))) := by
    intro a b h
    simp only [sh, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  rw [show ∑ q : Fin (2 * r' + k + 1), F (sh q) =
      ∑ p ∈ Finset.univ.map ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩, F p
      from (Finset.sum_map Finset.univ
        ⟨fun q : Fin (2 * r' + k + 1) => (sh q : Fin (2 * (1 + r') + k + 1)), hinj⟩ F).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hF
  by_contra hc
  apply hp
  have := p.isLt
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  refine ⟨⟨p.val - 1, by omega⟩, ?_⟩
  ext
  simp only [sh, Fin.val_mk]
  omega
private lemma liftVec_apply_sh (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (sh q) = v q := by
  have h1 : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [liftVec]
  rw [dif_pos h1]
  exact congrArg v (Fin.ext (by simp [sh]))
end Lv2
end BL
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' v) (liftVec k 1 r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [hpk_lv]
  simp only [dotProduct, Pi.star_apply]
  refine (sum_eq_sum_sh_of_zero_at_edges _ ?_).trans ?_
  · intro p hp
    have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    simp only [liftVec, dif_neg h0, mul_zero]
  · simp only [liftVec_apply_sh]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
