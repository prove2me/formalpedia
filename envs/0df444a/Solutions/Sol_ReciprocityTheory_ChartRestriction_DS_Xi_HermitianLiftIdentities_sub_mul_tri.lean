-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.sub_mul_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:17:55.26765+00:00
-- url     : https://prove2.me/submissions/519432b4-e8ed-48f6-9fb3-e938cd526fa7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec

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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (A * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hemb : ∑ l : Fin m, A (Fin.castLE h i) (Fin.castLE h l) * B (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), A (Fin.castLE h i) l * B l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hjl : id (Fin.castLE h j) < id l := by
    show (Fin.castLE h j).val < l.val
    have := j.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hjl, mul_zero]
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
