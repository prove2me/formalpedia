-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.sub_tri_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:17:58.433531+00:00
-- url     : https://prove2.me/submissions/bb95ec75-77ba-440d-ae9c-816b6f2515ca

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
    (Bᴴ * A).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᴴ * A.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hemb : ∑ l : Fin m, star (B (Fin.castLE h l) (Fin.castLE h i)) * A (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), star (B l (Fin.castLE h i)) * A l (Fin.castLE h j) := by
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
  have hil : id (Fin.castLE h i) < id l := by
    show (Fin.castLE h i).val < l.val
    have := i.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hil, star_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
