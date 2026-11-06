-- Prove2me | solution 2 for P2M_OAI_SevenEighths_HeckeTheta_pair_f__4d2050f76d8c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:41:19.253106+00:00
-- url     : https://prove2.me/submissions/ede5dd25-7af7-4814-aaac-89027b9eb593

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_cosetConstant_eq
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k

set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    (pair w).f₀ = w (0, 0) := by
  have hconst (a : Fin N × Fin N) :
      cosetConstant a.1 a.2 N (Nat.cast_pos.mpr (NeZero.pos N)) =
        if a = (0, 0) then 1 else 0 := by
    rw [cosetConstant_eq _ _ _ _ (by positivity) (by exact_mod_cast a.1.isLt)
      (by positivity) (by exact_mod_cast a.2.isLt)]
    have hz : (a.1 : ℝ) = 0 ∧ (a.2 : ℝ) = 0 ↔ a = (0, 0) := by
      simp only [Prod.ext_iff, Fin.ext_iff, Fin.val_zero, Nat.cast_eq_zero]
    simp only [hz]
  change (∑ p : (Fin N × Fin N) × Fin 2,
    w p.1 * (parityPair p.1.1 p.1.2 N _ p.2).f₀) = _
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  change (∑ a : Fin N × Fin N, w a * cosetConstant a.1 a.2 N _) = _
  simp_rw [hconst]
  simp
end OAI.SevenEighths.HeckeTheta
