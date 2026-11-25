-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockDimension_isAlgebraic_new_68223d104856
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:06.860619+00:00
-- url     : https://prove2.me/submissions/3c7e1bcb-6ef4-4e70-a644-768c51011af5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_new_a2cdbbbaf1b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_of_homog_2ffd1e4573b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_mem_adjoin_f2e6199c8967


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockDimension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockDimension
theorem _root_.solution [CharZero P.FunField] {j : Fin (D.size + 1)} (hj : D.elt j ≠ 0)
    (i : Fin (D.size + 1)) :
    IsAlgebraic (Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
      (Set.range fun v ↦ oldMap D (X v)))) (plusMap D (X (D.newCoord i))) := by
  set S := Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
      (Set.range fun v ↦ oldMap D (X v)))
  obtain ⟨fi, gi, δfi, δgi, hfi, hgi, hdi, hgiP, hxi⟩ := D.elt_deg i
  obtain ⟨fj, gj, δfj, δgj, hfj, hgj, hdj, hgjP, hxj⟩ := D.elt_deg j
  have hgi0 : P.mkF gi ≠ 0 := fun h ↦ hgiP ((P.mkF_eq_zero_iff gi).mp h)
  have hgj0 : P.mkF gj ≠ 0 := fun h ↦ hgjP ((P.mkF_eq_zero_iff gj).mp h)
  have hfj0 : P.mkF fj ≠ 0 := fun h ↦ hj (by rw [hxj, h, zero_div])
  have hδ : δgi + δfj = δfi + δgj := by
    funext k
    have h1 := hdi k
    have h2 := hdj k
    simp only [Pi.add_apply]
    omega
  have hH2 := oldMap_of_homog D (hgi.mul hfj)
  have hH1 := oldMap_of_homog D (hfi.mul hgj)
  rw [← hδ] at hH1
  set T := ∏ k, (X (some k) : MvPolynomial (Option ι) P.FunField) ^ (δgi + δfj) k
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero _)
  have key : P.mkF gi * P.mkF fj * D.elt i = P.mkF fi * P.mkF gj * D.elt j := by
    rw [hxi, hxj]
    field_simp
  have hrel : oldMap D (gi * fj) * plusMap D (X (D.newCoord i)) =
      oldMap D (fi * gj) * plusMap D (X (D.newCoord j)) := by
    rw [hH2, hH1, plusMap_X_new, plusMap_X_new]
    have e1 : T * C (P.mkF (gi * fj)) * (C (D.elt i) * X none) =
        T * C (P.mkF gi * P.mkF fj * D.elt i) * X none := by
      simp only [map_mul]
      ring
    have e2 : T * C (P.mkF (fi * gj)) * (C (D.elt j) * X none) =
        T * C (P.mkF fi * P.mkF gj * D.elt j) * X none := by
      simp only [map_mul]
      ring
    rw [e1, e2, key]
  have hmemY : ∀ g, oldMap D g ∈ S := fun g ↦
    Algebra.adjoin_mono (Set.subset_insert _ _) (TrdegAdjoin.map_mem_adjoin (oldMap D) g)
  have hmemE : plusMap D (X (D.newCoord j)) ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hne : oldMap D (gi * fj) ≠ 0 := by
    rw [hH2, map_mul]
    refine mul_ne_zero hT ?_
    rw [Ne, MvPolynomial.C_eq_zero]
    exact mul_ne_zero hgi0 hfj0
  refine IsAlgebraic.of_mul (y := oldMap D (gi * fj)) (mem_nonZeroDivisors_of_ne_zero hne)
    (isAlgebraic_algebraMap (⟨_, hmemY _⟩ : S)) ?_
  rw [hrel]
  exact isAlgebraic_algebraMap (⟨_, mul_mem (hmemY _) hmemE⟩ : S)
end GroundTheory.Heights₂.Heights.AddBlockDimension
