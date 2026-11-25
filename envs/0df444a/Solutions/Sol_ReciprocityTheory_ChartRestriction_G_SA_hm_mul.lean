-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.hm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:33:22.86521+00:00
-- url     : https://prove2.me/submissions/a0b9fe28-3307-40f7-af48-fcc0fe026149

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hm_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable {e f : ι → K} (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution (M M' : Matrix (Fin 2) (Fin 2) K) :
    hm σ J e f M * hm σ J e f M' = hm σ J e f (M * M') := by
  have matrix_eq_of_mulVec_eq_lemma_2 {ι : Type _} [Fintype ι] [DecidableEq ι] {K : Type _} [CommRing K] {A B : Matrix ι ι K} (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
    first
      | exact Matrix.ext_of_mulVec_single fun i => h _
      | exact Matrix.toLin'.injective (LinearMap.ext fun x => by simpa using h x)
  have hfe : hf σ J f e = 1 := hf_fe hσ hJ he hff hef
  refine matrix_eq_of_mulVec_eq_lemma_2 fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  simp only [hm_mulVec, hf_add_left, hf_smul_left, he, hff, hef, hfe,
    Matrix.mul_apply, Fin.sum_univ_two]
  module
end ReciprocityTheory.ChartRestriction.G.SA
