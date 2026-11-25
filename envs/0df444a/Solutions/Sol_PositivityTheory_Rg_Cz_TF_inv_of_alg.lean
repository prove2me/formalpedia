-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.inv_of_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:45.710832+00:00
-- url     : https://prove2.me/submissions/90b577c8-2eff-4949-b074-6e1feca98dcb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Theorems.Thm_PositivityTheory_Rg_Cz_TF_inv_aux
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (x : A) (hx : x ∈ B) (u : ℂ)
    (L : List ℂ) (h0 : (L.map fun c => x - algebraMap ℂ A c).prod = 0) (hu : ∀ c ∈ L, u + c ≠ 0) :
    ∃ h ∈ B, h * (algebraMap ℂ A u + x) = 1 := by
  obtain ⟨h, hB, hc, β, hβ, heq⟩ := inv_aux B x hx u L hu
  rw [h0] at heq
  have hv : h * (algebraMap ℂ A u + x) = (algebraMap ℂ A u + x) * h :=
    ((Algebra.commute_algebraMap_left u h).symm.add_right hc).eq
  have hvh : (algebraMap ℂ A u + x) * h = -algebraMap ℂ A β := eq_neg_of_add_eq_zero_left heq.symm
  refine ⟨algebraMap ℂ A (-β⁻¹) * h, B.mul_mem (B.algebraMap_mem _) hB, ?_⟩
  rw [mul_assoc, hv, hvh, mul_neg, ← map_mul]
  simp [hβ]
end PositivityTheory.Rg.Cz.TF
