-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:53.151293+00:00
-- url     : https://prove2.me/submissions/37843c2e-5c33-4946-aa5e-82d7b165ca1e

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_LogDetSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_trace_adjugate_mul_eq_sum_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix MeasureTheory
open scoped ComplexOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ) (G' : Matrix (Fin r) (Fin r) ℂ)
    (t : ℝ) (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t) :
    HasDerivAt (fun s => (G s).det) ((G t).adjugate * G').trace t := by
  rw [trace_adjugate_mul_eq_sum_perm]
  have hfun : (fun s => (G s).det) = fun s => ∑ σ : Equiv.Perm (Fin r),
      (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j := by
    funext s; exact Matrix.det_apply' _
  rw [hfun]
  have hσ : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin r))),
      HasDerivAt (fun s => (Equiv.Perm.sign σ : ℂ) * ∏ j, G s (σ j) j)
        ((Equiv.Perm.sign σ : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) • G' (σ i) i) t :=
    fun σ _ => by
      first
        | exact (HasDerivAt.fun_finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)).const_mul _
        | (have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)
           simp only [Finset.prod_apply] at hp
           exact hp.const_mul _)
        | (have hp := HasDerivAt.finset_prod (u := Finset.univ) (fun j _ => hG (σ j) j)
           convert hp.const_mul (Equiv.Perm.sign σ : ℂ) using 2
           funext s
           simp [Finset.prod_apply])
  first
    | exact HasDerivAt.fun_sum hσ
    | exact HasDerivAt.sum hσ
    | simpa using HasDerivAt.sum hσ
end ReciprocityTheory.GeometryOfNumbersTheory
