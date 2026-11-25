-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.Coch.cEv_prod2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:30:22.910477+00:00
-- url     : https://prove2.me/submissions/e400dbc2-acdb-430d-8230-df018c45bb13

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CochainExpansions_SumSumProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.Coch
variable {H V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.Cz.Coch
theorem _root_.solution {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → Fin N → H → ℂ) (c : ι → κ → V)
    (A B : Fin N → H) :
    cEv (fun v => ∑ x, ∑ y, (∏ k, f x y k (v k)) • c x y) A B =
      ∑ x, ∑ y, (∏ k, (f x y k (A k) - I * f x y k (B k))) • c x y := by
  unfold cEv
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  have e : ∀ k, f x y k (A k) - I * f x y k (B k) =
      ∑ b : Bool, (if b then (1 : ℂ) else -I) * f x y k (if b then A k else B k) := by
    intro k; simp; ring
  simp_rw [e]
  rw [Fintype.prod_sum]
end PositivityTheory.Rg.Cz.Coch
