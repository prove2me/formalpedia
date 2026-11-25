-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Cz_re_swapSum_le__5cc149ecbe22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:01.54211+00:00
-- url     : https://prove2.me/submissions/93678cf1-202c-44b1-9e78-9c6363270d65

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_pm
import Theorems.Thm_PositivityTheory_Rg_Cz_dot_pm_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (f : TV n ℂ Q) (B : Finset Q) (p : Q)
    (hp : p ∉ B) (hf : ∀ q ∈ B, ∀ q' ∈ B, q ≠ q' → pm (Equiv.swap q q') f = -f) :
    (∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f).re ≤ (star f ⬝ᵥ f).re := by
  set Y : Module.End ℂ (TV n ℂ Q) := ∑ q ∈ B, pm (Equiv.swap p q) with hY
  have hYf : Y f = ∑ q ∈ B, pm (Equiv.swap p q) f := by simp [hY, LinearMap.sum_apply]
  have hsa : ∀ u v : TV n ℂ Q, star u ⬝ᵥ Y v = star (Y u) ⬝ᵥ v := by
    intro u v
    simp only [hY, LinearMap.sum_apply, dotProduct_sum, star_sum, sum_dotProduct, dot_pm_swap]
  have hq : ∀ q ∈ B, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (Y f) =
      f - Y f + pm (Equiv.swap p q) f := by
    intro q hqB
    have hpq : p ≠ q := fun h => hp (h ▸ hqB)
    rw [hYf, ← Finset.add_sum_erase B _ hqB, map_add, map_sum, pm_pm, Equiv.swap_mul_self]
    have : ∀ q' ∈ B.erase q, (pm (Equiv.swap p q) : Module.End ℂ (TV n ℂ Q)) (pm (Equiv.swap p q') f) =
        -(pm (Equiv.swap p q') f) := by
      intro q' hq'
      obtain ⟨hne, hq'B⟩ := Finset.mem_erase.mp hq'
      have hpq' : p ≠ q' := fun h => hp (h ▸ hq'B)
      have hperm : Equiv.swap p q * Equiv.swap p q' = Equiv.swap p q' * Equiv.swap q q' := by
        ext x
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
        split_ifs <;> simp_all
      rw [pm_pm, hperm, ← pm_pm, hf q hqB q' hq'B (Ne.symm hne), map_neg]
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib]
    have h1 : (pm 1 : Module.End ℂ (TV n ℂ Q)) f = f := rfl
    rw [h1]
    abel
  have hYY : Y (Y f) = (B.card : ℂ) • f - (B.card : ℂ) • Y f + Y f := by
    conv_lhs => rw [hY, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl hq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_const, ← hYf]
    simp [Nat.cast_smul_eq_nsmul]
  set g := f - Y f with hg
  have hYg : Y g = -((B.card : ℂ) • g) := by
    rw [hg, map_sub, hYY, smul_sub]
    abel
  have hgg : star g ⬝ᵥ g = (1 + (B.card : ℂ)) * (star f ⬝ᵥ g) := by
    conv_lhs => rw [hg]
    rw [star_sub, sub_dotProduct, ← hsa, ← hg, hYg, dotProduct_neg, dotProduct_smul, smul_eq_mul]
    ring
  have hnn : 0 ≤ (star g ⬝ᵥ g).re := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_nonneg fun I _ => ?_
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (g I).re, sq_nonneg (g I).im]
  have hre : (star g ⬝ᵥ g).re = (1 + (B.card : ℝ)) * (star f ⬝ᵥ g).re := by
    rw [hgg]
    simp [Complex.mul_re]
  have hpos : 0 ≤ (star f ⬝ᵥ g).re := by
    have h1 : (0 : ℝ) < 1 + (B.card : ℝ) := by positivity
    nlinarith
  have hfg : star f ⬝ᵥ g = star f ⬝ᵥ f - ∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f := by
    rw [hg, dotProduct_sub, hYf, dotProduct_sum]
  rw [hfg, Complex.sub_re] at hpos
  linarith
end PositivityTheory.Rg.Cz
