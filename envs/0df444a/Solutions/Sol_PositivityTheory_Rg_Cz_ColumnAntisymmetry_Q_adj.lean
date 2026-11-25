-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:35.048392+00:00
-- url     : https://prove2.me/submissions/b9d7ecce-e439-413b-b5b4-0a1bebbfad92

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_swap_iff
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_pm_top
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_split
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
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
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (ℓ : M →ₗ[ℂ] ℂ) (top : Fin n) (col : Fin m → ℕ)
    (hmono : Monotone col) (hc : ∀ i j : Fin m, Commute (xJ E i) (xJ E j))
    (hP : ∀ i j : Fin m, (i : ℕ) + 1 = j →
      xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j)))
    (i j : Fin m) (hij : (i : ℕ) + 1 = j) (hcol : col i = col j) :
    Q (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ colD E col) (Equiv.swap i j) := by
  have hne : i ≠ j := by intro h; rw [h] at hij; omega
  rw [Q_swap_iff _ hne]
  obtain ⟨R, hD, hR⟩ := split E col hmono hc hP i j hij hcol
  set P : Module.End ℂ (TV n M (Fin m)) := pm (Equiv.swap i j) with hPdef
  have hx := (hP i j hij).1
  have PP : P * P = 1 := by rw [hPdef, ← pm_mul, Equiv.swap_mul_self, pm_one]
  have h2 : xJ E i * P = P * xJ E j - 1 := by
    calc xJ E i * P = (P * P) * xJ E i * P := by rw [PP, one_mul]
      _ = P * (P * xJ E i + 1) * P - P * P := by noncomm_ring
      _ = P * (xJ E j * P) * P - 1 := by rw [← hx, PP]
      _ = P * xJ E j - 1 := by rw [mul_assoc, mul_assoc, PP, mul_one]
  have hTP : (xJ E i - xJ E j + 1) * P = P * (1 + 1 - (xJ E i - xJ E j + 1)) - (1 + 1) := by
    calc (xJ E i - xJ E j + 1) * P = xJ E i * P - xJ E j * P + P := by noncomm_ring
      _ = (P * xJ E j - 1) - (P * xJ E i + 1) + P := by rw [h2, hx]
      _ = _ := by noncomm_ring
  have key : colD E col * P = P * (R + R - colD E col) - (R + R) := by
    rw [hD]
    calc (xJ E i - xJ E j + 1) * R * P = (xJ E i - xJ E j + 1) * P * R := by
          rw [mul_assoc, hR, ← mul_assoc]
      _ = (P * (1 + 1 - (xJ E i - xJ E j + 1)) - (1 + 1)) * R := by rw [hTP]
      _ = _ := by noncomm_ring
  refine LinearMap.ext fun f => ?_
  have e : colD E col (P f) = (colD E col * P) f := rfl
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.proj_apply]
  rw [e, key]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Pi.sub_apply, Pi.add_apply,
    pm_top, map_sub, map_add]
  simp only [hPdef, pm_top]
  ring
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
