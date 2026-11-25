-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.Q_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:45.891216+00:00
-- url     : https://prove2.me/submissions/42777be0-2225-425c-8825-5128d866c19d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAnti
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_Q_mul
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
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (col : Fin m → ℕ) (hmono : Monotone col)
    (hadj : ∀ i j : Fin m, (i : ℕ) + 1 = j → col i = col j → Q L (Equiv.swap i j)) :
    ∀ d (p q : Fin m), (q : ℕ) = p + d + 1 → col p = col q → Q L (Equiv.swap p q) := by
  intro d
  induction d with
  | zero => intro p q h hc; exact hadj p q (by omega) hc
  | succ d ih =>
    intro p q h hc
    let r : Fin m := ⟨(q : ℕ) - 1, by omega⟩
    have hpr : col p = col r := le_antisymm (hmono (show p ≤ r from Fin.le_def.mpr (by simp [r]; omega)))
      (hc ▸ hmono (show r ≤ q from Fin.le_def.mpr (by simp [r])))
    have hrq : col r = col q := hpr ▸ hc
    have h1 : p ≠ r := fun e => by rw [Fin.ext_iff] at e; simp [r] at e; omega
    have h2 : p ≠ q := fun e => by rw [Fin.ext_iff] at e; omega
    have hs : Equiv.swap p q = Equiv.swap r q * Equiv.swap p r * Equiv.swap r q := by
      rw [Equiv.swap_mul_swap_mul_swap h1 h2, Equiv.swap_comm]
    rw [hs]
    have A := hadj r q (by simp [r]; omega) hrq
    exact Q_mul L (Q_mul L A (ih p r (by simp [r]; omega) hpr)) A
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
