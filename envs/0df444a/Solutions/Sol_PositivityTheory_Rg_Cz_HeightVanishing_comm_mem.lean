-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.HeightVanishing.comm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:34:07.758664+00:00
-- url     : https://prove2.me/submissions/25800885-21f1-4184-82ab-55a5f682b748

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PHeight
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_ht_cons
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_cons
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_word_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_W_of
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_W_ind
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_letter_mem
import Theorems.Thm_PositivityTheory_Rg_Cz_HeightVanishing_mul_mem
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
open PositivityTheory.Rg.Cz.HeightVanishing
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable (E : Fin n → Fin n → Module.End ℂ M)
namespace PositivityTheory.Rg.Cz.HeightVanishing
theorem _root_.solution (hE : GlRel E) (a b : Fin n) {k : ℕ} {h : ℤ} {A : Module.End ℂ M} (hA : A ∈ W E k h) :
    E a b * A - A * E a b ∈ W E k (h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) := by
  have gl : ∀ c e : Fin n, E a b * E c e - E c e * E a b ∈
      W E 1 ((((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) + (((e : ℕ) : ℤ) - ((c : ℕ) : ℤ))) := by
    intro c e
    rw [hE a b c e]
    refine sub_mem ?_ ?_
    · split_ifs with h1
      · subst h1; exact W_of E le_rfl (by ring) (letter_mem E a e)
      · exact zero_mem _
    · split_ifs with h1
      · subst h1; exact W_of E le_rfl (by ring) (letter_mem E c b)
      · exact zero_mem _
  have hw : ∀ w : List (Fin n × Fin n),
      E a b * word E w - word E w * E a b ∈ W E w.length (ht w + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) := by
    intro w
    induction w with
    | nil => simp [word]
    | cons y w ih =>
      rw [word_cons]
      have e1 : E a b * (E y.1 y.2 * word E w) - E y.1 y.2 * word E w * E a b =
          (E a b * E y.1 y.2 - E y.1 y.2 * E a b) * word E w +
            E y.1 y.2 * (E a b * word E w - word E w * E a b) := by noncomm_ring
      rw [e1]
      refine add_mem ?_ ?_
      · exact W_of E (by simp only [List.length_cons]; omega) (by rw [ht_cons]; ring)
          (mul_mem E (gl y.1 y.2) (word_mem E w le_rfl rfl))
      · exact W_of E (by simp only [List.length_cons]; omega) (by rw [ht_cons]; ring)
          (mul_mem E (letter_mem E y.1 y.2) ih)
  refine W_ind E (p := fun A => E a b * A - A * E a b ∈ W E k (h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)))) (by simp) ?_ ?_ ?_ hA
  · intro x y hx hy
    have e : E a b * (x + y) - (x + y) * E a b = (E a b * x - x * E a b) + (E a b * y - y * E a b) := by
      noncomm_ring
    rw [e]; exact add_mem hx hy
  · intro c x hx
    have e : E a b * (c • x) - (c • x) * E a b = c • (E a b * x - x * E a b) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c hx
  · intro w h1 h2
    exact W_of E h1 (by rw [h2]) (hw w)
end PositivityTheory.Rg.Cz.HeightVanishing
