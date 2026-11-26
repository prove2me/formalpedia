-- Prove2me | solution 1 for Sabidussi.colorFiber_card_even_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:43.766806+00:00
-- url     : https://prove2.me/submissions/73aab9dd-9453-4265-8ce7-a60841031678

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Parity
import Theorems.Thm_Sabidussi_cast_colorFiber_card
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero


section
namespace Sabidussi
open scoped BigOperators
private theorem colorIndicator_eq_product (x c : Color) :
    (if x = c then 1 else 0 : F₂) =
      (1 + x.1 + c.1) * (1 + x.2 + c.2) := by
  rcases x with ⟨a, b⟩
  rcases c with ⟨u, v⟩
  fin_cases a <;> fin_cases b <;> fin_cases u <;> fin_cases v <;> decide
private theorem colorIndicator_eq_moments (x c : Color) :
    (if x = c then 1 else 0 : F₂) =
      (1 + c.1) * (1 + c.2) + (1 + c.2) * x.1 +
        (1 + c.1) * x.2 + quadratic x := by
  rw [colorIndicator_eq_product]
  simp only [quadratic]
  ring
end Sabidussi
end

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Color) (hcard : Even (Fintype.card I))
    (hsum : ∑ i, f i = 0) (hquadratic : ∑ i, quadratic (f i) = 0) (c : Color) :
    Even (colorFiber f c).card := by
  have hfst : ∑ i, (f i).1 = 0 := by
    calc
      ∑ i, (f i).1 = colorFstHom (∑ i, f i) := by
        simpa [colorFstHom] using (map_sum colorFstHom f Finset.univ).symm
      _ = 0 := by rw [hsum]; rfl
  have hsnd : ∑ i, (f i).2 = 0 := by
    calc
      ∑ i, (f i).2 = colorSndHom (∑ i, f i) := by
        simpa [colorSndHom] using (map_sum colorSndHom f Finset.univ).symm
      _ = 0 := by rw [hsum]; rfl
  have hcardF₂ : (Fintype.card I : F₂) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hcard
  change ∑ i, (f i).1 * (f i).2 = 0 at hquadratic
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [cast_colorFiber_card]
  simp_rw [colorIndicator_eq_moments]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  simp [hcardF₂, hfst, hsnd, hquadratic]
end Sabidussi
