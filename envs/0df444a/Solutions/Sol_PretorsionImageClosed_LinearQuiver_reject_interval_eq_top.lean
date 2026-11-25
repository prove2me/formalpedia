-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.reject_interval_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:42:36.065224+00:00
-- url     : https://prove2.me/submissions/4f592d0d-2999-44c9-a9ef-a2941ac144eb

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_cokernel_suffix_iff
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_bot_or_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_self
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_def
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_eq_bot_iff


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
variable {T F : Subcategory (Statement.LinRep k n)}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (hF : F.IsSubobjectClosed) {c d : Fin n} (hcd : c ≤ d)
    (h : ∀ j, c ≤ j → j ≤ d → ¬ F.prop (interval k c j)) : F.reject (interval k c d) = ⊤ := by
  rcases eq_bot_or_eq_suffix (F.reject (interval k c d)) with h0 | ⟨u', hcu', hu'd, hK⟩
  · exact absurd ((reject_eq_bot_iff hF).1 h0) (h d hcd le_rfl)
  · have hco : F.prop (cokernel (suffix (k := k) c d u' hcu').arrow) := by
      rw [← hK]
      exact F.prop_cokernel_reject _
    rcases eq_or_lt_of_le hcu' with hcu'' | hcu''
    · rw [hK]
      subst hcu''
      exact suffix_self c d
    · exfalso
      obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin n, ℓ'.val + 1 = u'.val :=
        ⟨⟨u'.val - 1, by omega⟩, by simp only; have := Fin.lt_def.1 hcu''; omega⟩
      have hℓ'd : ℓ' ≤ d := Fin.le_def.2 (by have := Fin.le_def.1 hu'd; omega)
      have hcℓ' : c ≤ ℓ' := Fin.le_def.2 (by have := Fin.lt_def.1 hcu''; omega)
      exact h ℓ' hcℓ' hℓ'd ((prop_cokernel_suffix_iff F hℓ'd hcu' hℓ').1 hco)
end PretorsionImageClosed.LinearQuiver
