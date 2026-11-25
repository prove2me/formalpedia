-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.reject_interval_eq_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:40:38.77205+00:00
-- url     : https://prove2.me/submissions/2156ee5a-f2c7-43e9-9e7c-a6b4abd3b235

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_prop_cokernel_suffix_iff
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_bot_or_eq_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_eq_bot_of_lt
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_le_suffix
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_self
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_def
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_top
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_eq_bot_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le


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
theorem _root_.solution (hF : F.IsSubobjectClosed) {c ℓ d v : Fin n} (hℓd : ℓ ≤ d)
    (hcv : c ≤ v) (hv : ℓ.val + 1 = v.val) (hb : F.prop (interval k c ℓ))
    (hmax : ∀ j, ℓ < j → j ≤ d → ¬ F.prop (interval k c j)) :
    F.reject (interval k c d) = suffix c d v hcv := by
  apply le_antisymm
  · apply reject_le hF
    exact (prop_cokernel_suffix_iff F hℓd hcv hv).2 hb
  · rcases eq_bot_or_eq_suffix (F.reject (interval k c d)) with h0 | ⟨u', hcu', hu'd, hK⟩
    · have hcd : F.prop (interval k c d) := (reject_eq_bot_iff hF).1 h0
      have hℓd' : ℓ = d := by
        by_contra hne
        exact hmax d (lt_of_le_of_ne hℓd hne) le_rfl hcd
      subst hℓd'
      rw [h0, suffix_eq_bot_of_lt hcv (Fin.lt_def.2 (by omega))]
    · have hco : F.prop (cokernel (suffix (k := k) c d u' hcu').arrow) := by
        rw [← hK]
        exact F.prop_cokernel_reject _
      rw [hK]
      rcases eq_or_lt_of_le hcu' with hcu'' | hcu''
      · have : suffix (k := k) c d u' hcu' = ⊤ := by
          subst hcu''
          exact suffix_self c d
        rw [this]
        exact le_top
      · obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Fin n, ℓ'.val + 1 = u'.val :=
          ⟨⟨u'.val - 1, by omega⟩, by simp only; have := Fin.lt_def.1 hcu''; omega⟩
        have hℓ'd : ℓ' ≤ d := Fin.le_def.2 (by have := Fin.le_def.1 hu'd; omega)
        have hF' : F.prop (interval k c ℓ') := (prop_cokernel_suffix_iff F hℓ'd hcu' hℓ').1 hco
        have hle : ℓ' ≤ ℓ := by
          by_contra hlt
          exact hmax ℓ' (not_le.1 hlt) hℓ'd hF'
        have hu'v : u' ≤ v := Fin.le_def.2 (by have := Fin.le_def.1 hle; omega)
        exact suffix_le_suffix hcu' hu'v
end PretorsionImageClosed.LinearQuiver
