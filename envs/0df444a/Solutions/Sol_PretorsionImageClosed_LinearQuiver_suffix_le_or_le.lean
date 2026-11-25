-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.suffix_le_or_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:19:13.238007+00:00
-- url     : https://prove2.me/submissions/53ef44ff-8a17-4caf-8683-5fb633835d90

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_suffix_le_suffix

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {a d ℓ ℓ' : Fin n} (h : a ≤ ℓ) (h' : a ≤ ℓ') :
    suffix (k := k) a d ℓ h ≤ suffix (k := k) a d ℓ' h' ∨
      suffix (k := k) a d ℓ' h' ≤ suffix (k := k) a d ℓ h := by
  rcases le_total ℓ' ℓ with hle | hle
  · exact Or.inl (suffix_le_suffix h' hle)
  · exact Or.inr (suffix_le_suffix h hle)
end PretorsionImageClosed.LinearQuiver
