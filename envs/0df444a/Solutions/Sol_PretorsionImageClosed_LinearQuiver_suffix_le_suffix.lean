-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.suffix_le_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:45.849821+00:00
-- url     : https://prove2.me/submissions/58110709-cad3-4dea-aa2d-18792cba7d41

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalIncl_comp

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
theorem _root_.solution {a d ℓ ℓ' : Fin n} (h : a ≤ ℓ) (h' : ℓ ≤ ℓ') :
    suffix (k := k) a d ℓ' (h.trans h') ≤ suffix a d ℓ h :=
  Subobject.mk_le_mk_of_comm (intervalIncl k d h') (intervalIncl_comp h h')
end PretorsionImageClosed.LinearQuiver
