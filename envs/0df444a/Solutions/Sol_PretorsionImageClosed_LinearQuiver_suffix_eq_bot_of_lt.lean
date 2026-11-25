-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.suffix_eq_bot_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:40.667706+00:00
-- url     : https://prove2.me/submissions/29440d96-6169-409e-94dd-70c07d670abe

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_isZero_interval_of_lt

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
theorem _root_.solution {a d ℓ : Fin n} (h : a ≤ ℓ) (hℓ : d < ℓ) : suffix (k := k) a d ℓ h = ⊥ := by
  rw [suffix, Subobject.mk_eq_bot_iff_zero]
  exact (isZero_interval_of_lt hℓ).eq_zero_of_src _
end PretorsionImageClosed.LinearQuiver
