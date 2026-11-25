-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.card_admFin_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:37:03.815227+00:00
-- url     : https://prove2.me/submissions/bd468c62-4cee-4818-bba6-f1ef159e9420

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalFamilies
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_FamilyRestriction
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_admFin_glue
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {D : IntervalFamily n} {J : Finset (Fin (n + 1))} (hJ : J ⊆ adm D) :
    (admFin (D.glue J)).card + (if J = ∅ then 0 else 1) =
      J.card + ((adm D).filter (fun c => ∀ a ∈ J, c ≤ a)).card := by
  rw [admFin_glue hJ, ← Finset.card_union_add_card_inter, Finset.inter_filter,
    Finset.inter_eq_left.2 hJ]
  congr 1
  by_cases hJe : J = ∅
  · rw [if_pos hJe, hJe]
    simp
  · rw [if_neg hJe]
    have hne : J.Nonempty := Finset.nonempty_iff_ne_empty.2 hJe
    symm
    rw [Finset.card_eq_one]
    refine ⟨J.min' hne, ?_⟩
    ext c
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hle⟩
      exact le_antisymm (hle _ (Finset.min'_mem J hne)) (Finset.min'_le J c hc)
    · rintro rfl
      exact ⟨Finset.min'_mem J hne, fun a ha => Finset.min'_le J a ha⟩
end PretorsionImageClosed.LinearQuiver
