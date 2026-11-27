-- Prove2me | solution 1 for SizeRamsey.Plan.transversal_no_blue_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:28:43.615422+00:00
-- url     : https://prove2.me/submissions/f1c3a058-9d8f-4fa5-b11d-7a1e3a777506

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_ColoringBase
public import Theorems.Thm_SizeRamsey_Plan_incidentRed_adj

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*}
    (F : SimpleGraph V) (S : Finset V)
    (h : c4Transversal F S) :
    ¬ HasC4 (F \ incidentRed F S) := by
  rintro ⟨f, hf, h01, h12, h23, h30⟩
  have hF : IsC4Map F f := ⟨hf, h01.1, h12.1, h23.1, h30.1⟩
  have red : ∀ a b : Fin 4, (F \ incidentRed F S).Adj (f a) (f b) →
      f a ∈ S → False := fun a b hab ha =>
    hab.2 ((incidentRed_adj F S _ _).2 ⟨hab.1, Or.inl ha⟩)
  obtain ⟨i, hi⟩ := h f hF
  fin_cases i
  · exact red _ _ h01 hi
  · exact red _ _ h12 hi
  · exact red _ _ h23 hi
  · exact red _ _ h30 hi
end SizeRamsey.Plan
