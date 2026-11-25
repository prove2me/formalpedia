-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__detIdeal_ne_bot_ac7c91201629
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:37.943579+00:00
-- url     : https://prove2.me/submissions/82081a3c-7b6f-441f-8e35-a8403576783d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
noncomputable section
namespace Formalism.BasicNotions.Examples₂
section Core
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
private theorem det_mem_detIdeal_lemma (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → Fin N → E)
    (hv : ∀ j, v j ∈ L) : (Matrix.of v).det ∈ detIdeal L := by
  unfold detIdeal
  exact Submodule.subset_span ⟨v, hv, rfl⟩
end Core
end Formalism.BasicNotions.Examples₂
end
end

set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (L : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) : detIdeal L ≠ ⊥ := by
  classical
  obtain ⟨b, hbL, hbspan, hbli⟩ : ∃ b ⊆ (L : Set (Fin N → E)),
      Submodule.span E b = Submodule.span E (L : Set (Fin N → E)) ∧
        LinearIndependent E ((↑) : b → Fin N → E) := by
    exact exists_linearIndependent E _
  rw [hsp] at hbspan
  let B : Module.Basis b E (Fin N → E) :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
  have : Finite b := Module.Finite.finite_basis B
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = N := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : b ≃ Fin N := Fintype.equivFinOfCardEq hcard
  let v : Fin N → Fin N → E := fun j => ((e.symm j : b) : Fin N → E)
  have hvL : ∀ j, v j ∈ L := fun j => hbL (e.symm j).2
  have hli : LinearIndependent E (fun j => Matrix.of v j) := hbli.comp e.symm e.symm.injective
  have hdet : (Matrix.of v).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero
  rw [Submodule.ne_bot_iff]
  exact ⟨(Matrix.of v).det, det_mem_detIdeal_lemma L v hvL, hdet⟩
end Formalism.BasicNotions.Examples₂
