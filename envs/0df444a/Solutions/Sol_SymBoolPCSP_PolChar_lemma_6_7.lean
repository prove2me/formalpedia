-- Prove2me | solution 1 for SymBoolPCSP.PolChar.lemma_6_7
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-05T19:32:44.83386+00:00
-- url     : https://prove2.me/submissions/4ff29171-052b-432e-9a8a-dfe9b022ca6b

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_PolChar_Basic
import Theorems.Thm_SymBoolPCSP_PolChar_pol_canonical_template_iff
import Theorems.Thm_SymBoolPCSP_PolChar_dictator_mem_of_projectionClosed

namespace SymBoolPCSP.PolChar

open PCSPBLPAff.Symmetric

/-- Lemma 6.7. With `R` the finitized arity and `e : Fin |D^R| ≃ D^R`, the single canonical
promise relation (dictators ⊆ graphs of `F R`) works: `P ⊆ Q` because `F` contains all
dictators, and `Pol = F` by the canonical-template lemma plus finitizability. -/
theorem lemma_6_7 {D : Type} [Fintype D] [DecidableEq D] (F : FunFamily D)
    (hpc : ProjectionClosed F) (hfin : Finitizable F) (hid : ContainsId F) :
    ∃ (τ : Type) (_ : Fintype τ) (ar : τ → ℕ) (𝔸 𝔹 : RelStruct τ ar D),
      (∀ R : τ, 𝔸.rel R ⊆ 𝔹.rel R) ∧ ∀ L : ℕ, 0 < L → Pol 𝔸 𝔹 L = F L := by
  obtain ⟨R, -, hR⟩ := hfin
  let e : Fin (Fintype.card (Fin R → D)) ≃ (Fin R → D) := (Fintype.equivFin _).symm
  refine ⟨Unit, inferInstance, fun _ => Fintype.card (Fin R → D),
    ⟨fun _ => {t | ∃ j : Fin R, t = fun c => e c j}⟩,
    ⟨fun _ => {t | ∃ g ∈ F R, t = fun c => g (e c)}⟩, ?_, ?_⟩
  · rintro - t ⟨j, rfl⟩
    exact ⟨fun y => y j, dictator_mem_of_projectionClosed F hpc hid j, rfl⟩
  · intro L hL
    ext f
    exact (pol_canonical_template_iff e (F R) f).trans (hR L hL f).symm

end SymBoolPCSP.PolChar

open SymBoolPCSP.PolChar PCSPBLPAff.Symmetric in
theorem solution {D : Type} [Fintype D] [DecidableEq D] (F : FunFamily D)
    (hpc : ProjectionClosed F) (hfin : Finitizable F) (hid : ContainsId F) :
    ∃ (τ : Type) (_ : Fintype τ) (ar : τ → ℕ) (𝔸 𝔹 : RelStruct τ ar D),
      (∀ R : τ, 𝔸.rel R ⊆ 𝔹.rel R) ∧ ∀ L : ℕ, 0 < L → Pol 𝔸 𝔹 L = F L :=
  SymBoolPCSP.PolChar.lemma_6_7 F hpc hfin hid
