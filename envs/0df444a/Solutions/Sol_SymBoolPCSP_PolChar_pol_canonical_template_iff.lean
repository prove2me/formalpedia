-- Prove2me | solution 1 for SymBoolPCSP.PolChar.pol_canonical_template_iff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-05T19:32:46.541408+00:00
-- url     : https://prove2.me/submissions/578e6825-df70-4b0e-b189-3569ce19c02a

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_PolChar_Basic

namespace SymBoolPCSP.PolChar

open PCSPBLPAff.Symmetric

theorem pol_canonical_template_iff {D : Type} {R N L : ℕ} (e : Fin N ≃ (Fin R → D))
    (S : Set ((Fin R → D) → D)) (f : (Fin L → D) → D) :
    IsPolymorphism
        (⟨fun _ => {t | ∃ j : Fin R, t = fun c => e c j}⟩ : RelStruct Unit (fun _ => N) D)
        (⟨fun _ => {t | ∃ g ∈ S, t = fun c => g (e c)}⟩ : RelStruct Unit (fun _ => N) D) f ↔
      ∀ π : Fin L → Fin R, projection f π ∈ S := by
  constructor
  · intro hf π
    obtain ⟨g, hg, hgeq⟩ := hf () (fun l c => e c (π l)) (fun l => ⟨π l, rfl⟩)
    have : projection f π = g := by
      funext y
      have h := congrFun hgeq (e.symm y)
      simpa [projection, Function.comp_def] using h
    rw [this]; exact hg
  · intro h _ M hM
    choose π hπ using hM
    refine ⟨projection f π, h π, ?_⟩
    funext c
    simp only [projection, Function.comp_def]
    congr 1
    funext l
    rw [hπ l]

end SymBoolPCSP.PolChar

open SymBoolPCSP.PolChar PCSPBLPAff.Symmetric in
theorem solution {D : Type} {R N L : ℕ} (e : Fin N ≃ (Fin R → D))
    (S : Set ((Fin R → D) → D)) (f : (Fin L → D) → D) :
    IsPolymorphism
        (⟨fun _ => {t | ∃ j : Fin R, t = fun c => e c j}⟩ : RelStruct Unit (fun _ => N) D)
        (⟨fun _ => {t | ∃ g ∈ S, t = fun c => g (e c)}⟩ : RelStruct Unit (fun _ => N) D) f ↔
      ∀ π : Fin L → Fin R, projection f π ∈ S :=
  SymBoolPCSP.PolChar.pol_canonical_template_iff e S f
