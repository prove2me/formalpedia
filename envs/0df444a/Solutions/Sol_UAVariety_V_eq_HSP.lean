-- Prove2me | solution 1 for UAVariety.V_eq_HSP
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:42:30.089369+00:00
-- url     : https://prove2.me/submissions/259392ea-998b-4651-ad2b-ac9294c8e6b0

import Definitions.Def_UAVariety_defs
import Theorems.Thm_UAVariety_S_H_subset_H_S
import Theorems.Thm_UAVariety_P_S_subset_S_P
import Theorems.Thm_UAVariety_P_H_subset_H_P
import Theorems.Thm_UAVariety_P_P_subset_P

universe u₁ v₁

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

/-! ### Reduction: Tarski's theorem -/

theorem hsp_H_mono {K K' : Set (Alg L)} (h : K ⊆ K') : H K ⊆ H K' :=
  fun _ ⟨A, hA, f, hf⟩ => ⟨A, h hA, f, hf⟩

theorem hsp_S_mono {K K' : Set (Alg L)} (h : K ⊆ K') : S K ⊆ S K' :=
  fun _ ⟨A, hA, hf⟩ => ⟨A, h hA, hf⟩

theorem hsp_H_H (K : Set (Alg L)) : H (H K) ⊆ H K := by
  rintro C ⟨B, ⟨A, hA, f, hf⟩, g, hg⟩
  exact ⟨A, hA, g.comp f, hg.comp hf⟩

theorem hsp_S_S (K : Set (Alg L)) : S (S K) ⊆ S K := by
  rintro C ⟨B, ⟨A, hA, ⟨f⟩⟩, ⟨g⟩⟩
  exact ⟨A, hA, ⟨f.comp g⟩⟩

theorem hsp_sub_H (K : Set (Alg L)) : K ⊆ H K :=
  fun A hA => ⟨A, hA, Hom.id L A, Function.surjective_id⟩

theorem hsp_sub_S (K : Set (Alg L)) : K ⊆ S K :=
  fun A hA => ⟨A, hA, ⟨Embedding.refl L A⟩⟩

theorem hsp_sub_P (K : Set (Alg L)) : K ⊆ P K := fun A hA =>
  ⟨PUnit.{u₁ + 1}, fun _ => A, fun _ => hA,
    ⟨{ toEquiv := (Equiv.funUnique PUnit.{u₁ + 1} A).symm
       map_fun' := fun _ _ => rfl
       map_rel' := fun r => isEmptyElim r }⟩⟩

theorem hsp_sub_HSP (K : Set (Alg L)) : K ⊆ H (S (P K)) :=
  fun _ hA => hsp_sub_H _ (hsp_sub_S _ (hsp_sub_P _ hA))

theorem hsp_P_mono {K K' : Set (Alg L)} (h : K ⊆ K') : P K ⊆ P K' :=
  fun _ ⟨ι, A, hA, he⟩ => ⟨ι, A, fun i => h (hA i), he⟩

theorem hsp_isVariety (K : Set (Alg L)) : IsVariety (H (S (P K))) :=
  ⟨hsp_H_H _,
   fun _ hA => hsp_H_mono (hsp_S_S _) (S_H_subset_H_S _ hA),
   fun _ hA => hsp_H_mono (hsp_S_mono (P_P_subset_P K))
     (hsp_H_mono (P_S_subset_S_P _) (P_H_subset_H_P _ hA))⟩

theorem hsp_HSP_subset {K W : Set (Alg L)} (hW : IsVariety W) (hK : K ⊆ W) :
    H (S (P K)) ⊆ W := fun _ hA =>
  hW.1 (hsp_H_mono hW.2.1 (hsp_H_mono (hsp_S_mono hW.2.2)
    (hsp_H_mono (hsp_S_mono (hsp_P_mono hK)) hA)))

theorem hsp_main (K : Set (Alg L)) :
    (S (H K) ⊆ H (S K) ∧ P (S K) ⊆ S (P K) ∧ P (H K) ⊆ H (P K)) ∧
      V K = H (S (P K)) :=
  ⟨⟨S_H_subset_H_S K, P_S_subset_S_P K, P_H_subset_H_P K⟩,
   Set.Subset.antisymm (fun _ hA => hA _ ⟨hsp_isVariety K, hsp_sub_HSP K⟩)
     (fun _ hA _ hW => hsp_HSP_subset hW.1 hW.2 hA)⟩

end UAVariety

open UAVariety in
theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (Alg L)) :
    (S (H K) ⊆ H (S K) ∧ P (S K) ⊆ S (P K) ∧ P (H K) ⊆ H (P K)) ∧
      V K = H (S (P K)) :=
  hsp_main K
