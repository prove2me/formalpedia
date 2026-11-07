-- Prove2me | solution 1 for UAVariety.free_mem_SP
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T17:14:49.310206+00:00
-- url     : https://prove2.me/submissions/bcf160c6-46a4-4803-a21b-e6a309715629

import Definitions.Def_UAVariety_defs
import Theorems.Thm_UAVariety_S_S_subset_S
import Theorems.Thm_UAVariety_quot_iInf_mem_SP
import Theorems.Thm_UAVariety_P_S_subset_S_P

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fsp_main (K : Set (Alg L)) (X : Type u₁) :
    freeAlg K X ∈ S (P K) ∧ (S K ⊆ K → P K ⊆ K → freeAlg K X ∈ K) := by
  have h1 : freeAlg K X ∈ S (P (S K)) :=
    quot_iInf_mem_SP (S K) (ι := {φ : Congruence (L := L) (L.Term X) // Alg.of φ.Quot ∈ S K})
      (fun φ => φ.1) (fun φ => φ.2) (freeCong K X)
      (fun p q => ⟨fun h φ => h φ.1 φ.2, fun h φ hφ => h ⟨φ, hφ⟩⟩)
  have h2 : freeAlg K X ∈ S (P K) := by
    obtain ⟨B, hB, e⟩ := h1
    exact S_S_subset_S (P K) ⟨B, P_S_subset_S_P K hB, e⟩
  refine ⟨h2, fun hS hP => hS ?_⟩
  obtain ⟨B, hB, e⟩ := h2
  exact ⟨B, hP hB, e⟩

end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] (K : Set (UAVariety.Alg L)) (X : Type u₁) :
    UAVariety.freeAlg K X ∈ UAVariety.S (UAVariety.P K) ∧
      (UAVariety.S K ⊆ K → UAVariety.P K ⊆ K → UAVariety.freeAlg K X ∈ K) :=
  UAVariety.fsp_main K X
