-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.open_dual_ideal_quasipoint_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:02:29.19493+00:00
-- url     : https://prove2.me/submissions/50798bd8-1043-4659-950b-dacc5e497048

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.5; de Groote, Observables I, PDF p./pp. 58.
-/
theorem solution {M : Type u} [TopologicalSpace M] (J : Set (Opens M)) (hJ : IsDualIdeal J) :
    IsQuasipoint J ↔ ∀ U : Opens M, U ∈ J ∨ openPseudoCompl U ∈ J := by
  classical
  have hpc (U : Opens M) : openPseudoCompl U = Uᶜ := by
    apply SetLike.coe_injective
    change (closure (U : Set M))ᶜ = ((Uᶜ : Opens M) : Set M)
    rw [Opens.coe_compl_eq_interior_compl, interior_compl]
  constructor
  · intro h U
    by_cases hu : U ∈ J
    · exact Or.inl hu
    · obtain ⟨V, hv, hvu⟩ := quasipoint_nonmember_has_disjoint_member J h U hu
      apply Or.inr
      apply hJ.2.2.1 V hv
      rw [hpc]
      exact le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hvu)
  · intro halt
    have hbase : IsFilterBase J := ⟨hJ.1, hJ.2.1, by
      intro a ha b hb
      exact ⟨a ⊓ b, hJ.2.2.2 a ha b hb, inf_le_left, inf_le_right⟩⟩
    refine ⟨hbase, ?_⟩
    intro C hc hJC
    apply Set.Subset.antisymm _ hJC
    intro U hu
    rcases halt U with hj | hj
    · exact hj
    · obtain ⟨W, hw, hwU, hwpc⟩ := hc.2.2 U hu (openPseudoCompl U) (hJC hj)
      have hz : W = ⊥ := by
        apply le_bot_iff.mp
        have hh := le_inf hwU hwpc
        rw [hpc, inf_compl_eq_bot] at hh
        exact hh
      exact False.elim (hc.2.1 (hz ▸ hw))
