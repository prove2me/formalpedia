-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.ideal_avoidance_iff_complements
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T04:56:10.426322+00:00
-- url     : https://prove2.me/submissions/f5efecbf-e241-401c-9767-c6d23f751486

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_distributive_basic_unions
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- rem-3.2; de Groote, Observables I, PDF p./pp. 54.
-/
theorem solution {L : Type u} [BooleanAlgebra L] (hcomplete : IsSigmaComplete L)
    (I : Set L) (hI : IsSigmaIdeal I) (B : StoneSpectrum L) :
    B.val ∩ I = ∅ ↔ (fun a : L => aᶜ) '' I ⊆ B.val := by
  classical
  have hDis : QAlgorithms.Papers.Independent.Intakethird100.P20.IsDistributive (L := L) :=
    ⟨fun a b c => inf_sup_left a b c, fun a b c => sup_inf_left a b c⟩
  have hcl := quasipoint_upward_and_meet_closed B.val B.property
  obtain ⟨b0, hb0⟩ := B.property.1.1
  have htop : (⊤ : L) ∈ B.val := hcl.1 b0 hb0 ⊤ le_top
  have dicho (a : L) : a ∈ B.val ∨ aᶜ ∈ B.val := by
    have hu := (distributive_basic_unions (L := L)).1 hDis a aᶜ
    have ht : B ∈ stoneBasic (a ⊔ aᶜ) := by
      change a ⊔ aᶜ ∈ B.val
      simpa only [sup_compl_eq_top] using htop
    rw [← hu] at ht
    exact ht
  constructor
  · intro hdisj x hx
    rcases hx with ⟨a, haI, hax⟩
    subst x
    rcases dicho a with haB | hacB
    · have hh : a ∈ B.val ∩ I := ⟨haB, haI⟩
      rw [hdisj] at hh
      exact False.elim hh
    · exact hacB
  · intro h
    refine Set.Subset.antisymm ?_ (Set.empty_subset _)
    rintro a ⟨haB, haI⟩
    have hacB : aᶜ ∈ B.val := h ⟨a, haI, rfl⟩
    have hz : (⊥ : L) ∈ B.val := by
      simpa only [inf_compl_eq_bot] using hcl.2 a haB aᶜ hacB
    exact False.elim (B.property.1.2.1 hz)
