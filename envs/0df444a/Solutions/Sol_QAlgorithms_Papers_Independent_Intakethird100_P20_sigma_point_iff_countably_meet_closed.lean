-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.sigma_point_iff_countably_meet_closed
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T15:38:51.598189+00:00
-- url     : https://prove2.me/submissions/82e365c9-9c44-4aa9-8674-ca425e1cca99

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_distributive_basic_unions
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.10; de Groote, Observables I, PDF p./pp. 50.
-/
theorem solution {L : Type u} [BooleanAlgebra L] (hcomplete : IsSigmaComplete L)
    (B : StoneSpectrum L) :
    IsSigmaPoint B.val ↔ ∀ a : ℕ → L, (∀ n, a n ∈ B.val) →
      ∀ b : L, IsGLB (Set.range a) b → b ∈ B.val := by
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
  have bad (a : L) (ha : a ∈ B.val) (hac : aᶜ ∈ B.val) : False := by
    apply B.property.1.2.1
    simpa only [inf_compl_eq_bot] using hcl.2 a ha aᶜ hac
  have dualInf (a : ℕ → L) (b : L) (hb : IsGLB (Set.range a) b) :
      IsLUB (Set.range fun n => (a n)ᶜ) bᶜ := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact compl_le_compl (hb.1 ⟨n, rfl⟩)
    · intro c hc
      have hh : cᶜ ≤ b := hb.2 (by
        rintro _ ⟨n, rfl⟩
        exact compl_le_of_compl_le (hc ⟨n, rfl⟩))
      simpa only [compl_compl] using compl_le_compl hh
  have dualSup (a : ℕ → L) (b : L) (hb : IsLUB (Set.range a) b) :
      IsGLB (Set.range fun n => (a n)ᶜ) bᶜ := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact compl_le_compl (hb.1 ⟨n, rfl⟩)
    · intro c hc
      have hh : b ≤ cᶜ := hb.2 (by
        rintro _ ⟨n, rfl⟩
        simpa only [compl_compl] using compl_le_compl (hc ⟨n, rfl⟩))
      simpa only [compl_compl] using compl_le_compl hh
  constructor
  · intro hp a ha b hb
    by_contra hnot
    have hbc := (dicho b).resolve_left hnot
    obtain ⟨n, hn⟩ := hp.2 (fun n => (a n)ᶜ) bᶜ (dualInf a b hb) hbc
    exact bad (a n) (ha n) hn
  · intro hclosed
    refine ⟨⟨B.property.1.1, B.property.1.2.1, hcl.1, hcl.2⟩, ?_⟩
    intro a b hb hbB
    by_contra hn
    push_neg at hn
    have hc : ∀ n, (a n)ᶜ ∈ B.val := fun n => (dicho (a n)).resolve_left (hn n)
    have hbc := hclosed (fun n => (a n)ᶜ) hc bᶜ (dualSup a b hb)
    exact bad b hbB hbc
