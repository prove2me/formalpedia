-- Prove2me | solution 1 for SingleMachinePrec.Framework.prop_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:09:20.391463+00:00
-- url     : https://prove2.me/submissions/dfabffcf-4697-45a5-900e-4b1c2dfcacd9

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_VertexCoverGraph



namespace SingleMachinePrec.Framework

section p32
variable {N : Type*}

theorem p32_rev_step (R : N → N → Prop) [IsPartialOrder N R] (x y : N) (h : ¬ R x y) :
    ∃ R' : N → N → Prop, IsPartialOrder N R' ∧ (∀ p q, R p q → R' p q) ∧ R' y x ∧
      ∀ p q, R' p q → R p q ∨ (R p y ∧ R x q) := by
  refine ⟨fun p q => R p q ∨ (R p y ∧ R x q), ?_, ?_, ?_, ?_⟩
  · refine { refl := ?_, trans := ?_, antisymm := ?_ }
    · intro p; exact Or.inl (refl_of R p)
    · intro p q r hpq hqr
      rcases hpq with hpq | ⟨hpy, hxq⟩ <;> rcases hqr with hqr | ⟨hqy, hxr⟩
      · exact Or.inl (trans_of R hpq hqr)
      · exact Or.inr ⟨trans_of R hpq hqy, hxr⟩
      · exact Or.inr ⟨hpy, trans_of R hxq hqr⟩
      · exact absurd (trans_of R hxq hqy) h
    · intro p q hpq hqp
      rcases hpq with hpq | ⟨hpy, hxq⟩ <;> rcases hqp with hqp | ⟨hqy, hxp⟩
      · exact antisymm_of R hpq hqp
      · exact absurd (trans_of R (trans_of R hxp hpq) hqy) h
      · exact absurd (trans_of R (trans_of R hxq hqp) hpy) h
      · exact absurd (trans_of R hxq hqy) h
  · intro p q hpq; exact Or.inl hpq
  · exact Or.inr ⟨refl_of R y, refl_of R x⟩
  · intro p q hpq; exact hpq

theorem p32_exists_rev (P : N → N → Prop) [IsPartialOrder N P] (a b c d : N)
    (hab : ¬ P a b) (hcd : ¬ P c d) (hn : ¬ (P a d ∧ P c b)) :
    ∃ L : N → N → Prop, IsLinearOrder N L ∧ (∀ p q, P p q → L p q) ∧ L b a ∧ L d c := by
  obtain ⟨R1, hR1, h1P, h1ba, h1c⟩ := p32_rev_step P a b hab
  have hn2 : ¬ R1 c d := by
    intro h
    rcases h1c c d h with h | ⟨h1, h2⟩
    · exact hcd h
    · exact hn ⟨h2, h1⟩
  obtain ⟨R2, hR2, h2R1, h2dc, -⟩ := p32_rev_step R1 c d hn2
  obtain ⟨L, hL, hle⟩ := extend_partialOrder R2
  exact ⟨L, hL, fun p q h => hle _ _ (h2R1 _ _ (h1P _ _ h)), hle _ _ (h2R1 _ _ h1ba),
    hle _ _ h2dc⟩

theorem p32_single (P : N → N → Prop) [IsPartialOrder N P] (u : IncPair P) :
    ∃ L : LinearExtension P, L.ReversesAll {u} := by
  obtain ⟨R', hR', hP, hy, -⟩ := p32_rev_step P u.1.1 u.1.2 u.2.1
  obtain ⟨L, hL, hle⟩ := extend_partialOrder R'
  refine ⟨⟨L, hL, fun p q h => hle _ _ (hP _ _ h)⟩, ?_⟩
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  rw [hv]
  refine ⟨hle _ _ hy, ?_⟩
  intro h
  apply u.2.1
  rw [← h]; exact refl_of P _

theorem prop_3_2_core {N : Type*} [Fintype N] (P : N → N → Prop) [IsPartialOrder N P] :
    vertexCoverGraph P = incPairsGraph P := by
  ext u v
  obtain ⟨⟨a, b⟩, hab⟩ := u
  obtain ⟨⟨c, d⟩, hcd⟩ := v
  have key : (vertexCoverGraph P).Adj ⟨(a, b), hab⟩ ⟨(c, d), hcd⟩ ↔
      (⟨(a, b), hab⟩ : IncPair P) ≠ ⟨(c, d), hcd⟩ ∧ (P a d ∧ P c b) := by
    constructor
    · rintro ⟨hne, h⟩
      refine ⟨hne, ?_⟩
      simp only [csRule] at h
      rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have h1' : b = c := h1
        have h2' : a = d := h2
        subst h1'; subst h2'
        exact ⟨refl_of P _, refl_of P _⟩
      · have h1' : b = c := h1
        subst h1'
        exact ⟨h2, refl_of P _⟩
      · exact ⟨h1, h2⟩
      · have h1' : d = a := h1
        have h2' : c = b := h2
        subst h1'; subst h2'
        exact ⟨refl_of P _, refl_of P _⟩
      · have h1' : d = a := h1
        subst h1'
        exact ⟨refl_of P _, h2⟩
      · exact ⟨h2, h1⟩
    · rintro ⟨hne, h1, h2⟩
      exact ⟨hne, Or.inl (Or.inr (Or.inr ⟨h1, h2⟩))⟩
  rw [key]
  show _ ↔ _ ∧ _
  apply and_congr_right
  intro hne
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rintro ⟨L, hrev⟩
      have e1 := hrev ⟨(a, b), hab⟩ (Set.mem_insert _ _)
      have e2 := hrev ⟨(c, d), hcd⟩ (Set.mem_insert_of_mem _ rfl)
      obtain ⟨e1, e1'⟩ := e1
      obtain ⟨e2, e2'⟩ := e2
      simp only at e1 e1' e2 e2'
      haveI := L.isLinearOrder
      have l1 := L.extends_P _ _ h1
      have l2 := L.extends_P _ _ h2
      have : L.le a b := trans_of L.le l1 (trans_of L.le e2 l2)
      exact e1' (antisymm_of L.le e1 this)
    · intro U' hU'
      have hsub : U' ⊆ {⟨(a, b), hab⟩, ⟨(c, d), hcd⟩} := hU'.subset
      by_cases hu : (⟨(a, b), hab⟩ : IncPair P) ∈ U'
      · by_cases hv : (⟨(c, d), hcd⟩ : IncPair P) ∈ U'
        · exact absurd (Set.insert_subset hu (Set.singleton_subset_iff.2 hv)) hU'.2
        · obtain ⟨L, hL⟩ := p32_single P ⟨(a, b), hab⟩
          refine ⟨L, fun w hw => hL w ?_⟩
          rcases hsub hw with rfl | rfl
          · rfl
          · exact absurd hw hv
      · obtain ⟨L, hL⟩ := p32_single P ⟨(c, d), hcd⟩
        refine ⟨L, fun w hw => hL w ?_⟩
        rcases hsub hw with rfl | rfl
        · exact absurd hw hu
        · rfl
  · rintro ⟨h1, h2⟩
    by_contra hn
    obtain ⟨L, hL, hPL, hba, hdc⟩ := p32_exists_rev P a b c d hab.1 hcd.1 hn
    apply h1
    refine ⟨⟨L, hL, hPL⟩, ?_⟩
    intro w hw
    rcases hw with rfl | rfl
    · refine ⟨hba, ?_⟩
      intro h; apply hab.1; rw [← h]; exact refl_of P _
    · refine ⟨hdc, ?_⟩
      intro h; apply hcd.1; rw [← h]; exact refl_of P _

end p32

end SingleMachinePrec.Framework

open SingleMachinePrec.Framework


theorem solution {N : Type*} [Fintype N] (P : N → N → Prop) [IsPartialOrder N P] :
    vertexCoverGraph P = incPairsGraph P := by
  exact prop_3_2_core P
