-- Prove2me | solution 1 for PricingWithTips.finset3DM_iff_allocation3DM
-- status  : ACCEPTED   (prove)
-- author  : @qmaai2907271020
-- created : 2026-10-21T20:21:26.739873+00:00
-- url     : https://prove2.me/submissions/2710c5cf-1c0e-4e58-970f-0da93d4f056c

import Definitions.Def_PricingWithTips_Finset3DM

namespace PricingWithTips

private theorem IsExactCover3DM.inj {α β : Type*} {M : Finset α}
    {p : α → β} (h : IsExactCover3DM M p) {t₁ t₂ : α}
    (h₁ : t₁ ∈ M) (h₂ : t₂ ∈ M) (heq : p t₁ = p t₂) :
    t₁ = t₂ := by
  obtain ⟨t, _, huniq⟩ := h (p t₁)
  calc
    t₁ = t := huniq t₁ ⟨h₁, rfl⟩
    _ = t₂ := (huniq t₂ ⟨h₂, heq.symm⟩).symm

private theorem forward (n : ℕ) (T : Finset (ThreeDMTriple n))
    (h : HasPerfectFinset3DM n T) :
    HasPerfect3DMatching n (fun b s d => decide ((b, s, d) ∈ T)) := by
  classical
  obtain ⟨M, hsub, hB, hS, hD⟩ := h
  let τ (b : Fin n) : ThreeDMTriple n := Classical.choose (hB b)
  have hτ (b : Fin n) : τ b ∈ M ∧ (τ b).1 = b :=
    (Classical.choose_spec (hB b)).1
  let A : Allocation (Fin n) (Fin n) (Fin n) := {
    assigned := fun b => some ((τ b).2.1, (τ b).2.2)
    store_unique := by
      intro b₁ b₂ s d₁ d₂ h₁ h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      have ht : τ b₁ = τ b₂ :=
        hS.inj (hτ b₁).1 (hτ b₂).1 (h₁.1.trans h₂.1.symm)
      calc
        b₁ = (τ b₁).1 := (hτ b₁).2.symm
        _ = (τ b₂).1 := congrArg Prod.fst ht
        _ = b₂ := (hτ b₂).2
    courier_unique := by
      intro b₁ b₂ s₁ s₂ d h₁ h₂
      simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      have ht : τ b₁ = τ b₂ :=
        hD.inj (hτ b₁).1 (hτ b₂).1 (h₁.2.trans h₂.2.symm)
      calc
        b₁ = (τ b₁).1 := (hτ b₁).2.symm
        _ = (τ b₂).1 := congrArg Prod.fst ht
        _ = b₂ := (hτ b₂).2
  }
  refine ⟨A, ?_, ?_⟩
  · intro b
    exact ⟨(τ b).2.1, (τ b).2.2, rfl⟩
  · intro b s d ht
    have hpair : ((τ b).2.1, (τ b).2.2) = (s, d) := by
      simpa [A, Allocation.Trades] using ht
    have htrip : τ b = (b, s, d) := by
      apply Prod.ext
      · exact (hτ b).2
      · exact hpair
    have hm : (b, s, d) ∈ T := by
      rw [← htrip]
      exact hsub (hτ b).1
    simpa using hm

private theorem triple_eq_of_trades {n : ℕ}
    (A : Allocation (Fin n) (Fin n) (Fin n))
    {t₁ t₂ : ThreeDMTriple n}
    (h₁ : A.Trades t₁.1 t₁.2.1 t₁.2.2)
    (h₂ : A.Trades t₂.1 t₂.2.1 t₂.2.2)
    (hb : t₁.1 = t₂.1) : t₁ = t₂ := by
  rcases t₁ with ⟨b₁, s₁, d₁⟩
  rcases t₂ with ⟨b₂, s₂, d₂⟩
  dsimp at hb
  subst b₂
  change A.assigned b₁ = some (s₁, d₁) at h₁
  change A.assigned b₁ = some (s₂, d₂) at h₂
  have hp : (s₁, d₁) = (s₂, d₂) := Option.some.inj (h₁.symm.trans h₂)
  exact congrArg (fun q : Fin n × Fin n => (b₁, q)) hp

private theorem reverse (n : ℕ) (T : Finset (ThreeDMTriple n))
    (h : HasPerfect3DMatching n (fun b s d => decide ((b, s, d) ∈ T))) :
    HasPerfectFinset3DM n T := by
  classical
  obtain ⟨A, hall, hedge⟩ := h
  let σ (b : Fin n) : Fin n := Classical.choose (hall b)
  let δ (b : Fin n) : Fin n :=
    Classical.choose (Classical.choose_spec (hall b))
  have htrade (b : Fin n) : A.Trades b (σ b) (δ b) :=
    Classical.choose_spec (Classical.choose_spec (hall b))
  have hσinj : Function.Injective σ := by
    intro b₁ b₂ heq
    have ht₂ : A.Trades b₂ (σ b₁) (δ b₂) := by
      simpa [heq] using htrade b₂
    exact A.store_unique (htrade b₁) ht₂
  have hδinj : Function.Injective δ := by
    intro b₁ b₂ heq
    have ht₂ : A.Trades b₂ (σ b₂) (δ b₁) := by
      simpa [heq] using htrade b₂
    exact A.courier_unique (htrade b₁) ht₂
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective hσinj
  have hδsurj : Function.Surjective δ := Finite.surjective_of_injective hδinj
  let M : Finset (ThreeDMTriple n) := Finset.univ.filter
    (fun t => A.Trades t.1 t.2.1 t.2.2)
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have htr : A.Trades t.1 t.2.1 t.2.2 := (Finset.mem_filter.mp ht).2
    exact of_decide_eq_true (hedge t.1 t.2.1 t.2.2 htr)
  · intro b
    refine ⟨(b, σ b, δ b), ?_, ?_⟩
    · exact ⟨by simp [M, htrade b], rfl⟩
    · intro t ht
      have htr : A.Trades t.1 t.2.1 t.2.2 := (Finset.mem_filter.mp ht.1).2
      exact triple_eq_of_trades A htr (htrade b) ht.2
  · intro s
    obtain ⟨b, hb⟩ := hσsurj s
    refine ⟨(b, σ b, δ b), ?_, ?_⟩
    · exact ⟨by simp [M, htrade b], hb⟩
    · intro t ht
      have htr : A.Trades t.1 t.2.1 t.2.2 := (Finset.mem_filter.mp ht.1).2
      have htrS : A.Trades t.1 s t.2.2 := by simpa [← ht.2] using htr
      have hbaseS : A.Trades b s (δ b) := by simpa [← hb] using htrade b
      have hbuyer : t.1 = b := A.store_unique htrS hbaseS
      exact triple_eq_of_trades A htr (htrade b) hbuyer
  · intro d
    obtain ⟨b, hb⟩ := hδsurj d
    refine ⟨(b, σ b, δ b), ?_, ?_⟩
    · exact ⟨by simp [M, htrade b], hb⟩
    · intro t ht
      have htr : A.Trades t.1 t.2.1 t.2.2 := (Finset.mem_filter.mp ht.1).2
      have htrD : A.Trades t.1 t.2.1 d := by simpa [← ht.2] using htr
      have hbaseD : A.Trades b (σ b) d := by simpa [← hb] using htrade b
      have hbuyer : t.1 = b := A.courier_unique htrD hbaseD
      exact triple_eq_of_trades A htr (htrade b) hbuyer

end PricingWithTips

theorem solution (n : ℕ)
    (T : Finset (PricingWithTips.ThreeDMTriple n)) :
    PricingWithTips.HasPerfectFinset3DM n T ↔
      PricingWithTips.HasPerfect3DMatching n
        (fun b s d => decide ((b, s, d) ∈ T)) := by
  exact ⟨PricingWithTips.forward n T, PricingWithTips.reverse n T⟩
