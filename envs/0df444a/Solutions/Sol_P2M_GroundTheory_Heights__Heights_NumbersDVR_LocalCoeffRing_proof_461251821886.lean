-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_LocalCoeffRing_proof_461251821886
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:06:38.521301+00:00
-- url     : https://prove2.me/submissions/92d43f59-2019-4ab4-8ed5-1258c64af4ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PLocalCoeffRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
universe u
private theorem mem_minimalPrimes_of_locCycle_ne_zero {S : Type*} [CommRing S] {J W : Ideal S}
    (h : locCycle J W ≠ 0) : W ∈ J.minimalPrimes := by
  by_contra hc
  exact h (by unfold locCycle; rw [dif_neg hc])
end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace LocalCoeffRing
theorem _root_.solution (h₁ : LocalQuotRing.Statement.{u}) (h₂ : LocalQuotPrimes.Statement.{u})
    (h₃ : LocCycleLocalQuot.Statement.{u}) (h₄ : LocalQuotColon.Statement.{u})
    (h₅ : LocalQuotFinsum.Statement.{u}) (h₆ : LocalCoeffLocal.Statement.{u}) :
    LocalCoeffRing.Statement.{u} := by
  intro R _ _ P U hP hU hPU hchain f g s u v hf hg hs hu huv hno
  have := hU
  obtain ⟨hdom, hloc, hunit, hker⟩ := h₁ R P U hP hPU
  have := hdom
  have := hloc
  obtain ⟨hup, hdown⟩ := h₂ R P U hPU
  have hmin := fun {J W : Ideal R} (h : locCycle J W ≠ 0) => mem_minimalPrimes_of_locCycle_ne_zero h
  have hmin' := fun {J W : Ideal (localQuot P U)} (h : locCycle J W ≠ 0) =>
    mem_minimalPrimes_of_locCycle_ne_zero h

  have hm : IsLocalRing.maximalIdeal (localQuot P U) = U.map (localQuotMap P U) := by
    ext y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not]
  have hUc : (U.map (localQuotMap P U)).comap (localQuotMap P U) = U := (hup U hU hPU le_rfl).2
  have hPbot : P.map (localQuotMap P U) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker _).mpr fun y hy => RingHom.mem_ker.mpr ((hker y).2 hy)
  have hmapx : ∀ x : R, (P ⊔ Ideal.span {x}).map (localQuotMap P U) =
      Ideal.span {localQuotMap P U x} := by
    intro x
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hPbot, bot_sup_eq]

  have hchain' : ∀ Q₁ Q₂ : Ideal (localQuot P U), Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ →
      Q₂ < IsLocalRing.maximalIdeal (localQuot P U) → False := by
    intro Q₁ Q₂ hQ₁ hQ₂ h0 h12 h2m
    obtain ⟨hP1, -, he1⟩ := hdown Q₁ hQ₁
    obtain ⟨-, hU2, he2⟩ := hdown Q₂ hQ₂
    exact hchain _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _)
      (lt_of_le_of_ne hP1 fun h => h0.ne (by rw [← he1, ← h, hPbot]))
      (lt_of_le_of_ne (Ideal.comap_mono h12.le) fun h => h12.ne (by rw [← he1, ← he2, h]))
      (lt_of_le_of_ne hU2 fun h => h2m.ne (by rw [← he2, h, hm]))
  have hne : ∀ x : R, x ∉ P → localQuotMap P U x ≠ 0 := fun x hx h => hx ((hker x).1 h)
  have hloc' := h₆ (localQuot P U) hchain' (localQuotMap P U f) (localQuotMap P U g)
    (localQuotMap P U s) (localQuotMap P U u) (localQuotMap P U v) (hne f hf) (hne g hg) (hne s hs)
    ((hunit _).2 fun h => hu (hUc ▸ Ideal.mem_comap.mpr h))
    (by rw [← sub_eq_zero, ← map_mul, ← map_mul, ← map_sub]; exact (hker _).2 huv) ?_
  swap
  ·
    intro W hW
    have hWm := hmin' hW
    have := hWm.1.1
    obtain ⟨hPW, hWU, hWe⟩ := hdown W hWm.1.1
    have h := hno (W.comap (localQuotMap P U)) hWU
    rw [h₃ R P U _ _ le_sup_left inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {f}) _ le_sup_left
      inferInstance hPW hWU, h₃ R P U (P ⊔ Ideal.span {g}) _ le_sup_left inferInstance hPW hWU,
      hmapx, hmapx, hmapx, hWe] at h
    exact h hW
  rw [hm] at hloc'
  convert hloc' using 1
  ·
    apply h₅ R P U hPU
    · intro G hG
      have hGU : G ≤ U := le_sup_left.trans (hmin (right_ne_zero_of_mul hG)).1.2
      have h2 := left_ne_zero_of_mul hG
      by_cases h : locCycle (P ⊔ Ideal.span {f}) G = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact ⟨(hmin h2).1.1, le_sup_left.trans (hmin h2).1.2, hGU⟩
      · exact ⟨(hmin h).1.1, le_sup_left.trans (hmin h).1.2, hGU⟩
    · intro p hp
      have h2 := left_ne_zero_of_mul hp
      by_cases h : locCycle (Ideal.span {localQuotMap P U f}) p = 0
      · rw [h, zero_sub, neg_ne_zero] at h2
        exact (hmin' h2).1.1
      · exact (hmin' h).1.1
    · intro G hG hPG hGU
      rw [h₃ R P U _ G le_sup_left hG hPG hGU, h₃ R P U (P ⊔ Ideal.span {g}) G le_sup_left hG hPG hGU,
        h₃ R P U (G ⊔ Ideal.span {s}) U (le_sup_of_le_left hPG) hU hPU le_rfl, hmapx, hmapx,
        Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  ·
    apply h₅ R P U hPU
    · intro W hW
      have h1 := hmin (left_ne_zero_of_mul hW)
      have h2 := hmin (right_ne_zero_of_mul hW)
      exact ⟨h1.1.1, le_sup_left.trans h1.1.2, le_sup_left.trans h2.1.2⟩
    · intro p hp
      exact (hmin' (left_ne_zero_of_mul hp)).1.1
    · intro W hW hPW hWU
      rw [h₃ R P U _ W le_sup_left hW hPW hWU, h₃ R P U (W ⊔ _) U (le_sup_of_le_left hPW) hU hPU le_rfl,
        hmapx, Ideal.map_sup, h₄ R P U f g]
end LocalCoeffRing
end GroundTheory.Heights₂.Heights.NumbersDVR
