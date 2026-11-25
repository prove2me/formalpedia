-- Prove2me | solution 1 for ReciprocityTheory.CA.height_add_one_le_height_comap_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:46.146056+00:00
-- url     : https://prove2.me/submissions/ab36acae-2f5c-4105-a81c-7f0c06c9f9d4

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
open Polynomial
private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    p.height = Order.height (⟨p, hp⟩ : PrimeSpectrum R) := by
  have hmem : p ∈ p.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton p
  unfold Ideal.height
  refine le_antisymm ((iInf₂_le p hmem).trans (le_of_eq rfl)) (le_iInf₂ fun J hJ => ?_)
  have hJp : J = p := by
    have h2 := hJ
    rw [Ideal.minimalPrimes_eq_subsingleton_self] at h2
    exact h2
  subst hJp
  exact le_of_eq rfl
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial
namespace ReciprocityTheory.CA
theorem _root_.solution {A S : Type*} [CommRing A] [IsDomain A]
    [CommRing S] (φ : A →+* S) (hφ : Function.Surjective φ) (hker : RingHom.ker φ ≠ ⊥)
    (q : Ideal S) [q.IsPrime] : q.height + 1 ≤ (q.comap φ).height := by
  let g : WithBot (PrimeSpectrum S) → PrimeSpectrum A := fun x =>
    Option.elim x ⟨⊥, Ideal.isPrime_bot⟩ (fun p => ⟨p.asIdeal.comap φ, inferInstance⟩)
  have hg : StrictMono g := by
    intro a b hab
    induction b using WithBot.recBotCoe with
    | bot => exact (not_lt_bot hab).elim
    | coe p' =>
      induction a using WithBot.recBotCoe with
      | bot =>
        change (⊥ : Ideal A) < p'.asIdeal.comap φ
        have hk : RingHom.ker φ ≤ p'.asIdeal.comap φ := fun y hy => by
          rw [Ideal.mem_comap, RingHom.mem_ker.mp hy]
          exact p'.asIdeal.zero_mem
        exact bot_lt_iff_ne_bot.mpr fun h => hker (le_bot_iff.mp (hk.trans h.le))
      | coe p =>
        have hpp : p < p' := WithBot.coe_lt_coe.mp hab
        change p.asIdeal.comap φ < p'.asIdeal.comap φ
        refine lt_of_le_of_ne (Ideal.comap_mono (show p.asIdeal ≤ p'.asIdeal from hpp.le)) ?_
        intro h
        have h' : p'.asIdeal ≤ p.asIdeal :=
          (Ideal.comap_le_comap_iff_of_surjective φ hφ _ _).mp h.ge
        exact lt_irrefl _ (lt_of_lt_of_le ((PrimeSpectrum.asIdeal_lt_asIdeal p p').mpr hpp) h')
  have h1 := Order.height_le_height_apply_of_strictMono g hg
    ((⟨q, ‹_›⟩ : PrimeSpectrum S) : WithBot (PrimeSpectrum S))
  rw [Order.height_coe_withBot] at h1
  rw [height_eq_order_height_lemma q, height_eq_order_height_lemma (q.comap φ)]
  exact h1
end ReciprocityTheory.CA
