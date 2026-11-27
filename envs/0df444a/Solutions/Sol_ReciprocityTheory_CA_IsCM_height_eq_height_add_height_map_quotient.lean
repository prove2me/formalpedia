-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.height_eq_height_add_height_map_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:42.106491+00:00
-- url     : https://prove2.me/submissions/3b8fe636-cd6e-460a-b838-00c3e9b836b7

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_IsSaturatedChain
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_localization_quotient_eq_height
import Theorems.Thm_ReciprocityTheory_CA_IsCM_height_add_ringKrullDim_quotient
import Theorems.Thm_ReciprocityTheory_CA_IsCM_localization_atPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.CA
open IsLocalRing
private theorem height_eq_order_height_lemma {R : Type*} [CommRing R] (I : Ideal R)
    [hI : I.IsPrime] : I.height = Order.height (⟨I, hI⟩ : PrimeSpectrum R) := by
  have hmin : I.minimalPrimes = {I} := Ideal.minimalPrimes_eq_subsingleton_self
  unfold Ideal.height
  apply le_antisymm
  · exact iInf₂_le I (by rw [hmin]; rfl)
  · refine le_iInf₂ fun J hJ => ?_
    have hJI : J = I := by rw [hmin] at hJ; exact hJ
    subst hJI
    exact le_rfl
private theorem height_le_height_Iic_lemma_2 {α β : Type*} [PartialOrder α] [Preorder β] (a : α)
    (f : Set.Iic a → β) (hf : StrictMono f) : Order.height a ≤ Order.height (f ⟨a, le_rfl⟩) := by
  have hmono : ∀ s : LTSeries α, Monotone s := fun s => by
    first
    | exact s.monotone
    | exact s.strictMono.monotone
  have H : ∀ s : LTSeries α, s.last ≤ a → (s.length : ℕ∞) ≤ Order.height (f ⟨a, le_rfl⟩) := by
    intro s hs
    let t : LTSeries β :=
      { length := s.length
        toFun := fun i => f ⟨s i, (hmono s (Fin.le_last i)).trans hs⟩
        step := fun i => hf (Subtype.mk_lt_mk.mpr (s.step i)) }
    have ht : t.last ≤ f ⟨a, le_rfl⟩ := by
      show f ⟨s (Fin.last s.length), _⟩ ≤ f ⟨a, le_rfl⟩
      exact hf.monotone (show s (Fin.last s.length) ≤ a from hs)
    exact Order.length_le_height ht
  first
  | exact Order.height_le_iff.mpr fun s hs => H s hs.le
  | exact Order.height_le fun s hs => H s hs.le
  | (unfold Order.height; exact iSup₂_le fun s hs => H s hs)
private theorem krullDim_le_height_lemma_3 {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : StrictMono f) (b : β) (hb : ∀ x, f x ≤ b) :
    Order.krullDim α ≤ (Order.height b : WithBot ℕ∞) := by
  unfold Order.krullDim
  refine iSup_le fun s => ?_
  have h := Order.length_le_height (p := s.map f hf) (x := b) (hb s.last)
  exact_mod_cast h
private theorem height_le_krullDim_lemma_6 {α : Type*} [Preorder α] (a : α) :
    (Order.height a : WithBot ℕ∞) ≤ Order.krullDim α := by
  first
  | exact Order.height_le_krullDim a
  | (have H : ∀ s : LTSeries α, ((s.length : ℕ∞) : WithBot ℕ∞) ≤ Order.krullDim α := fun s => by
       have := le_iSup (fun s : LTSeries α => (s.length : WithBot ℕ∞)) s
       exact_mod_cast this
     obtain ⟨k, hk⟩ := WithBot.ne_bot_iff_exists.mp
       (ne_bot_of_le_ne_bot WithBot.coe_ne_bot (H (RelSeries.singleton _ a)))
     rw [← hk]
     refine WithBot.coe_le_coe.mpr (Order.height_le_iff.mpr fun s _ => ?_)
     exact WithBot.coe_le_coe.mp (by rw [hk]; exact H s))
private theorem height_map_atPrime_lemma_5 {R : Type*} [CommRing R] (p q : Ideal R) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) [hp' : (p.map (algebraMap R (Localization.AtPrime q))).IsPrime] :
    (p.map (algebraMap R (Localization.AtPrime q))).height = p.height := by
  have hdisj : ∀ I : Ideal R, I ≤ q → Disjoint (q.primeCompl : Set R) (I : Set R) := fun I hI =>
    Set.disjoint_left.mpr fun x hx hxI => hx (hI hxI)
  rw [height_eq_order_height_lemma (p.map (algebraMap R (Localization.AtPrime q))),
    height_eq_order_height_lemma p]
  apply le_antisymm
  · let f : PrimeSpectrum (Localization.AtPrime q) → PrimeSpectrum R := fun x =>
      ⟨Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal, inferInstance⟩
    have hf : StrictMono f := by
      intro x y hxy
      show Ideal.comap (algebraMap R (Localization.AtPrime q)) x.asIdeal <
        Ideal.comap (algebraMap R (Localization.AtPrime q)) y.asIdeal
      refine lt_of_le_of_ne (Ideal.comap_mono (show x.asIdeal ≤ y.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.map (algebraMap R (Localization.AtPrime q))) e
      rw [IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q),
        IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)] at e2
      exact PrimeSpectrum.ext e2
    have hfp : f ⟨_, hp'⟩ = ⟨p, ‹p.IsPrime›⟩ := PrimeSpectrum.ext (by
      show Ideal.under R (p.map (algebraMap R (Localization.AtPrime q))) = p
      exact IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
        (S := Localization.AtPrime q) ‹p.IsPrime› (hdisj p hpq))
    have h := Order.height_le_height_apply_of_strictMono f hf ⟨_, hp'⟩
    rwa [hfp] at h
  · let g : Set.Iic (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum R) → PrimeSpectrum (Localization.AtPrime q) :=
      fun x => ⟨x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)),
        IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ _ inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq))⟩
    have hg : StrictMono g := by
      intro x y hxy
      show x.1.asIdeal.map (algebraMap R (Localization.AtPrime q)) <
        y.1.asIdeal.map (algebraMap R (Localization.AtPrime q))
      refine lt_of_le_of_ne (Ideal.map_mono (show x.1.asIdeal ≤ y.1.asIdeal from hxy.le))
        fun e => hxy.ne ?_
      have e2 := congrArg (Ideal.under R) e
      rw [IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show x.1.asIdeal ≤ p from x.2).trans hpq)),
        IsLocalization.comap_map_of_isPrime_disjoint (M := q.primeCompl)
          (S := Localization.AtPrime q) inferInstance
          (hdisj _ ((show y.1.asIdeal ≤ p from y.2).trans hpq))] at e2
      exact Subtype.ext (PrimeSpectrum.ext e2)
    exact height_le_height_Iic_lemma_2 _ g hg
end ReciprocityTheory.CA
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing
namespace ReciprocityTheory.CA
namespace IsCM
theorem _root_.solution {P : Type*} [CommRing P] [IsLocalRing P]
    (h : IsCM P) (p q : Ideal P) [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) :
    q.height = p.height + (q.map (Ideal.Quotient.mk p)).height := by
  have hL := h.localization_atPrime q
  have hdisj : Disjoint (q.primeCompl : Set P) (p : Set P) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hpq hxp)
  haveI hp' : (p.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have e := hL.height_add_ringKrullDim_quotient (p.map (algebraMap P (Localization.AtPrime q)))
  have e1 : (p.map (algebraMap P (Localization.AtPrime q))).height = p.height :=
    height_map_atPrime_lemma_5 p q hpq
  have e2 : ringKrullDim (Localization.AtPrime q) = q.height := by
    first
    | exact IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
    | (haveI hqL : (q.map (algebraMap P (Localization.AtPrime q))).IsPrime :=
         IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ q ‹_›
           (Set.disjoint_left.mpr fun x hx hxq => hx hxq)
       rw [← height_map_atPrime_lemma_5 q q le_rfl,
         height_eq_order_height_lemma (q.map (algebraMap P (Localization.AtPrime q)))]
       apply le_antisymm
       · refine krullDim_le_height_lemma_3 id strictMono_id _ fun x => ?_
         show x.asIdeal ≤ q.map (algebraMap P (Localization.AtPrime q))
         rw [← IsLocalization.map_comap (M := q.primeCompl) (S := Localization.AtPrime q)
           x.asIdeal]
         refine Ideal.map_mono fun z hz => ?_
         by_contra hzq
         exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hz)
           (IsLocalization.map_units (Localization.AtPrime q) (⟨z, hzq⟩ : q.primeCompl)))
       · exact height_le_krullDim_lemma_6 _)
  rw [ringKrullDim_localization_quotient_eq_height p q hpq, e1, e2] at e
  exact_mod_cast e.symm
end IsCM
end ReciprocityTheory.CA
