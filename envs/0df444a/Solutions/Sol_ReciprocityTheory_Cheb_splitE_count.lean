-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitE_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:53.108721+00:00
-- url     : https://prove2.me/submissions/6fcbf519-bb3b-4263-97e0-89357042efe7

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
import Theorems.Thm_ReciprocityTheory_Cheb_splitE_prime
import Theorems.Thm_ReciprocityTheory_Cheb_under_asIdeal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (q : Prm E) (hl : ¬ l ∣ Nrm q) (hq : χ ((Nrm q : ℕ) : ZMod l) = 1)
    (K : IntermediateField E (CyclotomicField l E))
    (hK : ∀ x : K, ∀ σ ∈ splitEH hirr χ, σ (x : CyclotomicField l E) = x) :
    Module.finrank E K ≤ {P : Prm K | under P = q ∧ Nrm P = Nrm q}.ncard := by
  classical
  have hfin : (q.asIdeal.primesOver (𝓞 K)).Finite := Algebra.QuasiFinite.finite_primesOver q.asIdeal
  let : Fintype (q.asIdeal.primesOver (𝓞 K)) := hfin.fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank q.asIdeal (𝓞 K)
  rw [← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 K) K] at hsum
  have hone : ∀ Q : q.asIdeal.primesOver (𝓞 K),
      Q.1.ramificationIdx (𝓞 E) * Q.1.inertiaDeg (𝓞 E) = 1 := by
    rintro ⟨Q, hQp, hQl⟩
    obtain ⟨h1, h2, -⟩ := splitE_prime hirr χ q hl hq K hK Q
    rw [h1, h2]
  simp only [hone, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
  let g : q.asIdeal.primesOver (𝓞 K) → Prm K := fun Q =>
    have := Q.2.2
    ⟨Q.1, Q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot q.ne_bot Q.1⟩
  have hg : Function.Injective g := by
    intro Q1 Q2 h
    apply Subtype.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
  have hset : {P : Prm K | under P = q ∧ Nrm P = Nrm q} = Set.range g := by
    ext P
    constructor
    · rintro ⟨hP, -⟩
      have hlo : P.asIdeal.LiesOver q.asIdeal := ⟨by rw [← hP, under_asIdeal]⟩
      exact ⟨⟨P.asIdeal, P.isPrime, hlo⟩, rfl⟩
    · rintro ⟨Q, rfl⟩
      have := Q.2.1
      have := Q.2.2
      refine ⟨?_, ?_⟩
      · ext1
        rw [under_asIdeal]
        exact (Ideal.over_def Q.1 q.asIdeal).symm
      · exact (splitE_prime hirr χ q hl hq K hK Q.1).2.2
  rw [hset, Set.ncard_range_of_injective hg, Nat.card_eq_fintype_card, hsum]
end ReciprocityTheory.Cheb
