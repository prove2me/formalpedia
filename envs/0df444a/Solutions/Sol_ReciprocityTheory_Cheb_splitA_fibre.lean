-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitA_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:42.57966+00:00
-- url     : https://prove2.me/submissions/901a892f-165d-4604-affb-8ee80d557949

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Theorems.Thm_ReciprocityTheory_Cheb_liesOver_of_under_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (q : Prm E) :
    {P : Prm (CyclotomicField l E) | under P = q}.Finite ∧
      {P : Prm (CyclotomicField l E) | under P = q}.ncard ≤ l - 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have : IsGalois E M := IsCyclotomicExtension.isGalois {l} E M
  have hfin : (q.asIdeal.primesOver (𝓞 M)).Finite := Algebra.QuasiFinite.finite_primesOver q.asIdeal
  have hinj : Function.Injective (fun P : Prm M => P.asIdeal) := fun a b h =>
    IsDedekindDomain.HeightOneSpectrum.ext h
  have hmaps : ∀ P ∈ {P : Prm M | under P = q}, P.asIdeal ∈ q.asIdeal.primesOver (𝓞 M) := by
    intro P hP
    have := liesOver_of_under_eq P q hP
    exact ⟨P.isPrime, this⟩
  refine ⟨hfin.preimage hinj.injOn |>.subset hmaps, ?_⟩
  have h1 := Set.ncard_le_ncard_of_injOn _ hmaps hinj.injOn hfin
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn q.asIdeal (𝓞 M) Gal(M/E)
  have h3 : Nat.card Gal(M/E) = l - 1 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.finrank M hirr, Nat.totient_prime hlp]
  rw [h3] at h2
  have h4 : q.asIdeal.ramificationIdxIn (𝓞 M) * q.asIdeal.inertiaDegIn (𝓞 M) ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; have := hlp.two_le; omega
  have h5 := Nat.le_mul_of_pos_right ((q.asIdeal.primesOver (𝓞 M)).ncard) (Nat.pos_of_ne_zero h4)
  exact h1.trans (h5.trans h2.le)
end ReciprocityTheory.Cheb
