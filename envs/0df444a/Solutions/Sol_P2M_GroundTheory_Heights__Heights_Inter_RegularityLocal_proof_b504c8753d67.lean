-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegularityLocal_proof_b504c8753d67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:49.416878+00:00
-- url     : https://prove2.me/submissions/fe011e6d-4c73-4742-a90a-9f9ab4aaf9de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocQuotCard
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisExtra
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_eq_card_localization_38fca17f945a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_finsum_mem_eq_sum_of_injective_7f5c6e678458
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isLocalization_of_mem_iff_9d8ee689c59d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locIdeal_eq_span_6d401f7ea2c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_card_eq_sum_log_card_localization_b44963729dfe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
set_option maxHeartbeats 1000000
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegularityLocal
theorem _root_.solution (hO : RegularityOrder.Statement) (hE : RegularityMaximalSpectrum.Statement) :
    RegularityLocal.Statement := by
  classical
  intro K _ ι _ P b hP hb
  have : P.IsPrime := hP.2.1.1
  obtain ⟨e, he⟩ := hE K ι P hP
  obtain ⟨hfree, hfinite, -⟩ := hO K ι P hP
  let φ : regRing P →+* FractionRing (MRing ι ⧸ P) := (funField P).subtype.comp (regRing P).subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  let ψ : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, regRing P →+* locRing P W.1 :=
    fun W => φ.codRestrict (locRing P W.1) fun x => x.2 W.1 W.2.1 W.2.2
  have hcard : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W},
      locIdeal P W.1 (φ b) = Ideal.span {ψ W b} := fun W => locIdeal_eq_span (b.2 W.1 W.2.1 W.2.2)
  have hloc : ∀ W, @IsLocalization (regRing P) _ (e W).asIdeal.primeCompl (locRing P W.1) _ (ψ W).toAlgebra :=
    fun W => by
      let _ := (ψ W).toAlgebra
      have := (e W).isMaximal
      exact isLocalization_of_mem_iff φ hφ (locRing P W.1) (fun _ => rfl) (e W).asIdeal (he W)

  have hone : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, b ∉ (e W).asIdeal →
      Nat.card (locRing P W.1 ⧸ locIdeal P W.1 (φ b)) = 1 := fun W hbW => by
    let _ := (ψ W).toAlgebra
    have := hloc W
    have hu : IsUnit (ψ W b) :=
      IsLocalization.map_units (M := (e W).asIdeal.primeCompl) (locRing P W.1) ⟨b, hbW⟩
    rw [hcard, Ideal.span_singleton_eq_top.2 hu]
    exact Nat.card_eq_one_iff_unique.2 ⟨Ideal.Quotient.subsingleton_iff.2 rfl, ⟨0⟩⟩

  set I : Ideal (regRing P) := Ideal.span {b} with hI
  have : Finite (regRing P ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot I (by rwa [hI, Ne, Ideal.span_singleton_eq_bot])
  have : Fintype (PrimeSpectrum (regRing P ⧸ I)) := Fintype.ofFinite _
  let m : PrimeSpectrum (regRing P ⧸ I) → MaximalSpectrum (regRing P) := fun p =>
    ⟨p.asIdeal.comap (Ideal.Quotient.mk I),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := p.asIdeal)⟩
  let g : PrimeSpectrum (regRing P ⧸ I) → {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} := fun p => e.symm (m p)
  have heg : ∀ p, (e (g p)).asIdeal = p.asIdeal.comap (Ideal.Quotient.mk I) := fun p =>
    congrArg MaximalSpectrum.asIdeal (e.apply_symm_apply (m p))
  have hg : Function.Injective g := fun p q hpq => by
    have h1 := congrArg (fun W => (e W).asIdeal) hpq
    simp only [heg] at h1
    exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)
  clear_value g m

  have hgp : ∀ p : PrimeSpectrum (regRing P ⧸ I),
      Nat.card (locRing P (g p).1 ⧸ locIdeal P (g p).1 (φ b)) = Nat.card (Localization.AtPrime p.asIdeal) :=
    fun p => by
      have := (e (g p)).isMaximal
      rw [hcard]
      exact card_quot_span_eq_card_localization (ψ (g p)) b (e (g p)).asIdeal p.asIdeal (heg p) (hloc (g p))

  have hsupp : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, b ∈ (e W).asIdeal → ∃ p, g p = W :=
    fun W hbW => by
      have := (e W).isMaximal
      have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ (e W).asIdeal := by
        rw [Ideal.mk_ker, hI, Ideal.span_le, Set.singleton_subset_iff]
        exact hbW
      refine ⟨⟨(e W).asIdeal.map (Ideal.Quotient.mk I),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩, ?_⟩
      apply e.injective
      apply MaximalSpectrum.ext
      rw [heg, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left,
        ← RingHom.ker_eq_comap_bot]
      exact hker
  have hfin : {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W (φ b)) ≠ 1} ⊆
      Set.range (fun p => (g p).1) := by
    rintro W ⟨h1, h2, h3⟩
    obtain ⟨p, hp⟩ := hsupp ⟨W, h1, h2⟩ (by_contra fun hn => h3 (hone ⟨W, h1, h2⟩ hn))
    exact ⟨p, congrArg Subtype.val hp⟩
  refine ⟨(Set.finite_range _).subset hfin, ?_⟩

  refine (finsum_mem_eq_sum_of_injective {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
    (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (φ b)))) (fun p => (g p).1)
    (Subtype.val_injective.comp hg) (fun p => (g p).2)
    fun W hW h0 => hfin ⟨hW.1, hW.2, fun h1 => h0 (by rw [h1, Nat.cast_one, Real.log_one])⟩).trans ?_
  rw [log_card_eq_sum_log_card_localization (regRing P ⧸ I)]
  exact Finset.sum_congr rfl fun p _ => congrArg (fun n : ℕ => Real.log n) (hgp p)
end RegularityLocal
end GroundTheory.Heights₂.Heights.Inter
