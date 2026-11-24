-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_FibreClosedComponent_proof_f184af0dda16
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:32.355577+00:00
-- url     : https://prove2.me/submissions/cae7c19d-efae-47a3-9b7a-ddce9ea88935

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreClosedComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial IsDedekindDomain
namespace GroundTheory.Heights₂.Heights.Vertical
namespace FibreClosedComponent
theorem _root_.solution : FibreClosedComponent.Statement := by
  intro O _ _ F _ _ _ n P W v hP hPO hW hWmax
  classical
  have := hP
  have : W.IsPrime := hW.1.1

  set mk : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) O ⧸ P := Ideal.Quotient.mk P with hmk_def
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hvW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W := le_sup_right.trans hW.1.2
  have hker : RingHom.ker mk = P := Ideal.mk_ker
  have hQprime : (W.map mk).IsPrime := Ideal.map_isPrime_of_surjective hmk (by rw [hker]; exact hPW)
  let Q : PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P) := ⟨W.map mk, hQprime⟩
  have hcomapQ : (W.map mk).comap mk = W := by
    rw [Ideal.comap_map_of_surjective _ hmk, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW]
  have halg : algebraMap O (MvPolynomial (Fin n) O ⧸ P) = mk.comp C := by
    exact RingHom.ext fun _ => rfl

  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) O)
    (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal)
  let U : Set (PrimeSpectrum (MvPolynomial (Fin n) O ⧸ P)) :=
    {q | ∀ W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes,
      W' ≠ W → ¬ W' ≤ q.asIdeal.comap mk}
  have hU : IsOpen U := by
    have hUc : Uᶜ = ⋃ W' ∈ {W' | W' ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O)
        v.asIdeal).minimalPrimes ∧ W' ≠ W},
        PrimeSpectrum.zeroLocus ((W'.map mk : Ideal (MvPolynomial (Fin n) O ⧸ P)) : Set _) := by
      ext q
      simp only [U, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not, Set.mem_iUnion,
        PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, exists_prop,
        and_assoc]
    rw [← isClosed_compl_iff, hUc]
    exact Set.Finite.isClosed_biUnion (hfin.subset fun _ h => h.1)
      fun _ _ => PrimeSpectrum.isClosed_zeroLocus _
  have hiso : IsOpen (X := PrimeSpectrum.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P)) ⁻¹'
      {Q.comap (algebraMap O (MvPolynomial (Fin n) O ⧸ P))}) {⟨Q, rfl⟩} := by
    refine isOpen_induced_iff.mpr ⟨U, hU, ?_⟩
    ext ⟨q, hq⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hqU
      have hq' : q.asIdeal.comap (algebraMap O _) = Q.asIdeal.comap (algebraMap O _) :=
        congrArg PrimeSpectrum.asIdeal hq
      have hle : P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ q.asIdeal.comap mk := by
        refine sup_le ?_ ?_
        · intro x hx
          show mk x ∈ q.asIdeal
          rw [show mk x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx]
          exact q.asIdeal.zero_mem
        · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← halg, hq', halg, ← Ideal.comap_comap]
          show v.asIdeal ≤ ((W.map mk).comap mk).comap C
          rw [hcomapQ, ← Ideal.map_le_iff_le_comap]
          exact hvW
      obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
      have hW''W : W'' = W := by
        by_contra hne
        exact hqU W'' hW'' hne hW''le
      rw [hW''W] at hW''le
      have heq : W = q.asIdeal.comap mk :=
        hWmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hW''le
      apply Subtype.ext
      apply PrimeSpectrum.ext
      change q.asIdeal = W.map mk
      rw [heq, Ideal.map_comap_of_surjective _ hmk]
    · intro h
      obtain rfl : q = Q := congrArg Subtype.val h
      intro W' hW' hne hle
      change W' ≤ (W.map mk).comap mk at hle
      rw [hcomapQ] at hle
      exact hne (le_antisymm hle (hW.2 hW'.1 hle))
  have : Algebra.QuasiFiniteAt O Q.asIdeal :=
    (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber Q).mpr hiso

  obtain ⟨r, hrQ, hr, hm⟩ :=
    Algebra.zariskisMainProperty_iff.mp (Algebra.ZariskisMainProperty.of_finiteType (R := O) Q.asIdeal)
  have hr0 : r ≠ 0 := fun h => hrQ (h ▸ Q.asIdeal.zero_mem)
  have hDalg : ∀ d : MvPolynomial (Fin n) O ⧸ P, IsAlgebraic O d := by
    intro d
    obtain ⟨m, hm⟩ := hm d
    exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hr0))
      (hr.pow m).isAlgebraic hm.isAlgebraic

  have hIprime : (P.map (MvPolynomial.map (algebraMap O F) :
      MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)).IsPrime := by
    let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := O) (S := F)
    have hloc : IsLocalization ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O))
        (MvPolynomial (Fin n) F) := MvPolynomial.isLocalization _ _
    refine IsLocalization.isPrime_of_isPrime_disjoint
      ((nonZeroDivisors O).map (C : O →+* MvPolynomial (Fin n) O)) (MvPolynomial (Fin n) F) P hP ?_
    rw [Set.disjoint_left]
    rintro x hx hxP
    obtain ⟨c, hc, rfl⟩ := Submonoid.mem_map.mp hx
    have hcP : c ∈ P.comap (C : O →+* MvPolynomial (Fin n) O) := hxP
    rw [hPO, Ideal.mem_bot] at hcP
    exact nonZeroDivisors.ne_zero hc hcP

  let I := P.map (MvPolynomial.map (algebraMap O F) : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) F)
  let φ : (MvPolynomial (Fin n) O ⧸ P) →ₐ[O] (MvPolynomial (Fin n) F ⧸ I) :=
    Ideal.quotientMapₐ I (MvPolynomial.mapAlgHom (Algebra.ofId O F)) Ideal.le_comap_map
  have hX : ∀ i, IsIntegral F (Ideal.Quotient.mk I (X i)) := by
    intro i
    have h : Ideal.Quotient.mk I (X i) = φ (Ideal.Quotient.mk P (X i)) := by
      show _ = Ideal.Quotient.mk I (MvPolynomial.map (algebraMap O F) (X i))
      rw [MvPolynomial.map_X]
    rw [h]
    exact (((hDalg _).algHom φ).extendScalars (IsFractionRing.injective O F)).isIntegral
  have hint : ∀ x : MvPolynomial (Fin n) F ⧸ I, IsIntegral F x := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | mul_X p i hp => rw [map_mul]; exact hp.mul (hX i)
  have : Algebra.IsIntegral F (MvPolynomial (Fin n) F ⧸ I) := ⟨hint⟩
  have hfield : IsField (MvPolynomial (Fin n) F ⧸ I) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap F _).injective).mp (Field.toIsField F)
  exact ringKrullDim_eq_zero_of_isField hfield
end FibreClosedComponent
end GroundTheory.Heights₂.Heights.Vertical
