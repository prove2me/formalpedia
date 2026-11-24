-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericDimBound_proof_f8c74c67c7b2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:14.048399+00:00
-- url     : https://prove2.me/submissions/5ed08e68-9258-4346-85a1-d673eb4f4e3f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMaxHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace GenericDimBound
theorem _root_.solution (hmax : MaximalIdealHeightFG.Statement.{u}) :
    GenericDimBound.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hT
  classical
  let KO := FractionRing O
  let S := MRing ι O
  let MainNotions := MRing ι KO
  let φ : S →+* MainNotions := algebraMap S MainNotions
  let M : Submonoid S := (nonZeroDivisors O).map (C : O →+* S)
  have : IsLocalization M MainNotions := MvPolynomial.isLocalization (nonZeroDivisors O) KO

  have hPker : ∀ f ∈ P, constantCoeff f = 0 := by
    intro f hf
    have h0 := hP.multiHomog f hf 0
    rw [weightedHomogeneousComponent_zero] at h0
    · have : coeff 0 f ∈ P.comap (C : O →+* S) := h0
      rw [hT, Ideal.mem_bot] at this
      rw [constantCoeff_eq]
      exact this
    · intro v h
      have := congrFun h v.1
      simp [blockWeight] at this

  have hdisj : Disjoint (M : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* S) := hmem
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero ha this
  have hPK : (genFib P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M MainNotions P hP.isPrime hdisj

  let N : Ideal MainNotions := RingHom.ker (constantCoeff : MainNotions →+* KO)
  have hNmax : N.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ _⟩
  have hPN : genFib P ≤ N := by
    rw [genFib, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, constantCoeff_map, hPker f hf, map_zero]
  let A := MainNotions ⧸ genFib P
  let mk : MainNotions →+* A := Ideal.Quotient.mk (genFib P)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomapN : (N.map mk).comap mk = N := by
    rw [Ideal.comap_map_of_surjective' _ hmk, Ideal.mk_ker, sup_eq_left.mpr hPN]
  let m : Ideal A := N.map mk
  have hm : m.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mk hmk hNmax with h | h
    · exfalso
      have : N = ⊤ := by rw [← hcomapN, h, Ideal.comap_top]
      exact hNmax.ne_top this
    · exact h
  have : Algebra.FiniteType KO A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ KO (genFib P))
      (Ideal.Quotient.mkₐ_surjective KO _)
  have hht : (m.height : WithBot ℕ∞) = ringKrullDim A := hmax KO A m hm

  let g : PrimeSpectrum A → PrimeSpectrum.zeroLocus (R := S) (P : Set S) := fun x =>
    ⟨⟨(x.asIdeal.comap mk).comap φ, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show mk (φ f) ∈ x.asIdeal
      have h0 : mk (φ f) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hf : φ f ∈ genFib P)
      rw [h0]
      exact x.asIdeal.zero_mem⟩
  have hg : StrictMono g := by
    intro x y hxy
    have h1 : x.asIdeal.comap mk < y.asIdeal.comap mk :=
      lt_of_le_of_ne (Ideal.comap_mono hxy.le) fun h =>
        hxy.ne (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective mk hmk h))
    exact (IsLocalization.orderEmbedding M MainNotions).strictMono h1

  have hlastN : ∀ f : S, f ∈ (m.comap mk).comap φ ↔ constantCoeff f = 0 := by
    intro f
    rw [hcomapN, Ideal.mem_comap, RingHom.mem_ker]
    show constantCoeff (MvPolynomial.map (algebraMap O KO) f) = 0 ↔ _
    rw [constantCoeff_map]
    exact ⟨fun h => IsFractionRing.injective O KO (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M1 : Ideal S := (IsLocalRing.maximalIdeal O).comap (constantCoeff : S →+* O)
  let top : PrimeSpectrum.zeroLocus (R := S) (P : Set S) :=
    ⟨⟨M1, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [hPker f hf]
      exact Ideal.zero_mem _⟩
  have htop : g ⟨m, hm.isPrime⟩ < top := by
    show (m.comap mk).comap φ < M1
    refine lt_of_le_of_ne (fun f hf => ?_) fun h => ?_
    · show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [(hlastN f).mp hf]
      exact Ideal.zero_mem _
    · have hC : (C ϖ : S) ∈ M1 := by
        show constantCoeff (C ϖ : S) ∈ IsLocalRing.maximalIdeal O
        rw [constantCoeff_C]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
      rw [← h, hlastN, constantCoeff_C] at hC
      exact hϖ.ne_zero hC

  have key : ∀ n : ℕ, (n : ℕ∞) ≤ m.height →
      ((n + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) := by
    intro n hn
    rw [show m.height = Order.height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) from
      PrimeSpectrum.height_eq_orderHeight ⟨m, hm.isPrime⟩] at hn
    obtain ⟨p, hplast, hplen⟩ :=
      Order.exists_series_of_le_height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) hn
    have hlt : (p.map g hg).last < top := by
      rw [LTSeries.last_map, hplast]
      exact htop
    have := Order.LTSeries.length_le_krullDim ((p.map g hg).snoc top hlt)
    simpa [hplen] using this

  rw [← hht, ringKrullDim_quotient P]
  have h1 := key 0 (by simp)
  have hne : Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) ≠ ⊥ := fun h => by
    rw [h] at h1; simp at h1
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at key ⊢
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
  refine ENat.forall_natCast_le_iff_le.mp fun a ha => ?_
  rcases a with _ | k
  · simp
  · have hk : (k : ℕ∞) ≤ m.height := by
      have : (k : ℕ∞) + 1 ≤ m.height + 1 := by exact_mod_cast ha
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
    have := key k hk
    exact_mod_cast this
end GenericDimBound
end GroundTheory.Heights₂.Heights.NumbersDVR
