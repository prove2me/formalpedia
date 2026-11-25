-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint.exists_dvr_point_flat_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:28.825108+00:00
-- url     : https://prove2.me/submissions/48ca878c-d930-4cd6-ae31-ab7b141f03f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DimensionQuotientBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PrimeAvoidanceFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscreteValuationPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DimensionQuotientBound_local_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_PrimeAvoidanceFibre_avoid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_PrimeAvoidanceFibre_finite_of_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint
open IsLocalRing
private theorem irreducible_mem_maximalIdeal {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal O := by
  exact (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.1
private theorem algebraMap_ne_zero_of_flat' {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B]
    [Algebra O B] [Module.Flat O B] {x : O} (hx : x ≠ 0) : algebraMap O B x ≠ 0 := by
  intro h
  have h1 : x • (1 : B) = x • (0 : B) := by simp [Algebra.smul_def, h]
  exact one_ne_zero ((Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
    (mem_nonZeroDivisors_of_ne_zero hx)) h1)
private theorem algebraMap_injective_of_uniformizer_ne_zero {O T : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing T] [IsDomain T] [Algebra O T] {ϖ : O} (hϖ : Irreducible ϖ)
    (h : algebraMap O T ϖ ≠ 0) : Function.Injective (algebraMap O T) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hmax : (RingHom.ker (algebraMap O T)).IsMaximal := by
    exact Ideal.IsPrime.isMaximal (RingHom.ker_isPrime (algebraMap O T)) hne
  have hk : RingHom.ker (algebraMap O T) = maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  apply h
  rw [← RingHom.mem_ker, hk]
  exact irreducible_mem_maximalIdeal hϖ
private theorem localization_away_domain_noetherian_finiteType {O R : Type} [CommRing O] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra O R] [Algebra.FiniteType O R] (s : R) (hs : s ≠ 0) :
    IsDomain (Localization.Away s) ∧ IsNoetherianRing (Localization.Away s) ∧
      Algebra.FiniteType O (Localization.Away s) ∧
      Function.Injective (algebraMap R (Localization.Away s)) := by
  have hle : Submonoid.powers s ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsLocalization.isDomain_localization hle
  · exact IsLocalization.isNoetherianRing (Submonoid.powers s) (Localization.Away s) inferInstance
  · have h1 : Algebra.FiniteType R (Localization.Away s) := by
      infer_instance
    exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType O R) h1
  · exact IsLocalization.injective (Localization.Away s) hle
private theorem isLocalization_fractionRing_of_isIntegral {O T : Type} [CommRing O] [IsDomain O] [CommRing T] [IsDomain T]
    [Algebra O T] [Algebra.IsIntegral O T] (hinj : Function.Injective (algebraMap O T)) :
    IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors O)) (FractionRing T) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, a, ha, rfl⟩
    refine isUnit_iff_ne_zero.2 ?_
    intro h
    apply nonZeroDivisors.ne_zero ha
    apply hinj
    apply IsFractionRing.injective T (FractionRing T)
    simpa using h
  · intro z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors T) z
    dsimp only at hab
    have hb0 : (b : T) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have hc : (Ideal.span {(b : T)}).comap (algebraMap O T) ≠ ⊥ := by
      exact Ideal.comap_ne_bot_of_integral_mem hb0 (Ideal.mem_span_singleton_self (b : T))
        (Algebra.IsIntegral.isIntegral (b : T))
    obtain ⟨c, hcmem, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hcmem
    obtain ⟨d, hd⟩ := hcmem
    refine ⟨⟨a * d, ⟨algebraMap O T c, c, mem_nonZeroDivisors_of_ne_zero hc0, rfl⟩⟩, ?_⟩
    show z * algebraMap T (FractionRing T) (algebraMap O T c) = algebraMap T (FractionRing T) (a * d)
    rw [← hd, map_mul, map_mul, mul_comm (algebraMap T (FractionRing T) d), ← mul_assoc, hab]
  · intro x y h
    exact ⟨1, by simpa using IsFractionRing.injective T (FractionRing T) h⟩
private theorem exists_dedekind_embedding_of_finite {O T : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [CommRing T] [IsDomain T] [Algebra O T] [Module.Finite O T]
    (hinj : Function.Injective (algebraMap O T)) :
    ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsDedekindDomain C) (_ : Algebra O C)
      (_ : Module.Finite O C) (ψ : T →ₐ[O] C), Function.Injective ψ := by
  classical
  haveI : NoZeroSMulDivisors O (FractionRing T) := by
    have hi : Function.Injective (algebraMap O (FractionRing T)) := by
      rw [IsScalarTower.algebraMap_eq O T (FractionRing T)]
      exact (IsFractionRing.injective T (FractionRing T)).comp hinj
    exact ⟨fun {c x} h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left (fun h' => hi (h'.trans (map_zero _).symm))⟩
  letI : Algebra (FractionRing O) (FractionRing T) := FractionRing.liftAlgebra O (FractionRing T)
  haveI : IsScalarTower O (FractionRing O) (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra O (FractionRing T)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors O)) (FractionRing T) :=
    isLocalization_fractionRing_of_isIntegral hinj
  haveI : FiniteDimensional (FractionRing O) (FractionRing T) :=
    Module.Finite.of_isLocalization O T (Rₚ := FractionRing O) (Sₚ := FractionRing T)
      (nonZeroDivisors O)
  haveI : CharZero (FractionRing O) := by
    infer_instance
  haveI : Algebra.IsSeparable (FractionRing O) (FractionRing T) := by
    infer_instance
  haveI : IsDedekindDomain (integralClosure O (FractionRing T)) := by
    infer_instance
  haveI : Module.Finite O (integralClosure O (FractionRing T)) := by
    exact IsIntegralClosure.finite O (FractionRing O) (FractionRing T)
      (integralClosure O (FractionRing T))
  refine ⟨integralClosure O (FractionRing T), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (IsScalarTower.toAlgHom O T (FractionRing T)).codRestrict _ ?_, ?_⟩
  · intro t
    exact (Algebra.IsIntegral.isIntegral t).map (IsScalarTower.toAlgHom O T (FractionRing T))
  · intro a b h
    exact IsFractionRing.injective T (FractionRing T) (congrArg Subtype.val h)
private theorem exists_dvr_embedding_of_dedekind {O C : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    [CommRing C] [IsDomain C] [IsDedekindDomain C] [Algebra O C] [Module.Finite O C]
    (hinj : Function.Injective (algebraMap O C)) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : C →ₐ[O] V), Function.Injective φ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := irreducible_mem_maximalIdeal hϖ
  have hϖ0 : algebraMap O C ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨N, hNmax⟩ := Ideal.exists_maximal C
  haveI := hNmax
  have hϖN : algebraMap O C ϖ ∈ N := by
    have hc : (N.comap (algebraMap O C)).IsMaximal := by
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N
    rw [← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal hc]
    exact hϖm
  have hch : ∀ P : Ideal C, P.IsPrime → ⊥ ≤ P → P ≤ N → algebraMap O C ϖ ∈ P → P = N := by
    intro P hP _ hPN hϖP
    have hP0 : P ≠ ⊥ := fun h => hϖ0 (by rw [h] at hϖP; exact (Submodule.mem_bot C).1 hϖP)
    exact (Ideal.IsPrime.isMaximal hP hP0).eq_of_le hNmax.ne_top hPN
  obtain ⟨s, hsN, hs⟩ := ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.avoid N ⊥ (algebraMap O C ϖ) hch
  have hs0 : s ≠ 0 := fun h => hsN (h ▸ N.zero_mem)
  haveI : Algebra.FiniteType O C := by
    infer_instance
  obtain ⟨hVd, hVn, hVf, hVi⟩ := localization_away_domain_noetherian_finiteType (O := O) s hs0
  have hϖV : algebraMap O (Localization.Away s) ϖ =
      algebraMap C (Localization.Away s) (algebraMap O C ϖ) :=
    IsScalarTower.algebraMap_apply O C _ ϖ
  have key : ∀ P : Ideal (Localization.Away s), P.IsPrime →
      algebraMap O (Localization.Away s) ϖ ∈ P →
      P = Ideal.map (algebraMap C (Localization.Away s)) N := by
    intro P hP hϖP
    haveI := hP
    have hQ : P.comap (algebraMap C (Localization.Away s)) = N := by
      apply hs
      · infer_instance
      · exact bot_le
      · rw [Ideal.mem_comap, ← hϖV]
        exact hϖP
      · intro h
        rw [Ideal.mem_comap] at h
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
    rw [← hQ]
    rw [IsLocalization.map_comap (Submonoid.powers s)]
  have hdisj : Disjoint (Submonoid.powers s : Set C) (N : Set C) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hsN (hNmax.isPrime.mem_of_pow_mem n hx)
  have hP0 : (Ideal.map (algebraMap C (Localization.Away s)) N).IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) _ N hNmax.isPrime hdisj
  have hϖmem : algebraMap O (Localization.Away s) ϖ ∈ Ideal.map (algebraMap C (Localization.Away s)) N := by
    rw [hϖV]
    exact Ideal.mem_map_of_mem _ hϖN
  haveI : Module.Finite O (Localization.Away s) := by
    refine ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ ⟨_, hP0, hϖmem⟩ ?_
    intro P P' hP hP' h1 h2
    rw [key P hP h1, key P' hP' h2]
  have hinjV : Function.Injective (algebraMap O (Localization.Away s)) := by
    rw [IsScalarTower.algebraMap_eq O C (Localization.Away s)]
    exact hVi.comp hinj
  have hnz : ∀ P : Ideal (Localization.Away s), P.IsPrime → P ≠ ⊥ →
      algebraMap O (Localization.Away s) ϖ ∈ P := by
    intro P hP hP0'
    haveI := hP
    have hc : P.comap (algebraMap O (Localization.Away s)) ≠ ⊥ := by
      obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0'
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
    have hm := IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hc)
    rw [← Ideal.mem_comap, hm]
    exact hϖm
  have hdvr : IsDiscreteValuationRing (Localization.Away s) := by
    haveI : IsDedekindDomain (Localization.Away s) := by
      exact IsLocalization.isDedekindDomain C (powers_le_nonZeroDivisors_of_noZeroDivisors hs0) _
    have hfin : {I : Ideal (Localization.Away s) | I.IsPrime}.Finite := by
      apply ((Set.finite_singleton (Ideal.map (algebraMap C (Localization.Away s)) N)).insert ⊥).subset
      intro P hP
      by_cases h : P = ⊥
      · exact Or.inl h
      · exact Or.inr (key P hP (hnz P hP h))
    haveI : IsPrincipalIdealRing (Localization.Away s) := IsPrincipalIdealRing.of_finite_primes hfin
    rw [IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime]
    refine ⟨inferInstance, _, ⟨?_, hP0⟩, ?_⟩
    · intro h
      rw [h, Ideal.mem_bot] at hϖmem
      exact hϖ.ne_zero (hinjV (hϖmem.trans (map_zero _).symm))
    · rintro P ⟨hP0', hP⟩
      exact key P hP (hnz P hP hP0')
  exact ⟨Localization.Away s, inferInstance, hVd, hdvr, inferInstance, inferInstance,
    IsScalarTower.toAlgHom O C (Localization.Away s), hVi⟩
private theorem exists_finite_domain_quotient_ne_zero {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤) (e : B) (he : e ≠ 0) :
    ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : Algebra O T) (_ : Module.Finite O T)
      (g : B →ₐ[O] T), Function.Injective (algebraMap O T) ∧ g e ≠ 0 := by
  classical
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := irreducible_mem_maximalIdeal hϖ
  have hw0 : algebraMap O B ϖ ≠ 0 := algebraMap_ne_zero_of_flat' hϖ.ne_zero
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ hsp
  haveI := hMmax
  have hwM : algebraMap O B ϖ ∈ M := hMle (Ideal.mem_map_of_mem _ hϖm)
  obtain ⟨q, hqp, hqM, heq, hwq, hch⟩ :=
    ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.local_step M (algebraMap O B ϖ) e hwM hw0 he
  obtain ⟨s, hsM, hs⟩ := ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.avoid M q (algebraMap O B ϖ) hch
  haveI := hqp
  have hsq : s ∉ q := fun h => hsM (hqM h)
  have hsb : Ideal.Quotient.mk q s ≠ 0 := fun h => hsq (Ideal.Quotient.eq_zero_iff_mem.1 h)
  haveI : Algebra.FiniteType O (B ⧸ q) := by
    infer_instance
  obtain ⟨hTd, hTn, hTf, hTi⟩ := localization_away_domain_noetherian_finiteType (O := O) (Ideal.Quotient.mk q s) hsb
  have hϖT : algebraMap O (Localization.Away (Ideal.Quotient.mk q s)) ϖ =
      algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s))
        (Ideal.Quotient.mk q (algebraMap O B ϖ)) := by
    rw [IsScalarTower.algebraMap_apply O (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s))]
    rfl
  have key : ∀ P : Ideal (Localization.Away (Ideal.Quotient.mk q s)), P.IsPrime →
      algebraMap O (Localization.Away (Ideal.Quotient.mk q s)) ϖ ∈ P →
      P = Ideal.map (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s)))
        (Ideal.map (Ideal.Quotient.mk q) M) := by
    intro P hP hϖP
    haveI := hP
    have hQ : (P.comap (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s)))).comap
        (Ideal.Quotient.mk q) = M := by
      apply hs
      · infer_instance
      · intro x hx
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
        exact P.zero_mem
      · rw [Ideal.mem_comap, Ideal.mem_comap, ← hϖT]
        exact hϖP
      · intro h
        rw [Ideal.mem_comap, Ideal.mem_comap] at h
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit _))
    rw [← hQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [IsLocalization.map_comap (Submonoid.powers (Ideal.Quotient.mk q s))]
  have hdisj : Disjoint (Submonoid.powers (Ideal.Quotient.mk q s) : Set (B ⧸ q))
      (Ideal.map (Ideal.Quotient.mk q) M : Set (B ⧸ q)) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    dsimp only at hx
    rw [← map_pow] at hx
    apply hsM
    apply hMmax.isPrime.mem_of_pow_mem n
    exact (Ideal.mem_quotient_iff_mem hqM).1 hx
  have hMq : (Ideal.map (Ideal.Quotient.mk q) M).IsPrime := by
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hqM)
  have hP0 : (Ideal.map (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s)))
      (Ideal.map (Ideal.Quotient.mk q) M)).IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (Ideal.Quotient.mk q s))
      _ _ hMq hdisj
  haveI : Module.Finite O (Localization.Away (Ideal.Quotient.mk q s)) := by
    refine ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ ⟨_, hP0, ?_⟩ ?_
    · rw [hϖT]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hwM)
    · intro P P' hP hP' h1 h2
      rw [key P hP h1, key P' hP' h2]
  refine ⟨Localization.Away (Ideal.Quotient.mk q s), inferInstance, hTd, inferInstance,
    inferInstance, (IsScalarTower.toAlgHom O (B ⧸ q)
      (Localization.Away (Ideal.Quotient.mk q s))).comp (Ideal.Quotient.mkₐ O q), ?_, ?_⟩
  · apply algebraMap_injective_of_uniformizer_ne_zero hϖ
    rw [hϖT]
    intro h
    apply hwq
    apply Ideal.Quotient.eq_zero_iff_mem.1
    apply hTi
    rw [h, map_zero]
  · intro h
    apply heq
    apply Ideal.Quotient.eq_zero_iff_mem.1
    apply hTi
    rw [map_zero]
    exact h
end ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint
theorem _root_.solution {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤) (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 := by
  obtain ⟨T, iT1, iT2, familyTheoremThreeBound, iT4, g, hTinj, hge⟩ := exists_finite_domain_quotient_ne_zero hsp e he
  obtain ⟨C, indexCFirst, indexCSecond, iC3, iC4, iC5, ψ, hψ⟩ := exists_dedekind_embedding_of_finite (O := O) (T := T) hTinj
  have hCinj : Function.Injective (algebraMap O C) := by
    intro a b h
    apply hTinj
    apply hψ
    rw [ψ.commutes, ψ.commutes]
    exact h
  obtain ⟨V, indexVFirst, indexVSecond, indexVThird, indexVFourth, iV5, φ, hφ⟩ := exists_dvr_embedding_of_dedekind (O := O) (C := C) hCinj
  refine ⟨V, indexVFirst, indexVSecond, indexVThird, indexVFourth, iV5, (φ.comp ψ).comp g, ?_⟩
  intro h
  apply hge
  apply hψ
  apply hφ
  rw [map_zero, map_zero]
  exact h
end ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint
