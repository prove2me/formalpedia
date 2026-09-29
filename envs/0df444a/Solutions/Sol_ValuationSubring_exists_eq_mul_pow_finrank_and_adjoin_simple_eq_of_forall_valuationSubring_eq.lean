-- Prove2me | solution 1 for ValuationSubring.exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/29ebd110-2179-506c-b6da-765659ea3b22

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
import Theorems.Thm_existsUnique_valuationSubring_of_pow_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq

set_option autoImplicit false

noncomputable section

open IsLocalRing IsDedekindDomain
open scoped IntermediateField Polynomial

namespace TubeMaxConst

section ValSub

theorem mem_nonunits_iff_inv_not_mem {K : Type*} [Field K] (O : ValuationSubring K) {s : K} (hs0 : s ≠ 0) :
    s ∈ O.nonunits ↔ s⁻¹ ∉ O := by
  have h := O.inv_mem_nonunits_iff (x := s⁻¹)
  rw [inv_inv] at h
  rw [h]
  constructor
  · rintro (h0 | h0)
    · exact absurd (inv_eq_zero.mp h0) hs0
    · exact h0
  · exact fun h0 => Or.inr h0

theorem zero_mem_nonunits {K : Type*} [Field K] (O : ValuationSubring K) : (0 : K) ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one

theorem mem_nonunits_comap_iff {K : Type*} [Field K] {E : Type*} [Field E] (X : ValuationSubring K) (φ : E →+* K) (e : E) :
    e ∈ (X.comap φ).nonunits ↔ φ e ∈ X.nonunits := by
  by_cases he0 : e = 0
  · subst he0
    rw [map_zero]
    exact ⟨fun _ => zero_mem_nonunits X, fun _ => zero_mem_nonunits _⟩
  · rw [mem_nonunits_iff_inv_not_mem _ he0, ValuationSubring.mem_comap, map_inv₀,
      mem_nonunits_iff_inv_not_mem X ((map_ne_zero φ).mpr he0)]

theorem mem_of_isIntegral {K : Type*} [Field K] (V : ValuationSubring K) {x : K} (h : IsIntegral V x) : x ∈ V := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := V) (A := K)).mp h
  rw [← hy]; exact y.2

end ValSub

section Constants

theorem irreducible_of_residue {L : Type*} [Field L] (A : ValuationSubring L) (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C] (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ϖ ≠ 0) : Irreducible ϖ := by
  have hres1 : IsLocalRing.residue A ⟨((1 : ↥C) : L), hC _ (1 : ↥C).2⟩ ≠ 0 := by
    have : (⟨((1 : ↥C) : L), hC _ (1 : ↥C).2⟩ : A) = 1 := rfl
    rw [this, map_one]; exact one_ne_zero
  have hϖu : ¬ IsUnit ϖ := by
    intro hu
    apply hres1
    rw [hϖ]
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    exact ⟨w, hw.symm⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible ↥C
  obtain ⟨k, w, hkw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hp
  have hresϖ : IsLocalRing.residue A ⟨((ϖ : ↥C) : L), hC _ ϖ.2⟩ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one _).symm⟩
  have hresp : IsLocalRing.residue A ⟨((p : ↥C) : L), hC _ p.2⟩ = 0 := by
    by_contra hne
    have hpu : IsUnit (⟨((p : ↥C) : L), hC _ p.2⟩ : A) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne
    have hwu : IsUnit (⟨(((w : ↥C) : ↥C) : L), hC _ (w : ↥C).2⟩ : A) := by
      obtain ⟨wi, hwi⟩ := (Units.isUnit w).exists_right_inv
      refine IsUnit.of_mul_eq_one (⟨((wi : ↥C) : L), hC _ wi.2⟩ : A) ?_
      apply Subtype.ext
      change ((w : ↥C) : L) * (wi : L) = 1
      rw [← Subring.coe_mul, hwi]; rfl
    have hϖA : (⟨((ϖ : ↥C) : L), hC _ ϖ.2⟩ : A) =
        ⟨(((w : ↥C) : ↥C) : L), hC _ (w : ↥C).2⟩ * ⟨((p : ↥C) : L), hC _ p.2⟩ ^ k := by
      apply Subtype.ext
      change ((ϖ : ↥C) : L) = ((w : ↥C) : L) * ((p : ↥C) : L) ^ k
      rw [hkw, Subring.coe_mul, Subring.coe_pow]
    have : IsUnit (⟨((ϖ : ↥C) : L), hC _ ϖ.2⟩ : A) := by rw [hϖA]; exact hwu.mul (hpu.pow k)
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr this) hresϖ
  obtain ⟨d', hd'⟩ := (hϖ p).mp hresp
  rcases hp.isUnit_or_isUnit hd' with hu | hu
  · exact absurd hu hϖu
  · have hassoc : Associated p ϖ := ⟨(hu.unit)⁻¹, by
      rw [hd', mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
    exact hassoc.irreducible hp

theorem mem_of_isIntegral_constants {L : Type*} [Field L] (A : ValuationSubring L) (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    {z : L} (hz : IsIntegral ↥C z) : z ∈ A := by
  apply mem_of_isIntegral A
  obtain ⟨p, hp, hpz⟩ := hz
  set jCA : ↥C →+* ↥A := (C.subtype).codRestrict A (fun c => hC c c.2) with hjCA
  refine ⟨p.map jCA, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (algebraMap (↥A) L).comp jCA = algebraMap (↥C) L := RingHom.ext (fun _ => rfl)
  rw [this]
  exact hpz

end Constants

end TubeMaxConst

open TubeMaxConst in
set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem solution
    {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L)
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A) [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    (hκ : ∀ a : ↥A, ∃ c : ↥C, a - ⟨(c : L), hC c c.2⟩ ∈ maximalIdeal ↥A)
    (huniq : ∀ V : ValuationSubring L, (∀ c : L, c ∈ C → c ∈ V) → ((ϖ : ↥C) : L) ∈ V.nonunits → V = A)
    (K₀ : Type*) [Field K₀] [Algebra ↥C K₀] [IsFractionRing ↥C K₀] [Algebra K₀ L] [IsScalarTower ↥C K₀ L]
    (K₁ : IntermediateField K₀ L) [FiniteDimensional K₀ ↥K₁] :
    ∃ ϖ₁ v w : L, ϖ₁ ∈ K₁ ∧ v ∈ K₁ ∧ w ∈ K₁ ∧
      IsIntegral ↥C ϖ₁ ∧ IsIntegral ↥C v ∧ IsIntegral ↥C w ∧ v * w = 1 ∧
      ((ϖ : ↥C) : L) = v * ϖ₁ ^ Module.finrank K₀ ↥K₁ ∧
      K₀⟮ϖ₁⟯ = K₁ := by

  haveI : CharZero K₀ := (algebraMap K₀ L).charZero
  haveI : IsScalarTower (↥C) (↥K₁) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hCK₁L : ∀ c : ↥C, ((algebraMap (↥C) (↥K₁) c : ↥K₁) : L) = (c : L) := fun _ => rfl
  have hinjCK₁ : Function.Injective (algebraMap (↥C) (↥K₁)) := by
    intro a b h
    have := congrArg (fun z : ↥K₁ => (z : L)) h
    simp only [hCK₁L] at this
    exact Subtype.ext this
  haveI : Module.IsTorsionFree (↥C) (↥K₁) := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinjCK₁
  haveI : Module.IsTorsionFree (↥C) (↥(integralClosure (↥C) (↥K₁))) := inferInstance
  haveI : IsDedekindDomain (↥(integralClosure (↥C) (↥K₁))) := integralClosure.isDedekindDomain (↥C) K₀ (↥K₁)
  haveI : Module.Finite (↥C) (↥(integralClosure (↥C) (↥K₁))) :=
    IsIntegralClosure.finite (↥C) K₀ (↥K₁) (↥(integralClosure (↥C) (↥K₁)))
  haveI : IsFractionRing (↥(integralClosure (↥C) (↥K₁))) (↥K₁) :=
    integralClosure.isFractionRing_of_finite_extension K₀ (↥K₁)
  have h1E : ∀ s : ↥(integralClosure (↥C) (↥K₁)), algebraMap _ (↥K₁) s = (s : ↥K₁) := fun _ => rfl
  have h01 : ∀ c : ↥C, ((algebraMap (↥C) (↥(integralClosure (↥C) (↥K₁))) c : ↥(integralClosure (↥C) (↥K₁))) : ↥K₁)
      = algebraMap (↥C) (↥K₁) c := fun _ => rfl
  have hinj0S : Function.Injective (algebraMap (↥C) (↥(integralClosure (↥C) (↥K₁)))) := by
    intro a b h
    have := congrArg (fun z : ↥(integralClosure (↥C) (↥K₁)) => (z : ↥K₁)) h
    simp only [h01] at this
    exact hinjCK₁ this
  haveI : FaithfulSMul (↥C) (↥(integralClosure (↥C) (↥K₁))) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj0S

  have hϖC0 : ϖ ≠ 0 := fun h => hϖ0 (by rw [h]; rfl)
  have hirr : Irreducible ϖ := irreducible_of_residue A C hC ϖ hϖ hϖC0
  have hmC : maximalIdeal (↥C) = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  have hmC0 : maximalIdeal (↥C) ≠ ⊥ := IsDiscreteValuationRing.not_a_field ↥C
  have hmCA : ∀ c : ↥C, c ∈ maximalIdeal (↥C) ↔ (⟨(c : L), hC c c.2⟩ : ↥A) ∈ maximalIdeal ↥A := by
    intro c
    rw [hmC, Ideal.mem_span_singleton', ← IsLocalRing.residue_eq_zero_iff, hϖ]
    constructor
    · rintro ⟨d, hd⟩; exact ⟨d, by rw [← hd, mul_comm]⟩
    · rintro ⟨d, hd⟩; exact ⟨d, by rw [hd, mul_comm]⟩

  have hSint : ∀ s : ↥(integralClosure (↥C) (↥K₁)), IsIntegral (↥C) (((s : ↥K₁) : L)) := by
    intro s
    obtain ⟨p, hp, hps⟩ := (mem_integralClosure_iff (↥C) (↥K₁)).mp s.2
    refine ⟨p, hp, ?_⟩
    have := congrArg (algebraMap (↥K₁) L) hps
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  have hSA : ∀ s : ↥(integralClosure (↥C) (↥K₁)), ((s : ↥K₁) : L) ∈ A := fun s =>
    mem_of_isIntegral_constants A C hC (hSint s)
  set φSA : ↥(integralClosure (↥C) (↥K₁)) →+* ↥A :=
    ((algebraMap (↥K₁) L).comp (algebraMap (↥(integralClosure (↥C) (↥K₁))) (↥K₁))).codRestrict A hSA with hφSA
  have hφSA_apply : ∀ s, ((φSA s : ↥A) : L) = ((s : ↥K₁) : L) := fun _ => rfl
  set QA : Ideal ↥(integralClosure (↥C) (↥K₁)) := (maximalIdeal ↥A).comap φSA with hQAdef
  have hQA : ∀ s, s ∈ QA ↔ ((s : ↥K₁) : L) ∈ A.nonunits := by
    intro s
    rw [hQAdef, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  haveI hQAp : QA.IsPrime := Ideal.comap_isPrime _ _

  have hclaim : ∀ Q : Ideal ↥(integralClosure (↥C) (↥K₁)), Q.IsPrime →
      algebraMap (↥C) _ ϖ ∈ Q → Q = QA := by
    intro Q hQ hϖQ
    haveI := hQ
    have hunits : ∀ s : Q.primeCompl, IsUnit (algebraMap (↥(integralClosure (↥C) (↥K₁))) (↥K₁) s) := by
      intro s
      apply IsUnit.mk0
      intro h0
      apply s.2
      have : (s : ↥(integralClosure (↥C) (↥K₁))) = 0 := by
        apply Subtype.ext
        rw [h1E] at h0
        exact h0
      rw [this]; exact Q.zero_mem
    set ψ : Localization.AtPrime Q →+* ↥K₁ := IsLocalization.lift (M := Q.primeCompl) hunits with hψ
    have hψ_alg : ∀ z : ↥(integralClosure (↥C) (↥K₁)), ψ (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z) = (z : ↥K₁) :=
      fun z => IsLocalization.lift_eq hunits z
    set φ : Localization.AtPrime Q →+* L := (algebraMap (↥K₁) L).comp ψ with hφ
    have hφ_alg : ∀ z : ↥(integralClosure (↥C) (↥K₁)), φ (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z) = ((z : ↥K₁) : L) := by
      intro z; change algebraMap (↥K₁) L (ψ _) = _; rw [hψ_alg]; rfl
    obtain ⟨V, hVmem, hVloc⟩ := IsLocalRing.exists_factor_valuationRing φ
    have hdom : ∀ z : ↥(integralClosure (↥C) (↥K₁)), z ∈ Q ↔ ((z : ↥K₁) : L) ∈ V.nonunits := by
      intro z
      constructor
      · intro hz
        have hm : algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z ∈ maximalIdeal (Localization.AtPrime Q) :=
          (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q z).mpr hz
        have hnu : ¬ IsUnit (φ.codRestrict V.toSubring hVmem (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z)) :=
          fun hu => (mem_maximalIdeal _ |>.mp hm) (IsLocalHom.map_nonunit _ hu)
        have hmax : (⟨φ (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z), hVmem _⟩ : V) ∈ maximalIdeal V := hnu
        rw [← hφ_alg]
        exact ValuationSubring.coe_mem_nonunits_iff.mpr hmax
      · intro hz
        by_contra hzQ
        have hu : IsUnit (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z) :=
          IsLocalization.map_units (Localization.AtPrime Q) (⟨z, hzQ⟩ : Q.primeCompl)
        have hu' : IsUnit (φ.codRestrict V.toSubring hVmem (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z)) := hu.map _
        have hmax : (⟨φ (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z), hVmem _⟩ : V) ∈ maximalIdeal V := by
          rw [← ValuationSubring.coe_mem_nonunits_iff]
          change φ (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) z) ∈ V.nonunits
          rwa [hφ_alg]
        exact (mem_maximalIdeal _ |>.mp hmax) hu'
    have hCV : ∀ c : L, c ∈ C → c ∈ V := by
      intro c hc
      have := hVmem (algebraMap (↥(integralClosure (↥C) (↥K₁))) (Localization.AtPrime Q) (algebraMap (↥C) _ ⟨c, hc⟩))
      rw [hφ_alg, h01, hCK₁L] at this
      exact this
    have hϖV : ((ϖ : ↥C) : L) ∈ V.nonunits := by
      have := (hdom _).mp hϖQ
      rwa [h01, hCK₁L] at this
    have hVA : V = A := huniq V hCV hϖV
    ext s
    rw [hdom, hQA, hVA]

  have hϖQA : algebraMap (↥C) _ ϖ ∈ QA := by
    rw [hQA, h01, hCK₁L]
    exact ValuationSubring.coe_mem_nonunits_iff.mpr ((hmCA ϖ).mp (hmC ▸ Ideal.mem_span_singleton_self ϖ))
  have hQA0 : QA ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hϖQA
    exact hϖC0 (hinj0S (by rw [hϖQA, map_zero]))
  haveI hQAover : QA.LiesOver (maximalIdeal ↥C) := by
    refine ⟨?_⟩
    ext c
    rw [Ideal.under_def, Ideal.mem_comap, hQA, h01, hCK₁L, hmCA c]
    exact ValuationSubring.coe_mem_nonunits_iff.symm
  have hQAmax : QA.IsMaximal := hQAp.isMaximal hQA0

  haveI hSloc : IsLocalRing ↥(integralClosure (↥C) (↥K₁)) := by
    refine IsLocalRing.of_unique_max_ideal ⟨QA, hQAmax, fun M hM => ?_⟩
    refine hclaim M hM.isPrime ?_
    haveI := hM
    have hMu : (M.under ↥C) = maximalIdeal ↥C :=
      IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under (↥C) M)
    have : ϖ ∈ M.under ↥C := by rw [hMu, hmC]; exact Ideal.mem_span_singleton_self ϖ
    rwa [Ideal.under_def, Ideal.mem_comap] at this
  have hQAm : QA = maximalIdeal _ := IsLocalRing.eq_maximalIdeal hQAmax
  have hunitS : ∀ s : ↥(integralClosure (↥C) (↥K₁)), s ∉ QA → IsUnit s := by
    intro s hs
    by_contra hu
    exact hs (hQAm ▸ (mem_maximalIdeal _).mpr hu)

  have hf : (maximalIdeal ↥C).inertiaDeg' QA = 1 := by
    rw [Ideal.inertiaDeg_algebraMap]
    have hsurj : Function.Surjective (algebraMap (↥C ⧸ maximalIdeal ↥C) (↥(integralClosure (↥C) (↥K₁)) ⧸ QA)) := by
      intro q
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨c, hc⟩ := hκ (φSA s)
      refine ⟨Ideal.Quotient.mk _ c, ?_⟩
      change Ideal.Quotient.mk QA (algebraMap (↥C) _ c) = Ideal.Quotient.mk QA s
      rw [Ideal.Quotient.eq, hQAdef, Ideal.mem_comap, map_sub]
      have : φSA (algebraMap (↥C) _ c) = ⟨(c : L), hC c c.2⟩ := Subtype.ext (by rw [hφSA_apply, h01, hCK₁L])
      rw [this, ← neg_sub]
      exact neg_mem_iff.mpr hc
    have hinj : Function.Injective (algebraMap (↥C ⧸ maximalIdeal ↥C) (↥(integralClosure (↥C) (↥K₁)) ⧸ QA)) := by
      letI : Field (↥C ⧸ maximalIdeal ↥C) := Ideal.Quotient.field (maximalIdeal ↥C)
      exact RingHom.injective _
    have e := LinearEquiv.ofBijective (Algebra.linearMap (↥C ⧸ maximalIdeal ↥C) (↥(integralClosure (↥C) (↥K₁)) ⧸ QA))
      ⟨hinj, hsurj⟩
    rw [← e.finrank_eq, Module.finrank_self]

  set n := Module.finrank K₀ ↥K₁ with hn
  have he : (maximalIdeal ↥C).ramificationIdx' QA = n := by
    have hsum := Ideal.sum_ramification_inertia (R := ↥C) (↥(integralClosure (↥C) (↥K₁))) K₀ (↥K₁)
      (p := maximalIdeal ↥C) hmC0
    rw [IsLocalRing.primesOverFinset_eq _ hmC0, Finset.sum_singleton, ← hQAm, hf, mul_one] at hsum
    exact hsum
  have hover : (maximalIdeal ↥C).primesOver ↥(integralClosure (↥C) (↥K₁)) = {QA} := by
    rw [hQAm]; exact IsLocalRing.primesOver_eq _ hmC0

  obtain ⟨W, hW⟩ : ∃ W : ValuationSubring ↥K₁, W = HeightOneSpectrum.valuationSubringAtPrime (↥K₁)
      (⟨QA, hQAp, hQA0⟩ : HeightOneSpectrum ↥(integralClosure (↥C) (↥K₁))) := ⟨_, rfl⟩
  obtain ⟨huniqW, hOW, hOWiff, -, π₁, v, -, hϖeq⟩ :=
    IsDiscreteValuationRing.forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton
      (O := ↥C) (↥K₁) ϖ hirr n QA hQA0 hover he hf W hW

  have hWS : ∀ w : ↥K₁, w ∈ W → ∃ s : ↥(integralClosure (↥C) (↥K₁)), (s : ↥K₁) = w := by
    intro w hw
    rw [hW] at hw
    have hw' : w ∈ (HeightOneSpectrum.valuationSubringAtPrime (↥K₁)
      (⟨QA, hQAp, hQA0⟩ : HeightOneSpectrum ↥(integralClosure (↥C) (↥K₁)))).toSubring := hw
    rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring] at hw'
    obtain ⟨a, s, hs, rfl⟩ := hw'
    have hsQ : s ∉ QA := hs
    obtain ⟨su, hsu⟩ := hunitS s hsQ
    refine ⟨a * ((su⁻¹ : (↥(integralClosure (↥C) (↥K₁)))ˣ) : ↥(integralClosure (↥C) (↥K₁))), ?_⟩
    rw [Subalgebra.coe_mul, h1E, h1E]
    congr 1
    symm
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hsu, ← Subalgebra.coe_mul, Units.mul_inv]
    rfl

  obtain ⟨sπ, hsπ⟩ := hWS _ π₁.2
  obtain ⟨sv, hsv⟩ := hWS _ (v : ↥W).2
  obtain ⟨sw, hsw⟩ := hWS _ ((v⁻¹ : (↥W)ˣ) : ↥W).2
  set ϖ₁ : L := (((π₁ : ↥W) : ↥K₁) : L) with hϖ₁def
  set vL : L := (((v : ↥W) : ↥K₁) : L) with hvLdef
  set wL : L := ((((v⁻¹ : (↥W)ˣ) : ↥W) : ↥K₁) : L) with hwLdef
  have hϖ₁K : ϖ₁ ∈ K₁ := ((π₁ : ↥W) : ↥K₁).2
  have hvK₁ : vL ∈ K₁ := ((v : ↥W) : ↥K₁).2
  have hwK₁ : wL ∈ K₁ := (((v⁻¹ : (↥W)ˣ) : ↥W) : ↥K₁).2
  have hϖ₁i : IsIntegral (↥C) ϖ₁ := by rw [hϖ₁def, ← hsπ]; exact hSint sπ
  have hvi : IsIntegral (↥C) vL := by rw [hvLdef, ← hsv]; exact hSint sv
  have hwi : IsIntegral (↥C) wL := by rw [hwLdef, ← hsw]; exact hSint sw
  have hvw : vL * wL = 1 := by
    have h1 : ((v : ↥W) : ↥K₁) * (((v⁻¹ : (↥W)ˣ) : ↥W) : ↥K₁) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv]; rfl
    have := congrArg (algebraMap (↥K₁) L) h1
    rwa [map_mul, map_one] at this
  have hϖL : ((ϖ : ↥C) : L) = vL * ϖ₁ ^ n := by
    have := congrArg (algebraMap (↥K₁) L) hϖeq
    rw [map_mul, map_pow] at this
    exact this
  refine ⟨ϖ₁, vL, wL, hϖ₁K, hvK₁, hwK₁, hϖ₁i, hvi, hwi, hvw, hϖL, ?_⟩

  have hn0 : 0 < n := Module.finrank_pos
  have hle : K₀⟮ϖ₁⟯ ≤ K₁ := IntermediateField.adjoin_simple_le_iff.mpr hϖ₁K
  have hϖ₁K₀ : IsIntegral K₀ ϖ₁ := hϖ₁i.tower_top
  haveI : FiniteDimensional K₀ ↥K₀⟮ϖ₁⟯ := IntermediateField.adjoin.finiteDimensional hϖ₁K₀
  have hfin : Module.finrank K₀ ↥K₀⟮ϖ₁⟯ ≤ n := IntermediateField.finrank_le_of_le_right hle
  have hϖK : ((ϖ : ↥C) : L) ∈ K₀⟮ϖ₁⟯ := by
    have : ((ϖ : ↥C) : L) = algebraMap K₀ L (algebraMap (↥C) K₀ ϖ) := IsScalarTower.algebraMap_apply _ _ _ ϖ
    rw [this]
    exact IntermediateField.algebraMap_mem _ _
  have hwϖ : wL * ((ϖ : ↥C) : L) = ϖ₁ ^ n := by
    calc wL * ((ϖ : ↥C) : L) = wL * (vL * ϖ₁ ^ n) := by rw [← hϖL]
      _ = vL * wL * ϖ₁ ^ n := by ring
      _ = ϖ₁ ^ n := by rw [hvw, one_mul]
  have hwL : wL = ϖ₁ ^ n * (((ϖ : ↥C) : L))⁻¹ := (eq_mul_inv_iff_mul_eq₀ hϖ0).mpr hwϖ
  have hwK : wL ∈ K₀⟮ϖ₁⟯ := by
    rw [hwL]
    exact mul_mem (pow_mem (IntermediateField.mem_adjoin_simple_self K₀ ϖ₁) n) (inv_mem hϖK)
  have hvL : vL = wL⁻¹ := eq_inv_of_mul_eq_one_left hvw
  have hvK : vL ∈ K₀⟮ϖ₁⟯ := by rw [hvL]; exact inv_mem hwK
  haveI : IsScalarTower (↥C) (↥K₀⟮ϖ₁⟯) L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  set ϖE : ↥K₀⟮ϖ₁⟯ := ⟨ϖ₁, IntermediateField.mem_adjoin_simple_self K₀ ϖ₁⟩ with hϖE
  set uE : ↥K₀⟮ϖ₁⟯ := ⟨wL, hwK⟩ with huE
  set vE : ↥K₀⟮ϖ₁⟯ := ⟨vL, hvK⟩ with hvE
  have hinjE : Function.Injective (IsScalarTower.toAlgHom (↥C) (↥K₀⟮ϖ₁⟯) L) := fun a b h => Subtype.ext h
  have huint : IsIntegral (↥C) uE :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (↥C) (↥K₀⟮ϖ₁⟯) L) hinjE (x := uE)).mp hwi
  have hvint : IsIntegral (↥C) vE :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom (↥C) (↥K₀⟮ϖ₁⟯) L) hinjE (x := vE)).mp hvi
  have huvE : uE * vE = 1 := Subtype.ext (by change wL * vL = 1; rw [mul_comm]; exact hvw)
  have hϖEeq : ϖE ^ n = algebraMap (↥C) (↥K₀⟮ϖ₁⟯) ϖ * uE := by
    apply Subtype.ext
    change ϖ₁ ^ n = ((ϖ : ↥C) : L) * wL
    rw [mul_comm, hwϖ]
  obtain ⟨hdeg, -⟩ := existsUnique_valuationSubring_of_pow_eq_mul (↥C) K₀ (↥K₀⟮ϖ₁⟯) n hn0 hfin ϖ hirr uE vE huvE
    huint hvint ϖE hϖEeq
  exact IntermediateField.eq_of_le_of_finrank_eq hle hdeg

end

end S_ValuationSubring_exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq
end P2MW
export P2MW.S_ValuationSubring_exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq (solution)
