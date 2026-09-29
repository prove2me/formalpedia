-- Prove2me | solution 1 for ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bae9a58c-2863-59fe-81b7-aa8e4aff987f

import Theorems.Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime

open scoped Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace PlaceTransitivity

noncomputable abbrev Zbar : Subalgebra ℤ ℚ̄ := integralClosure ℤ ℚ̄

local notation "ℤ̄" => Zbar

theorem coe_mem (A : ValuationSubring ℚ̄) (b : ℤ̄) : (b : ℚ̄) ∈ A := by
  have hb : IsIntegral ℤ (b : ℚ̄) := b.2
  have hbA : IsIntegral A (b : ℚ̄) := by
    obtain ⟨p, hp, hpb⟩ := hb
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap A ℚ̄).comp (Int.castRingHom A) = algebraMap ℤ ℚ̄ := RingHom.ext_int _ _
    rw [this]
    exact hpb
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := ℚ̄)).mp hbA
  rw [← hy]
  exact y.2

noncomputable def toPlace (A : ValuationSubring ℚ̄) : ℤ̄ →+* A :=
  ((Subalgebra.val ℤ̄).toRingHom).codRestrict A.toSubring (coe_mem A)

@[scoped simp] theorem coe_toPlace (A : ValuationSubring ℚ̄) (b : ℤ̄) : (toPlace A b : ℚ̄) = b := rfl

noncomputable def center (A : ValuationSubring ℚ̄) : Ideal ℤ̄ :=
  Ideal.comap (toPlace A) (IsLocalRing.maximalIdeal A)

theorem mem_center_iff {A : ValuationSubring ℚ̄} {b : ℤ̄} :
    b ∈ center A ↔ (b : ℚ̄) ∈ A.nonunits := by
  rw [center, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_toPlace]

scoped instance center_isPrime (A : ValuationSubring ℚ̄) : (center A).IsPrime :=
  Ideal.comap_isPrime _ _

theorem center_under {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄} (hA : A.LiesOverPrime q) :
    (center A).under ℤ = Ideal.span {(q : ℤ)} := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  refine (hmax.eq_of_le ?_ ?_).symm
  · exact Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ ℤ̄ (q : ℤ) ∈ center A
    rw [mem_center_iff]
    have : ((algebraMap ℤ ℤ̄ (q : ℤ) : ℤ̄) : ℚ̄) = (q : ℚ̄) := by
      rw [map_natCast]; rfl
    rw [this]
    exact hA

theorem mem_smul_nonunits_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {τ : L ≃ₐ[K] L} {A : ValuationSubring L} {x : L} :
    x ∈ (τ • A).nonunits ↔ τ.symm x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  have e0 : x = 0 ↔ τ.symm x = 0 := by
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; simpa using congrArg τ h
  have e1 : x⁻¹ ∈ τ • A ↔ (τ.symm x)⁻¹ ∈ A := by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have : (τ⁻¹ : L ≃ₐ[K] L) • x⁻¹ = (τ.symm x)⁻¹ := by
      show τ.symm x⁻¹ = (τ.symm x)⁻¹
      exact map_inv₀ _ _
    rw [this]
  rw [e0, e1]

theorem le_of_forall_not_mem_nonunits {q : ℕ} (hq : q.Prime) {V W : ValuationSubring ℚ̄}
    (hV : V.LiesOverPrime q)
    (h : ∀ s : ℤ̄, (s : ℚ̄) ∉ V.nonunits → (s : ℚ̄) ∉ W.nonunits) : V ≤ W := by
  intro x hx
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime V hq hV x hx
  have hsW : (s : ℚ̄) ∉ W.nonunits := h s hs
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hsW
  obtain ⟨hs0, hsinv⟩ := hsW
  have hx_eq : x = (x' : ℚ̄) * (s : ℚ̄)⁻¹ := by
    rw [← hxs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hx_eq]
  exact W.mul_mem _ _ (coe_mem W x') hsinv

section Bundle

theorem isGalois_Qbar : IsGalois ℚ ℚ̄ := by
  have h : @IsGalois ℚ _ ℚ̄ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

theorem isAlgebraic_Qbar : Algebra.IsAlgebraic ℚ ℚ̄ := by
  have h : @Algebra.IsAlgebraic ℚ ℚ̄ _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
  exact h

end Bundle

theorem exists_smul_center_eq {q : ℕ} (hq : q.Prime) {A A₀ : ValuationSubring ℚ̄}
    (hA : A.LiesOverPrime q) (hA₀ : A₀.LiesOverPrime q) :
    ∃ g : ℚ̄ ≃ₐ[ℚ] ℚ̄, center A₀ = g • center A := by
  classical
  haveI := isGalois_Qbar
  haveI := isAlgebraic_Qbar
  haveI : Algebra.IsIntegral ℚ ℚ̄ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  letI : TopologicalSpace ℤ̄ := ⊥
  haveI : DiscreteTopology ℤ̄ := ⟨rfl⟩
  haveI : ContinuousSMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) ℤ̄ := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(b : ℚ̄)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : ℚ̄))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {(b : ℚ̄)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (b : ℚ̄) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : ℚ̄))
  haveI : Algebra.IsInvariant ℤ ℤ̄ (ℚ̄ ≃ₐ[ℚ] ℚ̄) := ⟨fun b hb => by
    have hb' : (b : ℚ̄) ∈ Set.range (algebraMap ℚ ℚ̄) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : ℤ̄ => (z : ℚ̄)) (hb g)
    obtain ⟨r, hr⟩ := hb'
    have hrint : IsIntegral ℤ r := by
      have h := b.2
      rw [mem_integralClosure_iff, ← hr] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℚ̄)
        (algebraMap ℚ ℚ̄).injective).mp h
    obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
    refine ⟨n, Subtype.ext ?_⟩
    show ((algebraMap ℤ ℤ̄ n : ℤ̄) : ℚ̄) = b
    rw [← hr, ← hn]
    simp⟩
  have hu : (center A).under ℤ = (center A₀).under ℤ := by
    rw [center_under hq hA, center_under hq hA₀]
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := ℤ) (G := ℚ̄ ≃ₐ[ℚ] ℚ̄) (center A) (center A₀) hu

end PlaceTransitivity
p2m_reactivate "P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.PlaceTransitivity"

namespace PlaceTransitivity

theorem smul_eq_of_smul_center_eq {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄}
    (hA : A.LiesOverPrime q) {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g • center A = center A) : g • A = A := by
  classical
  have key : ∀ s : Zbar, (s : ℚ̄) ∈ (g • A).nonunits ↔ (s : ℚ̄) ∈ A.nonunits := by
    intro s
    rw [mem_smul_nonunits_iff, ← mem_center_iff (A := A), ← hg,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff]
    have : ((g⁻¹ • s : Zbar) : ℚ̄) = g.symm s := by
      rw [integralClosure.coe_smul, AlgEquiv.smul_def, AlgEquiv.aut_inv]
    rw [this]
  have hgA : (g • A).LiesOverPrime q := by
    show (q : ℚ̄) ∈ (g • A).nonunits
    rw [mem_smul_nonunits_iff, map_natCast]
    exact hA
  apply le_antisymm
  · exact le_of_forall_not_mem_nonunits hq hgA fun s hs => fun h => hs ((key s).mpr h)
  · exact le_of_forall_not_mem_nonunits hq hA fun s hs => fun h => hs ((key s).mp h)

theorem exists_frobenius_algEquiv {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄}
    [(center A).LiesOver (Ideal.span {(q : ℤ)})] :
    ∃ f : (Zbar ⧸ center A) ≃ₐ[ℤ ⧸ Ideal.span {(q : ℤ)}] (Zbar ⧸ center A),
      ∀ b : Zbar, f (Ideal.Quotient.mk (center A) b) = (Ideal.Quotient.mk (center A) b) ^ q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩

  have hqmem : ((q : ℤ) : Zbar) ∈ center A := by
    have := (Ideal.mem_of_liesOver (center A) (Ideal.span {(q : ℤ)}) (q : ℤ)).mp
      (Ideal.mem_span_singleton_self _)
    simpa using this
  haveI : CharP (Zbar ⧸ center A) q := by
    rw [CharP.charP_iff_prime_eq_zero hq]
    have : ((q : ℕ) : Zbar ⧸ center A) = Ideal.Quotient.mk (center A) ((q : ℤ) : Zbar) := by
      simp
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqmem
  let fr : (Zbar ⧸ center A) →+* (Zbar ⧸ center A) := frobenius (Zbar ⧸ center A) q
  have fr_apply : ∀ y, fr y = y ^ q := fun y => rfl

  let fa : (Zbar ⧸ center A) →ₐ[ℤ ⧸ Ideal.span {(q : ℤ)}] (Zbar ⧸ center A) :=
    { fr with
      commutes' := fun r => by
        obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
        show fr (Ideal.Quotient.mk (center A) (algebraMap ℤ Zbar n)) =
          Ideal.Quotient.mk (center A) (algebraMap ℤ Zbar n)
        rw [eq_intCast, map_intCast, map_intCast] }
  have fa_apply : ∀ y, fa y = y ^ q := fun y => rfl

  have hinj : Function.Injective fa := by
    intro y₁ y₂ h
    rw [fa_apply, fa_apply] at h
    exact frobenius_inj (Zbar ⧸ center A) q h
  have hsurj : Function.Surjective fa := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (b : ℚ̄) hq.pos
    have hcint : IsIntegral ℤ c := by
      refine IsIntegral.of_pow hq.pos ?_
      rw [hc]; exact b.2
    refine ⟨Ideal.Quotient.mk (center A) ⟨c, hcint⟩, ?_⟩
    rw [fa_apply, ← map_pow]
    congr 1
    exact Subtype.ext hc
  exact ⟨AlgEquiv.ofBijective fa ⟨hinj, hsurj⟩, fun b => rfl⟩

end PlaceTransitivity
p2m_reactivate "P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.PlaceTransitivity"

open PlaceTransitivity in

theorem solution {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q := by
  classical

  haveI := isGalois_Qbar
  haveI := isAlgebraic_Qbar
  haveI : Algebra.IsIntegral ℚ ℚ̄ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  letI : TopologicalSpace Zbar := ⊥
  haveI : DiscreteTopology Zbar := ⟨rfl⟩
  haveI : ContinuousSMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) Zbar := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(b : ℚ̄)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : ℚ̄))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {(b : ℚ̄)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (b : ℚ̄) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : ℚ̄))
  haveI : Algebra.IsInvariant ℤ Zbar (ℚ̄ ≃ₐ[ℚ] ℚ̄) := ⟨fun b hb => by
    have hb' : (b : ℚ̄) ∈ Set.range (algebraMap ℚ ℚ̄) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : Zbar => (z : ℚ̄)) (hb g)
    obtain ⟨r, hr⟩ := hb'
    have hrint : IsIntegral ℤ r := by
      have h := b.2
      rw [mem_integralClosure_iff, ← hr] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℚ̄)
        (algebraMap ℚ ℚ̄).injective).mp h
    obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
    refine ⟨n, Subtype.ext ?_⟩
    show ((algebraMap ℤ Zbar n : Zbar) : ℚ̄) = b
    rw [← hr, ← hn]
    simp⟩

  haveI hover : (center A).LiesOver (Ideal.span {(q : ℤ)}) := ⟨(center_under hq hA).symm⟩
  obtain ⟨f, hf⟩ := exists_frobenius_algEquiv (A := A) hq
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal.span {(q : ℤ)}) (center A) f

  have hgQ : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • center A = center A := g.2
  have hgA : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • A = A := smul_eq_of_smul_center_eq hq hA hgQ
  have hgD : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ A.decompositionSubgroup ℚ := MulAction.mem_stabilizer_iff.mpr hgA
  refine ⟨g, hgD, ?_⟩

  let ψ : Zbar →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp (toPlace A)
  have hψ : ∀ b : Zbar, ψ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • b) = ψ b ^ q := by
    intro b
    have h1 : Ideal.Quotient.mk (center A) (g • b) = (Ideal.Quotient.mk (center A) b) ^ q := by
      rw [← hf b, ← hg, Ideal.Quotient.stabilizerHom_apply]
    rw [← map_pow, Ideal.Quotient.eq] at h1
    have h1' : toPlace A (g • b) - toPlace A (b ^ q) ∈ IsLocalRing.maximalIdeal A := by
      have := h1
      unfold center at this
      rw [Ideal.mem_comap, map_sub] at this
      exact this
    have h2 := (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal A)).mpr h1'
    show IsLocalRing.residue A (toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • b)) =
      (IsLocalRing.residue A (toPlace A b)) ^ q
    rw [← map_pow, ← map_pow]
    exact h2

  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime A hq hA a a.2
  set d : A.decompositionSubgroup ℚ := ⟨g, hgD⟩
  have hψs : ψ s ≠ 0 := by
    intro h0
    apply hs
    have : toPlace A s ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.residue_eq_zero_iff _).mp h0
    rw [← ValuationSubring.coe_mem_nonunits_iff] at this
    exact this

  have e1 : a * toPlace A s = toPlace A x' := Subtype.ext hxs
  have e2 : (d • a) * toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • s) = toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • x') := by
    apply Subtype.ext
    show (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (a : ℚ̄) * (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (s : ℚ̄) = (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x' : ℚ̄)
    rw [← map_mul, hxs]
  have e1' : IsLocalRing.residue A a * ψ s = ψ x' := by
    show IsLocalRing.residue A a * IsLocalRing.residue A (toPlace A s) =
      IsLocalRing.residue A (toPlace A x')
    rw [← map_mul, e1]
  have e2' : IsLocalRing.residue A (d • a) * ψ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • s) =
      ψ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • x') := by
    show IsLocalRing.residue A (d • a) * IsLocalRing.residue A (toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • s)) =
      IsLocalRing.residue A (toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • x'))
    rw [← map_mul, e2]
  rw [hψ s, hψ x', ← e1', mul_pow] at e2'
  have hcancel := mul_right_cancel₀ (pow_ne_zero q hψs) e2'
  show d • IsLocalRing.residue A a = (IsLocalRing.residue A a) ^ q
  have : d • (IsLocalRing.residue A a) = IsLocalRing.residue A (d • a) :=
    (IsLocalRing.ResidueField.residue_smul (A.decompositionSubgroup ℚ) d a).symm
  exact this.trans hcancel

end S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime (solution)
