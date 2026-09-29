-- Prove2me | solution 1 for ValuationSubring.exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7ee218f3-793b-5083-9420-b4cf31b12680

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_inf_fixedField_decompositionSubgroup
import Theorems.Thm_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace HensL1

variable (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)

local notation "L" => AlgebraicClosure ℚ

abbrev RD : Subring L := Pl.toSubring ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring

scoped instance instIsAlgebraicL : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ <;>
    first | with_reducible_and_instances rfl | exact Subsingleton.elim _ _

section Field

variable (x : L)

abbrev Kx : IntermediateField ℚ L := IntermediateField.adjoin ℚ {x}

scoped instance : FiniteDimensional ℚ (Kx x) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral

scoped instance : NumberField (Kx x) := NumberField.mk

abbrev Bx : Type := NumberField.RingOfIntegers (Kx x)

noncomputable abbrev toL : Bx x →+* L := (algebraMap (Kx x) L).comp (algebraMap (Bx x) (Kx x))

theorem toL_injective : Function.Injective (toL x) :=
  (algebraMap (Kx x) L).injective.comp (NumberField.RingOfIntegers.coe_injective)

end Field

section Place

variable (x : L)

theorem toL_mem_Pl (b : Bx x) : toL x b ∈ Pl := by
  obtain ⟨f, hf, hfb⟩ := NumberField.RingOfIntegers.isIntegral_coe b

  have hint' : IsIntegral Pl (toL x b) := by
    refine ⟨f.map (Int.castRingHom Pl), hf.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap Pl L).comp (Int.castRingHom Pl)) ((algebraMap (Kx x) L).comp (algebraMap ℤ (Kx x))),
      show toL x b = algebraMap (Kx x) L (algebraMap (Bx x) (Kx x) b) from rfl, ← Polynomial.hom_eval₂]
    exact (congrArg (algebraMap (Kx x) L) hfb).trans (map_zero _)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Pl) (K := L)).mp hint'
  rw [← hy]
  exact y.2

variable {x}
variable (hx : x ∈ RD Pl)

include hx in

theorem Kx_le_fixedField : (Kx x).toSubalgebra ≤ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubalgebra := by
  change Kx x ≤ IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact hx.2

include hx in

theorem toL_mem_RD (b : Bx x) : toL x b ∈ RD Pl :=
  ⟨toL_mem_Pl Pl x b, Kx_le_fixedField Pl hx (algebraMap (Bx x) (Kx x) b).2⟩

variable (x) in

def toPl : Bx x →+* Pl := (toL x).codRestrict Pl.toSubring (toL_mem_Pl Pl x)

@[scoped simp] theorem coe_toPl (b : Bx x) : ((toPl Pl x b : Pl) : L) = toL x b := rfl

def toRD : Bx x →+* RD Pl := (toL x).codRestrict (RD Pl) (toL_mem_RD Pl hx)

@[scoped simp] theorem coe_toRD (b : Bx x) : ((toRD Pl hx b : RD Pl) : L) = toL x b := rfl

variable (x) in

def 𝔮 : Ideal (Bx x) := (maximalIdeal Pl).comap (toPl Pl x)

theorem mem_𝔮_iff (b : Bx x) : b ∈ 𝔮 Pl x ↔ Pl.valuation (toL x b) < 1 := by
  rw [𝔮, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

scoped instance : (𝔮 Pl x).IsPrime := Ideal.IsPrime.comap _

include hPl in
theorem valuation_p_lt_one : Pl.valuation ((p : ℕ) : L) < 1 :=
  (ValuationSubring.mem_nonunits_iff Pl).mp hPl

include hPl in
theorem p_mem_𝔮 : ((p : ℕ) : Bx x) ∈ 𝔮 Pl x := by
  rw [mem_𝔮_iff, map_natCast]
  exact valuation_p_lt_one p Pl hPl

include hPl in
theorem 𝔮_ne_bot : 𝔮 Pl x ≠ ⊥ := by
  intro h
  have := p_mem_𝔮 p Pl hPl (x := x)
  rw [h, Ideal.mem_bot] at this
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)

scoped instance 𝔮_isMaximal [hq : Fact (𝔮 Pl x ≠ ⊥)] : (𝔮 Pl x).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hq.out

theorem comap_𝔮_eq (hPl : Pl.LiesOverPrime p) :
    (𝔮 Pl x).comap (algebraMap ℤ (Bx x)) = Ideal.span {((p : ℕ) : ℤ)} := by
  have hmax : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))).irreducible
  refine (hmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_).symm
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact p_mem_𝔮 p Pl hPl

scoped instance 𝔮_liesOver [hPl : Fact (Pl.LiesOverPrime p)] : (𝔮 Pl x).LiesOver (Ideal.span {((p : ℕ) : ℤ)}) :=
  ⟨(comap_𝔮_eq p Pl hPl.out).symm⟩

end Place

section Unramified

variable {x : L} (hx : x ∈ RD Pl)

theorem not_isUnit_toRD (hPl : Pl.LiesOverPrime p) {b : Bx x} (hb : b ∈ 𝔮 Pl x) : ¬ IsUnit (toRD Pl hx b) := by
  rw [(ValuationSubring.henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup Pl p hPl).2.2]
  exact (mem_𝔮_iff Pl b).mp hb

include hx in

theorem p_not_mem_𝔮_sq (hPl : Pl.LiesOverPrime p) : ((p : ℕ) : Bx x) ∉ 𝔮 Pl x ^ 2 := by
  obtain ⟨hDVR, hirr, -⟩ := ValuationSubring.isDiscreteValuationRing_inf_fixedField_decompositionSubgroup Pl p hPl
  haveI := hDVR
  intro hp2

  have hle : 𝔮 Pl x ≤ (maximalIdeal (RD Pl)).comap (toRD Pl hx) := fun b hb =>
    (mem_maximalIdeal _).mpr (not_isUnit_toRD p Pl hx hPl hb)
  have hp2' : toRD Pl hx ((p : ℕ) : Bx x) ∈ maximalIdeal (RD Pl) ^ 2 :=
    Ideal.le_comap_pow _ 2 (Ideal.pow_right_mono hle 2 hp2)
  rw [map_natCast, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hp2'
  obtain ⟨c, hc⟩ := hp2'
  apply hirr.not_isUnit
  refine IsUnit.of_mul_eq_one (b := c) ?_
  have hp0 : ((p : ℕ) : RD Pl) ≠ 0 := hirr.ne_zero
  apply mul_left_cancel₀ hp0
  rw [mul_one, ← mul_assoc, ← pow_two]
  exact hc.symm

include hx in

theorem isUnramifiedAt_𝔮 (hPl : Pl.LiesOverPrime p) : Algebra.IsUnramifiedAt ℤ (𝔮 Pl x) := by
  have hp0 : (𝔮 Pl x).under ℤ ≠ ⊥ := by
    rw [Ideal.under_def, comap_𝔮_eq p Pl hPl]
    simpa [Ideal.span_singleton_eq_bot] using (Fact.out : p.Prime).ne_zero
  rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ), ← not_ne_iff,
    ← Ideal.ramificationIdx'_eq_ramificationIdx ((𝔮 Pl x).under ℤ) (𝔮 Pl x) hp0, Ideal.under_def,
    Ideal.ramificationIdx_ne_one_iff Ideal.map_comap_le]
  intro hle
  apply p_not_mem_𝔮_sq p Pl hx hPl
  apply hle
  rw [comap_𝔮_eq p Pl hPl, Ideal.map_span, Set.image_singleton, map_natCast]
  exact Ideal.mem_span_singleton_self _

include hx in

theorem isEtaleAt_𝔮 (hPl : Pl.LiesOverPrime p) : Algebra.IsEtaleAt ℤ (𝔮 Pl x) :=
  haveI := isUnramifiedAt_𝔮 p Pl hx hPl
  haveI : Algebra.FinitePresentation ℤ (Bx x) := (Algebra.FinitePresentation.of_finiteType (R := ℤ)).mp inferInstance
  Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (R := ℤ) (𝔮 Pl x)

end Unramified

section Assembly

variable {x : L} (hx : x ∈ RD Pl)

def xK (x : L) : Kx x := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩

@[scoped simp] theorem coe_xK (x : L) : ((xK x : Kx x) : L) = x := rfl

theorem valuation_eq_one_of_not_mem {b : Bx x} (hb : b ∉ 𝔮 Pl x) : Pl.valuation (toL x b) = 1 :=
  le_antisymm (by simpa using Pl.valuation_le_one (toPl Pl x b)) (not_lt.mp ((mem_𝔮_iff Pl b).not.mp hb))

theorem isUnit_toPl_of_not_mem {b : Bx x} (hb : b ∉ 𝔮 Pl x) : IsUnit (toPl Pl x b) := by
  by_contra h
  have : toPl Pl x b ∈ maximalIdeal Pl := (mem_maximalIdeal _).mpr h
  rw [ValuationSubring.valuation_lt_one_iff] at this
  exact hb ((mem_𝔮_iff Pl b).mpr this)

include hx hPl in

theorem exists_mul_eq_of_mem : ∃ (b t : Bx x), t ∉ 𝔮 Pl x ∧ (xK x : Kx x) * algebraMap (Bx x) (Kx x) t = algebraMap (Bx x) (Kx x) b := by
  let v : IsDedekindDomain.HeightOneSpectrum (Bx x) := ⟨𝔮 Pl x, inferInstance, 𝔮_ne_bot p Pl hPl⟩
  obtain ⟨n, d, h | h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := Kx x) (xK x)
  · exact ⟨n, d, d.2, h⟩
  · by_cases hn : n ∈ 𝔮 Pl x
    ·
      exfalso
      apply d.2
      show (d : Bx x) ∈ 𝔮 Pl x
      rw [mem_𝔮_iff]
      have hd : toL x d = x * toL x n := by
        have := congrArg (algebraMap (Kx x) L) h
        rw [map_mul] at this
        exact this.symm
      rw [hd, map_mul]
      calc Pl.valuation x * Pl.valuation (toL x n) ≤ 1 * Pl.valuation (toL x n) :=
            mul_le_mul_left ((Pl.valuation_le_one_iff x).mpr hx.1) _
        _ < 1 := by rw [one_mul]; exact (mem_𝔮_iff Pl n).mp hn
    · exact ⟨d, n, hn, h⟩

include hx hPl in

theorem main : ∃ (E : Type) (_ : CommRing E) (_ : Algebra.Etale ℤ E) (ι : E →+* AlgebraicClosure ℚ) (φ₀ : E →+* ZMod p),
      (∀ e : E, ι e ∈ Pl) ∧
      (∀ (e : E) (n : ℤ), (n : ZMod p) = φ₀ e → Pl.valuation (ι e - n) < 1) ∧
      x ∈ Set.range ι := by
  classical

  haveI := isEtaleAt_𝔮 p Pl hx hPl
  haveI : Algebra.FinitePresentation ℤ (Bx x) := (Algebra.FinitePresentation.of_finiteType (R := ℤ)).mp inferInstance
  obtain ⟨f, hf, hEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := ℤ) (𝔮 Pl x)
  obtain ⟨b, t, ht, hbt⟩ := exists_mul_eq_of_mem p Pl hPl hx
  have hg : f * t ∉ 𝔮 Pl x := fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hf ht)
  let E := Localization.Away (f * t)
  have hE : Algebra.Etale ℤ E := by
    haveI := hEt
    have h1 := (Algebra.basicOpen_subset_etaleLocus_iff (R := ℤ) (f := f)).mpr inferInstance
    have h2 : Algebra.FormallyEtale ℤ E := (Algebra.basicOpen_subset_etaleLocus_iff (R := ℤ) (f := f * t)).mp
      (fun q hq => h1 (PrimeSpectrum.basicOpen_mul_le_left f t hq))
    exact ⟨h2, .of_isLocalizationAway (f * t)⟩

  have huP : IsUnit (toPl Pl x (f * t)) := isUnit_toPl_of_not_mem Pl hg
  have hRDu := (ValuationSubring.henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup Pl p hPl).2.2
  have huRD : IsUnit (toRD Pl hx (f * t)) := by
    by_contra h
    rw [hRDu] at h
    exact hg ((mem_𝔮_iff Pl _).mpr h)
  let ιP : E →+* Pl := IsLocalization.Away.lift (f * t) (g := toPl Pl x) huP
  let ιD : E →+* RD Pl := IsLocalization.Away.lift (f * t) (g := toRD Pl hx) huRD
  have hιP : ∀ c : Bx x, ιP (algebraMap (Bx x) E c) = toPl Pl x c := fun c => IsLocalization.Away.lift_eq _ huP c
  have hιD : ∀ c : Bx x, ιD (algebraMap (Bx x) E c) = toRD Pl hx c := fun c => IsLocalization.Away.lift_eq _ huRD c

  have hPD : (Pl.subtype.comp ιP : E →+* L) = ((RD Pl).subtype.comp ιD : E →+* L) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (f * t)) ?_
    ext c
    simp only [RingHom.comp_apply, hιP, hιD]
    rfl

  obtain ⟨π, -, hπ⟩ := (ValuationSubring.henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup Pl p hPl).2.1

  have hE' : @Algebra.Etale ℤ E _ _ (Ring.toIntAlgebra E) := by
    convert hE
    exact Subsingleton.elim _ _
  refine ⟨E, inferInstance, hE', Pl.subtype.comp ιP, π.comp ιD, fun e => (ιP e).2, fun e n hn => ?_, ?_⟩
  ·
    have h0 : π (ιD e - n) = 0 := by
      rw [map_sub, map_intCast, show π (ιD e) = (π.comp ιD) e from rfl, ← hn, sub_self]
    have h1 := (hπ _).mp h0
    have h2 : ((ιD e - n : RD Pl) : L) = (Pl.subtype.comp ιP) e - n := by
      rw [hPD]
      simp
    rwa [h2] at h1
  ·
    refine ⟨IsLocalization.mk' E (b * f) (⟨f * t, Submonoid.mem_powers _⟩ : Submonoid.powers (f * t)), ?_⟩
    have hmk := IsLocalization.mk'_spec E (b * f) (⟨f * t, Submonoid.mem_powers _⟩ : Submonoid.powers (f * t))
    have hιL : ∀ c : Bx x, (Pl.subtype.comp ιP) (algebraMap (Bx x) E c) = toL x c := fun c => by
      rw [RingHom.comp_apply, hιP]; rfl

    have key : (Pl.subtype.comp ιP) (IsLocalization.mk' E (b * f) (⟨f * t, Submonoid.mem_powers _⟩ : Submonoid.powers (f * t)))
        * toL x (f * t) = toL x (b * f) := by
      have := congrArg (Pl.subtype.comp ιP) hmk
      rwa [map_mul, hιL, hιL] at this
    have hbt' : x * toL x t = toL x b := by
      have := congrArg (algebraMap (Kx x) L) hbt
      rwa [map_mul] at this
    have hft : toL x (f * t) ≠ 0 := by
      rw [map_ne_zero_iff _ (toL_injective x)]
      intro h0; exact hg (h0 ▸ Ideal.zero_mem _)
    apply mul_right_cancel₀ hft
    rw [key, map_mul, map_mul, ← hbt']
    ring

end Assembly

end HensL1
p2m_reactivate "P2MW.S_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup.HensL1"

theorem solution
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (x : AlgebraicClosure ℚ)
    (hx : x ∈ (Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra.Etale ℤ E) (ι : E →+* AlgebraicClosure ℚ) (φ₀ : E →+* ZMod p),
      (∀ e : E, ι e ∈ Pl) ∧
      (∀ (e : E) (n : ℤ), (n : ZMod p) = φ₀ e → Pl.valuation (ι e - n) < 1) ∧
      x ∈ Set.range ι :=
  HensL1.main p Pl hPl hx

end
p2m_reactivate "P2MW.S_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup.HensL1"

end S_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup
end P2MW
export P2MW.S_ValuationSubring_exists_etale_int_ringHom_apply_eq_of_mem_inf_fixedField_decompositionSubgroup (solution)
