-- Prove2me | solution 1 for ValuationSubring.exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0d3362eb-fa49-59c1-82aa-20877629f94e

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open IsLocalRing
open scoped Pointwise

namespace ValuationSubring
p2m_export "ValuationSubring" "comap coe_mem_nonunits_iff mem_comap smul_mem_pointwise_smul_iff ext nonunits mem_nonunits_iff mk smul_mem_pointwise_smul inv_mem_nonunits_iff mul_mem one_mem mem_pointwise_smul_iff_inv_smul_mem decompositionSubgroup algebra valuation inclusion LiesOverPrime exists_algEquiv_smul_eq_of_liesOverPrime exists_integral_mul_eq_of_liesOverPrime"
namespace PlaceMove
p2m_open "ValuationSubring"

local notation "ℚbar" => AlgebraicClosure ℚ
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "𝓞" => (integralClosure ℤ (AlgebraicClosure ℚ))

theorem liesOverPrime_of_charP (A : ValuationSubring ℚbar) (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField A) p] : A.LiesOverPrime p := by
  have h0 : (residue A) (p : A) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero (ResidueField A) p
  have hmem : (p : A) ∈ maximalIdeal A := by
    rwa [← IsLocalRing.residue_eq_zero_iff]
  have := (ValuationSubring.coe_mem_nonunits_iff (A := A) (a := (p : A))).mpr hmem
  simpa [ValuationSubring.LiesOverPrime] using this

theorem charP_of_ringEquiv {A A' : ValuationSubring ℚbar} (p : ℕ) [CharP (ResidueField A) p]
    (e : ResidueField A' ≃+* ResidueField A) : CharP (ResidueField A') p :=
  charP_of_injective_ringHom (e.symm : ResidueField A →+* ResidueField A').injective p

theorem algebraRat_eq :
    (AlgebraicClosure.instAlgebra ℚ : Algebra ℚ ℚbar) = (inferInstance : Algebra ℚ ℚbar) :=
  Subsingleton.elim _ _

theorem isAlgebraic_rat : Algebra.IsAlgebraic ℚ ℚbar := by
  have h := AlgebraicClosure.isAlgebraic (k := ℚ)
  rwa [algebraRat_eq] at h

attribute [local instance] isAlgebraic_rat

theorem isAlgClosure_rat : IsAlgClosure ℚ ℚbar := ⟨inferInstance, inferInstance⟩

attribute [local instance] isAlgClosure_rat

theorem normal_rat : Normal ℚ ℚbar := IsAlgClosure.normal ℚ ℚbar

attribute [local instance] normal_rat

theorem isGalois_rat : IsGalois ℚ ℚbar := ⟨⟩

attribute [local instance] isGalois_rat

theorem smulCommClass_int : SMulCommClass Γ ℤ ℚbar :=
  ⟨fun g n x => by simp only [zsmul_eq_mul, AlgEquiv.smul_def, map_mul, map_intCast]⟩

attribute [local instance] smulCommClass_int

theorem isInvariant_int : Algebra.IsInvariant ℤ 𝓞 Γ where
  isInvariant := by
    rintro ⟨x, hx⟩ hx'
    have hxint : IsIntegral ℤ x := hx
    obtain ⟨y, rfl⟩ := Algebra.IsInvariant.isInvariant (A := ℚ) (B := ℚbar) (G := Γ) x
      fun g => congrArg Subtype.val (hx' g)
    rw [isIntegral_algebraMap_iff (algebraMap ℚ ℚbar).injective] at hxint
    obtain ⟨n, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hxint
    refine ⟨n, Subtype.ext ?_⟩
    simp

attribute [local instance] isInvariant_int

@[reducible] def topO : TopologicalSpace 𝓞 := ⊥

attribute [local instance] topO

theorem discreteO : DiscreteTopology 𝓞 := ⟨rfl⟩

attribute [local instance] discreteO

theorem isOpen_setOf_smul_eq (x b : 𝓞) : IsOpen {g : Γ | g • x = b} := by
  rw [isOpen_iff_forall_mem_open]
  intro g₀ hg₀
  have hxint : IsIntegral ℚ (x : ℚbar) := Algebra.IsIntegral.isIntegral _
  set E : IntermediateField ℚ ℚbar := IntermediateField.adjoin ℚ {(x : ℚbar)} with hE
  haveI : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hxint
  refine ⟨(fun h => g₀ * h) '' (E.fixingSubgroup : Set Γ), ?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    have hfix : h • x = x := by
      apply Subtype.ext
      rw [integralClosure.coe_smul, AlgEquiv.smul_def]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hh _
        (IntermediateField.mem_adjoin_simple_self ℚ _)
    show (g₀ * h) • x = b
    rw [mul_smul, hfix]
    exact hg₀
  · exact (Homeomorph.mulLeft g₀).isOpenMap _ (IntermediateField.fixingSubgroup_isOpen _)
  · exact ⟨1, Subgroup.one_mem _, mul_one g₀⟩

theorem continuousSMul_O : ContinuousSMul Γ 𝓞 := by
  constructor
  rw [continuous_discrete_rng]
  intro b
  have hset : (fun q : Γ × 𝓞 => q.1 • q.2) ⁻¹' {b} = ⋃ x : 𝓞, {g : Γ | g • x = b} ×ˢ {x} := by
    ext ⟨g, x⟩
    simp
  rw [hset]
  exact isOpen_iUnion fun x => (isOpen_setOf_smul_eq x b).prod (isOpen_discrete _)

attribute [local instance] continuousSMul_O

theorem coe_mem (A : ValuationSubring ℚbar) (b : 𝓞) : (b : ℚbar) ∈ A := by
  obtain ⟨P, hP, hPb⟩ := (b.2 : IsIntegral ℤ (b : ℚbar))
  have hint : IsIntegral A (b : ℚbar) := by
    refine ⟨P.map (Int.castRingHom A), hP.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap A ℚbar).comp (Int.castRingHom A) = algebraMap ℤ ℚbar := by
      ext n; simp
    rw [hcomp]
    exact hPb
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

def incl (A : ValuationSubring ℚbar) : 𝓞 →+* A where
  toFun b := ⟨b, coe_mem A b⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_incl (A : ValuationSubring ℚbar) (b : 𝓞) : ((incl A b : A) : ℚbar) = b := rfl

def center (A : ValuationSubring ℚbar) : Ideal 𝓞 := (maximalIdeal A).comap (incl A)

theorem mem_center_iff {A : ValuationSubring ℚbar} {b : 𝓞} :
    b ∈ center A ↔ (b : ℚbar) ∈ A.nonunits := by
  rw [show b ∈ center A ↔ incl A b ∈ maximalIdeal A from Iff.rfl,
    ← ValuationSubring.coe_mem_nonunits_iff, coe_incl]

scoped instance center_isPrime (A : ValuationSubring ℚbar) : (center A).IsPrime :=
  Ideal.comap_isPrime (incl A) (maximalIdeal A)

theorem center_under {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (center A).under ℤ = Ideal.span {(p : ℤ)} := by
  have hpmem : (p : ℤ) ∈ (center A).under ℤ := by
    rw [Ideal.mem_comap, mem_center_iff]
    simp at hA ⊢
    exact hA
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  exact (hmax.eq_of_le (Ideal.comap_isPrime _ _).1
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpmem))).symm

theorem center_liesOver {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (center A).LiesOver (Ideal.span {(p : ℤ)}) :=
  ⟨(center_under hp hA).symm⟩

theorem center_isMaximal {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (center A).IsMaximal := by
  haveI := center_liesOver hp hA
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  exact Ideal.IsMaximal.of_liesOver_isMaximal (center A) (Ideal.span {(p : ℤ)})

def toRes (A : ValuationSubring ℚbar) : 𝓞 ⧸ center A →+* ResidueField A :=
  Ideal.Quotient.lift (center A) ((residue A).comp (incl A)) fun b hb => by
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact hb

@[scoped simp] theorem toRes_mk (A : ValuationSubring ℚbar) (b : 𝓞) :
    toRes A (Ideal.Quotient.mk _ b) = residue A (incl A b) := rfl

theorem toRes_injective {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Function.Injective (toRes A) := by
  haveI := center_isMaximal hp hA
  letI : Field (𝓞 ⧸ center A) := Ideal.Quotient.field _
  exact (toRes A).injective

theorem toRes_surjective {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) :
    Function.Surjective (toRes A) := by
  haveI := center_isMaximal hp hA
  letI : Field (𝓞 ⧸ center A) := Ideal.Quotient.field _
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨x, s, hs, hax⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime A hp hA (a : ℚbar) a.2

  have haxA : a * incl A s = incl A x := Subtype.ext (by simpa using hax)
  have hsunit : incl A s ∉ maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff, coe_incl]
    exact hs
  have hres_s : residue A (incl A s) ≠ 0 := by
    rwa [Ne, IsLocalRing.residue_eq_zero_iff]
  refine ⟨Ideal.Quotient.mk _ x * (Ideal.Quotient.mk _ s)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, toRes_mk, toRes_mk, ← haxA, map_mul, mul_inv_cancel_right₀ hres_s]

def resEquiv {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) :
    (𝓞 ⧸ center A) ≃+* ResidueField A :=
  RingEquiv.ofBijective (toRes A) ⟨toRes_injective hp hA, toRes_surjective hp hA⟩

@[scoped simp] theorem resEquiv_mk {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (b : 𝓞) : resEquiv hp hA (Ideal.Quotient.mk _ b) = residue A (incl A b) := rfl

theorem inv_mem_of_not_mem_nonunits {A : ValuationSubring ℚbar} {z : ℚbar} (hz : z ∉ A.nonunits) :
    z⁻¹ ∈ A := by
  by_contra h
  have := (A.inv_mem_nonunits_iff (x := z⁻¹)).mpr (Or.inr h)
  rw [inv_inv] at this
  exact hz this

theorem smul_le_of_mem_stabilizer {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) {g : Γ} (hg : g ∈ MulAction.stabilizer Γ (center A)) :
    g • A ≤ A := by
  intro y hy
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hy
  set a : ℚbar := g⁻¹ • y with ha
  have hya : y = g a := by simp [ha, AlgEquiv.smul_def]
  obtain ⟨x, s, hs, hax⟩ := ValuationSubring.exists_integral_mul_eq_of_liesOverPrime A hp hA a hy
  have hs0 : (s : ℚbar) ≠ 0 := by
    intro h0
    apply hs
    rw [h0, ValuationSubring.mem_nonunits_iff, map_zero]
    exact zero_lt_one

  have hsQ : s ∉ center A := fun h => hs (mem_center_iff.mp h)
  have hgsQ : g • s ∉ center A := by
    intro h
    have h' : g • s ∈ g • center A := by rwa [hg]
    exact hsQ (Ideal.smul_mem_pointwise_smul_iff.mp h')
  have hgs : ((g • s : 𝓞) : ℚbar) ∉ A.nonunits := fun h => hgsQ (mem_center_iff.mpr h)
  have hgs_inv : (g (s : ℚbar))⁻¹ ∈ A := by
    have := inv_mem_of_not_mem_nonunits hgs
    rwa [integralClosure.coe_smul, AlgEquiv.smul_def] at this
  have hgx : g (x : ℚbar) ∈ A := by
    have := coe_mem A (g • x)
    rwa [integralClosure.coe_smul, AlgEquiv.smul_def] at this

  have hga : g a = g (x : ℚbar) * (g (s : ℚbar))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (by simpa using hs0), ← map_mul, hax]
  rw [hya, hga]
  exact A.mul_mem _ _ hgx hgs_inv

theorem smul_eq_of_mem_stabilizer {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime)
    (hA : A.LiesOverPrime p) {g : Γ} (hg : g ∈ MulAction.stabilizer Γ (center A)) :
    g • A = A := by
  refine le_antisymm (smul_le_of_mem_stabilizer hp hA hg) ?_
  have hg' : g⁻¹ ∈ MulAction.stabilizer Γ (center A) := inv_mem hg
  have h := smul_le_of_mem_stabilizer hp hA hg'
  calc A = g • g⁻¹ • A := by rw [smul_inv_smul]
    _ ≤ g • A := by
        intro y hy
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hy ⊢
        exact h hy

def toAlgEquiv {A : ValuationSubring ℚbar} {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (f : (𝓞 ⧸ center A) ≃+* (𝓞 ⧸ center A)) :
    letI := center_liesOver hp hA
    (𝓞 ⧸ center A) ≃ₐ[ℤ ⧸ Ideal.span {(p : ℤ)}] (𝓞 ⧸ center A) :=
  letI := center_liesOver hp hA
  AlgEquiv.ofRingEquiv (f := f) fun z => by
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hn : (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}) n) = (n : ℤ ⧸ Ideal.span {(p : ℤ)}) := by
      simp
    rw [hn, map_intCast, map_intCast]

theorem exists_mem_decompositionSubgroup_residue_eq {A : ValuationSubring ℚbar} {p : ℕ}
    (hp : p.Prime) (hA : A.LiesOverPrime p) (ρ : ResidueField A ≃+* ResidueField A) :
    ∃ (d : Γ) (hd : d ∈ A.decompositionSubgroup ℚ),
      ∀ a : A, residue A ((⟨d, hd⟩ : A.decompositionSubgroup ℚ) • a) = ρ (residue A a) := by
  haveI := center_liesOver hp hA
  set Φ := resEquiv hp hA with hΦ

  set σ := toAlgEquiv hp hA (Φ.trans (ρ.trans Φ.symm)) with hσ
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Γ) (Ideal.span {(p : ℤ)}) (center A) σ
  have hgD : (g : Γ) • A = A := smul_eq_of_mem_stabilizer hp hA g.2
  refine ⟨g, hgD, ?_⟩

  have key : ∀ b : 𝓞, residue A ((⟨(g : Γ), hgD⟩ : A.decompositionSubgroup ℚ) • incl A b) =
      ρ (residue A (incl A b)) := by
    intro b
    have h1 : Ideal.Quotient.stabilizerHom (center A) (Ideal.span {(p : ℤ)}) Γ g
        (Ideal.Quotient.mk _ b) = σ (Ideal.Quotient.mk _ b) := by rw [hg]
    rw [Ideal.Quotient.stabilizerHom_apply] at h1

    have h2 : Φ (Ideal.Quotient.mk _ ((g : Γ) • b)) = ρ (Φ (Ideal.Quotient.mk _ b)) := by
      have := congrArg Φ h1
      simp [hσ, toAlgEquiv] at this
      exact this
    rw [hΦ, resEquiv_mk, resEquiv_mk] at h2
    exact (congrArg (residue A) (Subtype.ext rfl)).trans h2

  intro a
  obtain ⟨z, hz⟩ := (resEquiv hp hA).surjective (residue A a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [resEquiv_mk] at hz

  rw [IsLocalRing.ResidueField.residue_smul, ← hz, ← IsLocalRing.ResidueField.residue_smul]
  exact key b

section SMulEq

variable {A A' : ValuationSubring ℚbar} (g : Γ) (hg : g • A' = A)

include hg in
theorem mem_of_mem (x : ℚbar) (hx : x ∈ A') : g x ∈ A := by
  have h := ValuationSubring.smul_mem_pointwise_smul g x A' hx
  rwa [hg, AlgEquiv.smul_def] at h

include hg in
theorem mem_iff (x : ℚbar) : g x ∈ A ↔ x ∈ A' := by
  refine ⟨fun h => ?_, mem_of_mem g hg x⟩
  have h' : g • x ∈ g • A' := by rwa [hg, AlgEquiv.smul_def]
  exact ValuationSubring.smul_mem_pointwise_smul_iff.mp h'

include hg in
theorem symm_mem_of_mem (y : ℚbar) (hy : y ∈ A) : g.symm y ∈ A' := by
  rw [← mem_iff g hg]
  simpa using hy

def ringEquivOfSMulEq : A' ≃+* A where
  toFun x := ⟨g x, mem_of_mem g hg x x.2⟩
  invFun y := ⟨g.symm y, symm_mem_of_mem g hg y y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_ringEquivOfSMulEq_apply (x : A') :
    ((ringEquivOfSMulEq g hg x : A) : ℚbar) = g x := rfl

def resMap : ResidueField A' ≃+* ResidueField A :=
  IsLocalRing.ResidueField.mapEquiv (ringEquivOfSMulEq g hg)

theorem resMap_residue (x : A') :
    resMap g hg (residue A' x) = residue A (ringEquivOfSMulEq g hg x) := rfl

end SMulEq

end ValuationSubring.PlaceMove
p2m_reactivate "P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField.ValuationSubring P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField.ValuationSubring.PlaceMove"
p2m_reactivate "P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField.ValuationSubring"

end
p2m_reactivate "P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField.ValuationSubring P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField.ValuationSubring.PlaceMove"

open ValuationSubring.PlaceMove IsLocalRing in
open scoped Pointwise in
theorem solution (p : ℕ) [Fact p.Prime] (A A' : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField A) p] (e : IsLocalRing.ResidueField A' ≃+* IsLocalRing.ResidueField A) : ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ • A' = A ∧ ∀ (x : A') (y : A), (y : AlgebraicClosure ℚ) = τ (x : AlgebraicClosure ℚ) → IsLocalRing.residue A y = e (IsLocalRing.residue A' x) := by
  have hp : p.Prime := Fact.out
  have hA : A.LiesOverPrime p := liesOverPrime_of_charP A p
  haveI : CharP (ResidueField A') p := charP_of_ringEquiv p e
  have hA' : A'.LiesOverPrime p := liesOverPrime_of_charP A' p

  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp A' A hA' hA

  set ρ : ResidueField A ≃+* ResidueField A := (resMap g hg).symm.trans e with hρ
  obtain ⟨d, hd, hdρ⟩ := exists_mem_decompositionSubgroup_residue_eq hp hA ρ
  refine ⟨d * g, ?_, ?_⟩
  · rw [mul_smul, hg]
    exact hd
  · intro x y hy
    have hyx : y = (⟨d, hd⟩ : A.decompositionSubgroup ℚ) • ringEquivOfSMulEq g hg x := by
      apply Subtype.ext
      rw [hy]
      rfl
    rw [hyx, hdρ, hρ, RingEquiv.coe_trans, Function.comp_apply]
    congr 1
    rw [RingEquiv.symm_apply_eq]
    rfl

end S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField
end P2MW
export P2MW.S_ValuationSubring_exists_algEquiv_smul_eq_and_residue_eq_of_ringEquiv_residueField (solution)
