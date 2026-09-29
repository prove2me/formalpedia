-- Prove2me | solution 1 for ValuationSubring.exists_admissible_smallConstants_stable_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/259dd6c8-58d4-5aa2-9077-063dca50eec9

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_ValuationSubring_isIntegral_and_exists_totallyRamified_layers_of_henselian
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
import Theorems.Thm_ValuationSubring_henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_henselianLocalRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_admissible_smallConstants_stable_of_eq_three

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise

namespace ConstAdm

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem isUnit_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R) :
    IsUnit (e x) ↔ IsUnit x := by
  constructor
  · intro h
    have := h.map e.symm
    simpa using this
  · intro h
    exact h.map e

theorem henselian_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [hR : HenselianLocalRing R]
    (e : R ≃+* S) : HenselianLocalRing S := by
  haveI : Nontrivial S := e.symm.toEquiv.nontrivial
  haveI : IsLocalRing S := IsLocalRing.of_surjective' (e : R →+* S) e.surjective
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  set g : Polynomial R := f.map (e.symm : S →+* R) with hg
  have hgm : g.Monic := hf.map _
  have hev : ∀ x : S, g.eval (e.symm x) = e.symm (f.eval x) := by
    intro x
    rw [hg, Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (e.symm : S →+* R) x
  have hevd : ∀ x : S, g.derivative.eval (e.symm x) = e.symm (f.derivative.eval x) := by
    intro x
    rw [hg, Polynomial.derivative_map, Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (e.symm : S →+* R) x
  have h₁' : g.eval (e.symm a₀) ∈ maximalIdeal R := by
    rw [hev, mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_of_ringEquiv e.symm]
    exact h₁
  have h₂' : IsUnit (g.derivative.eval (e.symm a₀)) := by
    rw [hevd, isUnit_iff_of_ringEquiv e.symm]
    exact h₂
  obtain ⟨a, ha, hamem⟩ := HenselianLocalRing.is_henselian g hgm (e.symm a₀) h₁' h₂'
  refine ⟨e a, ?_, ?_⟩
  · have : e.symm (f.eval (e a)) = 0 := by
      rw [← hev, e.symm_apply_apply]
      exact ha
    simpa using congrArg e this
  · have hm : e.symm (e a - a₀) ∈ maximalIdeal R := by
      simpa using hamem
    rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_of_ringEquiv e.symm] at hm
    exact hm

theorem irreducible_of_factorization {R : Type*} [CommRing R] [IsDomain R] (ϖ : R)
    (hϖu : ¬ IsUnit ϖ) (hϖ0 : ϖ ≠ 0)
    (hfact : ∀ a : R, a ≠ 0 → ∃ (m : ℕ) (w : R), IsUnit w ∧ a = ϖ ^ m * w) :
    Irreducible ϖ := by
  refine ⟨hϖu, fun a b hab => ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl; exact hϖ0 (by simpa using hab)
  have hb0 : b ≠ 0 := by
    rintro rfl; exact hϖ0 (by simpa using hab)
  obtain ⟨i, wa, hwa, rfl⟩ := hfact a ha0
  obtain ⟨j, wb, hwb, rfl⟩ := hfact b hb0
  rcases Nat.eq_zero_or_pos i with hi | hi
  · left; simpa [hi] using hwa
  rcases Nat.eq_zero_or_pos j with hj | hj
  · right; simpa [hj] using hwb
  exfalso
  apply hϖu
  have key : ϖ * 1 = ϖ * (ϖ ^ (i + j - 1) * (wa * wb)) := by
    have hij : i + j - 1 + 1 = i + j := by omega
    calc ϖ * 1 = ϖ := mul_one ϖ
      _ = ϖ ^ i * wa * (ϖ ^ j * wb) := hab
      _ = ϖ ^ (i + j) * (wa * wb) := by ring
      _ = ϖ ^ (i + j - 1 + 1) * (wa * wb) := by rw [hij]
      _ = ϖ * (ϖ ^ (i + j - 1) * (wa * wb)) := by ring
  have h1 : (1 : R) = ϖ ^ (i + j - 1) * (wa * wb) := mul_left_cancel₀ hϖ0 key
  have hdvd : ϖ ∣ (1 : R) := by
    rw [h1]
    exact Dvd.dvd.mul_right (dvd_pow_self ϖ (by omega)) _
  exact isUnit_of_dvd_one hdvd

theorem dvr_of_factorization {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] (ϖ : R)
    (hϖu : ¬ IsUnit ϖ) (hϖ0 : ϖ ≠ 0)
    (hfact : ∀ a : R, a ≠ 0 → ∃ (m : ℕ) (w : R), IsUnit w ∧ a = ϖ ^ m * w) :
    IsDiscreteValuationRing R ∧ maximalIdeal R = Ideal.span {ϖ} := by
  have hirr : Irreducible ϖ := irreducible_of_factorization ϖ hϖu hϖ0 hfact
  have hR : IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization R := by
    refine ⟨ϖ, hirr, ?_⟩
    intro x hx
    obtain ⟨m, w, hw, rfl⟩ := hfact x hx
    exact ⟨m, hw.unit, by simp⟩
  haveI hdvr : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization hR
  exact ⟨hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr⟩

theorem apply_mem_fixedField_inertia (A : ValuationSubring ℚ̄) (τ : ℚ̄ ≃ₐ[ℚ] ℚ̄)
    (hτ : ∀ x : ℚ̄, x ∈ A ↔ τ x ∈ A) (x : ℚ̄)
    (hx : x ∈ IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) :
    τ x ∈ IntermediateField.fixedField (A.inertiaSubgroupIn ℚ) := by
  have hτA : τ • A = A := by
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hτ (τ⁻¹ y)]
    simp
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  have hσ' : σ ∈ (τ • A).inertiaSubgroupIn ℚ := by rwa [hτA]
  have hc := ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul A τ hσ'
  have h1 := hx _ hc
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at h1
  have h2 := congrArg τ h1
  simpa using h2

theorem fixingSubgroup_le_inertiaSubgroupIn (q : ℕ) [Fact q.Prime] (A : ValuationSubring ℚ̄)
    (hA : A.LiesOverPrime q) (k₀ : IntermediateField ℚ ℚ̄)
    (hT : IntermediateField.fixedField (A.inertiaSubgroupIn ℚ) ≤ k₀) :
    k₀.fixingSubgroup ≤ A.inertiaSubgroupIn ℚ := by
  intro σ hσ
  obtain ⟨O, -, -, -, -, -, hiff, -⟩ :=
    ValuationSubring.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq q A hA
  refine (hiff σ).mpr ?_
  intro x hxO
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  apply hσ
  apply hT
  rw [IntermediateField.mem_fixedField_iff]
  intro f hf
  exact (hiff f).mp hf x hxO

theorem henselian_comap (A : ValuationSubring ℚ̄) (k₀ : IntermediateField ℚ ℚ̄)
    (hI : k₀.fixingSubgroup ≤ A.inertiaSubgroupIn ℚ) :
    HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ ℚ̄)) := by
  have h36 := ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn A k₀.fixingSubgroup hI
  rw [InfiniteGalois.fixedField_fixingSubgroup] at h36
  let e : ↥(A.toSubring ⊓ k₀.toSubring) ≃+* ↥(A.comap (algebraMap ↥k₀ ℚ̄)) :=
    { toFun := fun x => ⟨⟨(x : ℚ̄), (Subring.mem_inf.mp x.2).2⟩, (Subring.mem_inf.mp x.2).1⟩
      invFun := fun y => ⟨((y : ↥k₀) : ℚ̄), Subring.mem_inf.mpr ⟨y.2, (y : ↥k₀).2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact henselian_of_ringEquiv e

def incl (A : ValuationSubring ℚ̄) (k₀ : IntermediateField ℚ ℚ̄) :
    ↥(A.comap (algebraMap ↥k₀ ℚ̄)) →+* ↥A :=
  { toFun := fun x => ⟨((x : ↥k₀) : ℚ̄), x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

@[scoped simp] theorem coe_incl (A : ValuationSubring ℚ̄) (k₀ : IntermediateField ℚ ℚ̄)
    (x : ↥(A.comap (algebraMap ↥k₀ ℚ̄))) : ((incl A k₀ x : ↥A) : ℚ̄) = ((x : ↥k₀) : ℚ̄) := rfl

scoped instance isLocalHom_incl (A : ValuationSubring ℚ̄) (k₀ : IntermediateField ℚ ℚ̄) :
    IsLocalHom (incl A k₀) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hx
  have hb' : (((x : ↥k₀) : ℚ̄)) * (b : ℚ̄) = 1 := by
    have := congrArg (fun t : ↥A => (t : ℚ̄)) hb
    simpa using this
  have hx0 : ((x : ↥k₀) : ℚ̄) ≠ 0 := by
    intro h; rw [h, zero_mul] at hb'; exact zero_ne_one hb'
  have hbeq : (b : ℚ̄) = ((x : ↥k₀) : ℚ̄)⁻¹ := eq_inv_of_mul_eq_one_right hb'
  have hbk : (b : ℚ̄) ∈ k₀ := by
    rw [hbeq]; exact inv_mem (x : ↥k₀).2
  refine isUnit_iff_exists_inv.mpr ⟨⟨⟨(b : ℚ̄), hbk⟩, b.2⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  exact hb'

theorem exists_sub_mem_maximalIdeal (q : ℕ) [Fact q.Prime] (A : ValuationSubring ℚ̄)
    (hA : A.LiesOverPrime q) (k₀ : IntermediateField ℚ ℚ̄)
    (hT : IntermediateField.fixedField (A.inertiaSubgroupIn ℚ) ≤ k₀) (a : ↥A) :
    ∃ c : ↥(A.comap (algebraMap ↥k₀ ℚ̄)), a - incl A k₀ c ∈ maximalIdeal ↥A := by
  obtain ⟨c, hc, hfix⟩ :=
    ValuationSubring.exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime A
      (Fact.out : q.Prime) hA (residue ↥A a)
  have hck : (c : ℚ̄) ∈ k₀ := by
    apply hT
    rw [IntermediateField.mem_fixedField_iff]
    exact hfix
  refine ⟨⟨⟨(c : ℚ̄), hck⟩, c.2⟩, ?_⟩
  have : incl A k₀ ⟨⟨(c : ℚ̄), hck⟩, c.2⟩ = c := Subtype.ext rfl
  rw [this, ← residue_eq_zero_iff, map_sub, sub_eq_zero]
  exact hc.symm

theorem isAlgClosed_residueField_comap (q : ℕ) [Fact q.Prime] (A : ValuationSubring ℚ̄)
    (hA : A.LiesOverPrime q) (k₀ : IntermediateField ℚ ℚ̄)
    (hT : IntermediateField.fixedField (A.inertiaSubgroupIn ℚ) ≤ k₀) :
    IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ ℚ̄))) := by
  let φ := ResidueField.map (incl A k₀)
  have hinj : Function.Injective φ := φ.injective
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := residue_surjective y
    obtain ⟨c, hc⟩ := exists_sub_mem_maximalIdeal q A hA k₀ hT a
    refine ⟨residue _ c, ?_⟩
    rw [ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hc
  let e := RingEquiv.ofBijective φ ⟨hinj, hsurj⟩
  haveI := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  exact IsAlgClosed.of_ringEquiv (ResidueField ↥A) _ e.symm

theorem apply_mem_adjoin_of_forall_mem {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E →ₐ[F] E) (U : Set E)
    (hU : ∀ y ∈ U, f y ∈ IntermediateField.adjoin F U) (x : E)
    (hx : x ∈ IntermediateField.adjoin F U) : f x ∈ IntermediateField.adjoin F U := by
  have hx' : f x ∈ (IntermediateField.adjoin F U).map f := by
    rw [IntermediateField.mem_map]; exact ⟨x, hx, rfl⟩
  rw [IntermediateField.adjoin_map] at hx'
  refine (IntermediateField.adjoin_le_iff.mpr ?_) hx'
  rintro _ ⟨y, hy, rfl⟩
  exact hU y hy

end ConstAdm
p2m_reactivate "P2MW.S_ValuationSubring_exists_admissible_smallConstants_stable_of_eq_three.ConstAdm"

open ValuationSubring ConstAdm in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A),
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))} ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      (∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧

      (∀ τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), (∀ x : (AlgebraicClosure ℚ), x ∈ A ↔ τ x ∈ A) →
        ∀ x : (AlgebraicClosure ℚ), x ∈ k₀ → τ x ∈ k₀) ∧
      ∃ (ℓ : ℕ), ℓ.Prime ∧ 3 ≤ ℓ ∧ ℓ ≠ q ∧ ¬ ℓ ∣ M' ∧
      ∃ (ζ₀ : ↥k₀), IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ) ∧
      ∃ (ϖt : ↥k₀), (ϖt : AlgebraicClosure ℚ) ∈ A ∧
        ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ) := by
  classical
  have hqp : q.Prime := Fact.out

  obtain ⟨ℓ, hℓge, hℓp⟩ := Nat.exists_infinite_primes (max q M' + 3)
  have hℓ3 : 3 ≤ ℓ := by omega
  have hℓq : ℓ ≠ q := by
    have : q < ℓ := by omega
    omega
  have hℓM' : ¬ ℓ ∣ M' := by
    intro h
    have hM0 : 0 < M' := Nat.pos_of_ne_zero (NeZero.ne M')
    have := Nat.le_of_dvd hM0 h
    omega

  haveI hqℓ0 : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero hqp.ne_zero hℓp.ne_zero⟩
  haveI : NeZero ((q * ℓ : ℕ) : AlgebraicClosure ℚ) := ⟨by exact_mod_cast (Nat.mul_ne_zero hqp.ne_zero hℓp.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (q * ℓ)
  have hN : 0 < q ^ 2 - 1 := by
    have : 2 ≤ q := hqp.two_le
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  haveI hN0 : NeZero (q ^ 2 - 1) := ⟨hN.ne'⟩
  haveI : NeZero ((q ^ 2 - 1 : ℕ) : AlgebraicClosure ℚ) := ⟨by exact_mod_cast hN.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (q ^ 2 - 1)
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq (q : AlgebraicClosure ℚ) hN
  have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := by
    exact_mod_cast (natCast_mem A q)
  have hq0' : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, zero_pow hN.ne'] at hϖ
    exact hq0' hϖ.symm
  have hϖA : ϖ ∈ A := by
    by_contra hnot
    have hlt : 1 < A.valuation ϖ := by
      rw [← not_le, A.valuation_le_one_iff]; exact hnot
    have hle : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hqA
    rw [← hϖ, map_pow] at hle
    exact absurd hle (not_le.mpr (one_lt_pow₀ hlt hN.ne'))
  have hvq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA

  obtain ⟨hdvrT, hirrT, -, -⟩ :=
    ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A q hA
  have hhensT := ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn (K := ℚ) A
  have hresT := ValuationSubring.isAlgClosed_residueField_comap_fixedField_inertiaSubgroupIn A q hA ℚ
  let T : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)

  let S : Set (AlgebraicClosure ℚ) := {ζ, ξ, ϖ}
  let L : IntermediateField ↥T (AlgebraicClosure ℚ) := IntermediateField.adjoin ↥T S
  let k₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := L.restrictScalars ℚ
  let U : Set (AlgebraicClosure ℚ) := (T : Set (AlgebraicClosure ℚ)) ∪ S
  have hk₀ : k₀ = IntermediateField.adjoin ℚ U := IntermediateField.restrictScalars_adjoin ℚ T S
  have hTU : (T : Set (AlgebraicClosure ℚ)) ⊆ U := Set.subset_union_left
  have hSU : S ⊆ U := Set.subset_union_right
  have hUk : U ⊆ (IntermediateField.adjoin ℚ U : Set (AlgebraicClosure ℚ)) :=
    IntermediateField.subset_adjoin ℚ U
  have hTk : T ≤ k₀ := by
    rw [hk₀]; exact fun x hx => hUk (hTU hx)
  have hSk : S ⊆ k₀ := by
    rw [hk₀]; exact fun x hx => hUk (hSU hx)
  have hζS : ζ ∈ S := by simp [S]
  have hξS : ξ ∈ S := by simp [S]
  have hϖS : ϖ ∈ S := by simp [S]
  have hζL : ζ ∈ L := IntermediateField.subset_adjoin ↥T S hζS
  have hξL : ξ ∈ L := IntermediateField.subset_adjoin ↥T S hξS
  have hϖL : ϖ ∈ L := IntermediateField.subset_adjoin ↥T S hϖS
  haveI : Algebra.IsAlgebraic ↥T ↥L := by
    haveI := AlgebraicClosure.isAlgebraic ℚ; infer_instance

  let AL : ValuationSubring ↥L := A.comap (algebraMap ↥L (AlgebraicClosure ℚ))
  have hcm : AL.comap (algebraMap ↥T ↥L) = A.comap (algebraMap ↥T (AlgebraicClosure ℚ)) := by
    ext x; rfl
  have hBR := ValuationSubring.isIntegral_and_exists_totallyRamified_layers_of_henselian
    ↥T (AlgebraicClosure ℚ) L AL
  rw [hcm] at hBR
  have hqT : ((q : ℕ) : ↥T) ∈ A.comap (algebraMap ↥T (AlgebraicClosure ℚ)) := by
    rw [ValuationSubring.mem_comap, map_natCast]; exact hqA
  have hq' : ((q : ℕ) : ↥(A.comap (algebraMap ↥T (AlgebraicClosure ℚ)))) = ⟨(q : ↥T), hqT⟩ :=
    Subtype.ext (by simp)
  haveI := hdvrT
  have hunifT := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirrT
  rw [hq'] at hunifT
  obtain ⟨-, htower⟩ := hBR (q : ↥T) hqT hdvrT hunifT hhensT hresT
  obtain ⟨n, ϖ', u, v, hn, hϖ'A, huv, hgen, -, hpow, hfact⟩ :=
    htower {⟨ζ, hζL⟩, ⟨ξ, hξL⟩, ⟨ϖ, hϖL⟩}
  have hLle : L ≤ IntermediateField.adjoin ↥T {((ϖ' : ↥L) : AlgebraicClosure ℚ)} := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact hgen ⟨ζ, hζL⟩ (by simp)
    · rw [h]; exact hgen ⟨ξ, hξL⟩ (by simp)
    · rw [h]; exact hgen ⟨ϖ, hϖL⟩ (by simp)

  have hϖ'k : ((ϖ' : ↥L) : AlgebraicClosure ℚ) ∈ k₀ := (ϖ' : ↥L).2
  let ϖR : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := ⟨⟨((ϖ' : ↥L) : AlgebraicClosure ℚ), hϖ'k⟩, hϖ'A⟩
  have hu0 : (u : ↥L) ≠ 0 := by
    intro hu; rw [hu, zero_mul] at huv; exact zero_ne_one huv
  have hqL : algebraMap ↥T ↥L (q : ↥T) = ((q : ℕ) : ↥L) := map_natCast _ q
  have hqL0 : ((q : ℕ) : ↥L) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hϖ'0 : ((ϖ' : ↥L) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have h' : ϖ' = 0 := by exact_mod_cast h
    rw [h', zero_pow hn.ne', hqL] at hpow
    exact (mul_ne_zero hqL0 hu0) hpow.symm
  have hϖR0 : ϖR ≠ 0 := by
    intro h
    apply hϖ'0
    have h2 : ((ϖR : ↥k₀) : AlgebraicClosure ℚ) =
        (((0 : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) : AlgebraicClosure ℚ) := by rw [h]
    exact h2.trans (by simp)

  have hfactR : ∀ a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), a ≠ 0 →
      ∃ (m : ℕ) (w : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))), IsUnit w ∧ a = ϖR ^ m * w := by
    intro a ha
    let aL : ↥L := ⟨((a : ↥k₀) : AlgebraicClosure ℚ), (a : ↥k₀).2⟩
    have haL : aL ∈ AL := a.2
    have haL0 : aL ≠ 0 := by
      intro h
      apply ha
      have h2 : (aL : AlgebraicClosure ℚ) = ((0 : ↥L) : AlgebraicClosure ℚ) := by rw [h]
      apply Subtype.ext; apply Subtype.ext
      exact h2.trans (by simp)
    obtain ⟨m, w, z, hwz, haw⟩ := hfact aL haL (hLle aL.2) haL0
    let wR : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) :=
      ⟨⟨(((w : ↥AL) : ↥L) : AlgebraicClosure ℚ), ((w : ↥AL) : ↥L).2⟩, w.2⟩
    let zR : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) :=
      ⟨⟨(((z : ↥AL) : ↥L) : AlgebraicClosure ℚ), ((z : ↥AL) : ↥L).2⟩, z.2⟩
    have hwz' : wR * zR = 1 := by
      apply Subtype.ext; apply Subtype.ext
      have := congrArg (fun t : ↥L => (t : AlgebraicClosure ℚ)) hwz
      simpa using this
    refine ⟨m, wR, IsUnit.of_mul_eq_one zR hwz', ?_⟩
    apply Subtype.ext; apply Subtype.ext
    have := congrArg (fun t : ↥L => (t : AlgebraicClosure ℚ)) haw
    simpa using this

  have hqunitA : ¬ IsUnit (⟨((q : ℕ) : AlgebraicClosure ℚ), hqA⟩ : ↥A) := by
    intro h
    rw [ValuationSubring.valuation_eq_one_iff] at h
    exact absurd hvq (by rw [h]; exact lt_irrefl 1)
  have hpowR : ϖR ^ n = ⟨⟨((q : ℕ) : AlgebraicClosure ℚ), hTk (natCast_mem T q)⟩, hqA⟩ *
      ⟨⟨(((u : ↥AL) : ↥L) : AlgebraicClosure ℚ), ((u : ↥AL) : ↥L).2⟩, u.2⟩ := by
    apply Subtype.ext; apply Subtype.ext
    have := congrArg (fun t : ↥L => (t : AlgebraicClosure ℚ)) hpow
    rw [hqL] at this
    simpa using this
  have hϖRu : ¬ IsUnit ϖR := by
    intro hunit
    have h1 : IsUnit (ϖR ^ n) := hunit.pow n
    rw [hpowR] at h1
    have h2 := (isUnit_of_mul_isUnit_left h1).map (incl A k₀)
    exact hqunitA h2
  obtain ⟨hdvr, hunif⟩ := dvr_of_factorization ϖR hϖRu hϖR0 hfactR

  have hI := fixingSubgroup_le_inertiaSubgroupIn q A hA k₀ hTk
  have hhens := henselian_comap A k₀ hI
  have hres := isAlgClosed_residueField_comap q A hA k₀ hTk
  have hlift : ∀ a : AlgebraicClosure ℚ, a ∈ A → ∃ c : ↥k₀, (c : AlgebraicClosure ℚ) ∈ A ∧
      ∃ h : a - c ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A := by
    intro a ha
    obtain ⟨c, hc⟩ := exists_sub_mem_maximalIdeal q A hA k₀ hTk ⟨a, ha⟩
    refine ⟨(c : ↥k₀), c.2, sub_mem ha c.2, ?_⟩
    convert hc using 1
    rfl

  have hstab : ∀ τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, x ∈ A ↔ τ x ∈ A) → ∀ x : AlgebraicClosure ℚ, x ∈ k₀ → τ x ∈ k₀ := by
    intro τ hτ x hx
    rw [hk₀] at hx ⊢
    refine apply_mem_adjoin_of_forall_mem (τ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) U ?_ x hx
    intro y hy
    change τ y ∈ IntermediateField.adjoin ℚ U
    rcases hy with hyT | hyS
    · exact hUk (hTU (apply_mem_fixedField_inertia A τ hτ y hyT))
    · have hyS' : y = ζ ∨ y = ξ ∨ y = ϖ := by simpa [S] using hyS
      rcases hyS' with h | h | h
      · rw [h]
        obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ)
          (by rw [← map_pow, hζ.pow_eq_one, map_one])
        rw [← hi]
        exact pow_mem (hUk (hSU hζS)) i
      · rw [h]
        obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one (ξ := τ ξ)
          (by rw [← map_pow, hξ.pow_eq_one, map_one])
        rw [← hi]
        exact pow_mem (hUk (hSU hξS)) i
      · rw [h]
        have h1 : (τ ϖ * ϖ⁻¹) ^ (q ^ 2 - 1) = 1 := by
          rw [mul_pow, ← map_pow, hϖ, map_natCast, inv_pow, hϖ, mul_inv_cancel₀ hq0']
        obtain ⟨j, -, hj⟩ := hξ.eq_pow_of_pow_eq_one h1
        have h2 : τ ϖ = ξ ^ j * ϖ := by
          rw [hj, inv_mul_cancel_right₀ hϖ0]
        rw [h2]
        exact mul_mem (pow_mem (hUk (hSU hξS)) j) (hUk (hSU hϖS))

  exact ⟨k₀, ⟨((ϖ' : ↥L) : AlgebraicClosure ℚ), hϖ'k⟩, hϖ'A, hdvr, hunif, hhens, hres, hlift, hstab,
    ℓ, hℓp, hℓ3, hℓq, hℓM', ⟨ζ, hSk hζS⟩, hζ, ⟨ϖ, hSk hϖS⟩, hϖA, 1, isUnit_one, by simp [hϖ]⟩

end S_ValuationSubring_exists_admissible_smallConstants_stable_of_eq_three
end P2MW
export P2MW.S_ValuationSubring_exists_admissible_smallConstants_stable_of_eq_three (solution)
