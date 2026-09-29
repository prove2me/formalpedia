-- Prove2me | solution 1 for ValuationSubring.exists_eq_tameCharacter_pow_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/11d9f739-f8cd-5dba-b531-3799b8fb0cf6

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter
import Theorems.Thm_ValuationSubring_tameCharacter_mul_of_mem_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_tameCharacter_pow_left
import Theorems.Thm_ValuationSubring_exists_tame_generator_inertiaSubgroupIn
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_eq_tameCharacter_pow_of_pow_eq_one
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete GaloisRep.DeformationRingData.instIsLocalHom GaloisRep.DeformationRingData.instCommRing GaloisRep.DeformationRingData.instIsLocalRing GaloisRep.DeformationRingData.instIsNoetherianRing GaloisRep.DeformationRingData.instIsAdicComplete GaloisRep.DeformationRingData.instAlgebra GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ExtCitation.LocalLevel.coe_smul_OO GaloisRep.DeformationRingData.mk.injEq GaloisRep.DeformationRingData.mk.sizeOf_spec GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

namespace TameClassW3

open ValuationSubring

variable (P : ValuationSubring (AlgebraicClosure ℚ))

private theorem tameCharacter_of_mem (π : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (h : σ π / π ∈ P) :
    P.tameCharacter π σ = IsLocalRing.residue P ⟨σ π / π, h⟩ := by
  unfold ValuationSubring.tameCharacter
  exact dif_pos h

private theorem tameCharacter_natCast (n : ℕ) (hn : (n : AlgebraicClosure ℚ) ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter (n : AlgebraicClosure ℚ) σ = 1 := by
  have h1 : σ (n : AlgebraicClosure ℚ) / (n : AlgebraicClosure ℚ) = 1 := by
    rw [map_natCast, div_self hn]
  have hmem : σ (n : AlgebraicClosure ℚ) / (n : AlgebraicClosure ℚ) ∈ P := by
    rw [h1]; exact P.one_mem
  rw [tameCharacter_of_mem P _ σ hmem]
  have : (⟨σ (n : AlgebraicClosure ℚ) / (n : AlgebraicClosure ℚ), hmem⟩ : P) = 1 := Subtype.ext h1
  rw [this, map_one]

private theorem tameCharacter_pow_eq_one {π : AlgebraicClosure ℚ} {m p : ℕ}
    (hp0 : (p : AlgebraicClosure ℚ) ≠ 0) (hπ : π ^ m = p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter π σ ^ m = 1 := by
  rw [← ValuationSubring.tameCharacter_pow_left P π σ m, hπ]
  exact tameCharacter_natCast P p hp0 σ

section Multiplicative

variable {k : Type*} [Field k]

private theorem map_one_of_mul (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k)
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, f (σ * τ) = f σ * f τ)
    {n : ℕ} (hn : n ≠ 0) (hfn : ∀ σ ∈ P.inertiaSubgroupIn ℚ, f σ ^ n = 1) : f 1 = 1 := by
  have h1 : (1 : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ P.inertiaSubgroupIn ℚ :=
    Subgroup.one_mem _
  have hne : f 1 ≠ 0 := by
    intro h0
    have := hfn 1 h1
    rw [h0, zero_pow hn] at this
    exact zero_ne_one this
  have hsq : f 1 * f 1 = f 1 * 1 := by rw [mul_one, ← hf 1 h1 1 h1, mul_one]
  exact mul_left_cancel₀ hne hsq

private theorem map_pow_of_mul (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k)
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, f (σ * τ) = f σ * f τ)
    {n : ℕ} (hn : n ≠ 0) (hfn : ∀ σ ∈ P.inertiaSubgroupIn ℚ, f σ ^ n = 1)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (i : ℕ) :
    f (σ ^ i) = f σ ^ i := by
  induction i with
  | zero => rw [pow_zero, pow_zero]; exact map_one_of_mul P f hf hn hfn
  | succ i ih => rw [pow_succ, hf _ (Subgroup.pow_mem _ hσ i) σ hσ, ih, pow_succ]

private theorem map_decomp (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k)
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, f (σ * τ) = f σ * f τ)
    {n : ℕ} (hn : n ≠ 0) (hfn : ∀ σ ∈ P.inertiaSubgroupIn ℚ, f σ ^ n = 1)
    {γ x w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hγ : γ ∈ P.inertiaSubgroupIn ℚ)
    (hx : x ∈ P.inertiaSubgroupIn ℚ) (hw : w ∈ P.inertiaSubgroupIn ℚ) (j N : ℕ) :
    f (γ ^ j * x ^ N * w ^ N) = f γ ^ j * f x ^ N * f w ^ N := by
  rw [hf _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hγ j) (Subgroup.pow_mem _ hx N)) _
      (Subgroup.pow_mem _ hw N),
    hf _ (Subgroup.pow_mem _ hγ j) _ (Subgroup.pow_mem _ hx N),
    map_pow_of_mul P f hf hn hfn hγ, map_pow_of_mul P f hf hn hfn hx,
    map_pow_of_mul P f hf hn hfn hw]

end Multiplicative

private theorem eq_one_of_apply_generator {p : ℕ} (hp : p.Prime) (hP : P.LiesOverPrime p)
    {m : ℕ} (hpm : ¬ p ∣ m) {π : AlgebraicClosure ℚ} (hπ : π ^ m = p)
    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P)
    (hf : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, f (σ * τ) = f σ * f τ)
    (hfm : ∀ σ ∈ P.inertiaSubgroupIn ℚ, f σ ^ m = 1)
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ₀ : σ₀ ∈ P.inertiaSubgroupIn ℚ)
    (hω : IsPrimitiveRoot (P.tameCharacter π σ₀) m) (hf0 : f σ₀ = 1)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    f τ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero

  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hπ
    exact hp0 hπ.symm
  set t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P :=
    fun σ => P.tameCharacter π σ with ht_def
  have ht : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, t (σ * τ) = t σ * t τ :=
    fun σ hσ τ _ => ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn P π hπ0 hσ τ
  have htm : ∀ σ ∈ P.inertiaSubgroupIn ℚ, t σ ^ m = 1 :=
    fun σ _ => tameCharacter_pow_eq_one P hp0 hπ σ

  by_contra hne
  have hfin : orderOf (f τ) ∣ m := orderOf_dvd_of_pow_eq_one (hfm τ hτ)
  have hd1 : orderOf (f τ) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  set ℓ := (orderOf (f τ)).minFac with hℓ_def
  have hℓ : ℓ.Prime := Nat.minFac_prime hd1
  have hℓm : ℓ ∣ m := (Nat.minFac_dvd _).trans hfin
  have hℓp : ℓ ≠ p := fun h => hpm (h ▸ hℓm)

  set e := m.factorization ℓ with he_def
  set M := m / ℓ ^ e with hM_def
  have hmeq : ℓ ^ e * M = m := Nat.ordProj_mul_ordCompl_eq_self m ℓ
  have hℓM : ¬ ℓ ∣ M := Nat.not_dvd_ordCompl hℓ hm0
  have he0 : 0 < e := hℓ.factorization_pos_of_dvd hm0 hℓm

  obtain ⟨γ, hγ, hgen⟩ :=
    ValuationSubring.exists_tame_generator_inertiaSubgroupIn hℓ hp hℓp P hP e

  set fM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P :=
    fun σ => f σ ^ M with hfM_def
  set tM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P :=
    fun σ => t σ ^ M with htM_def
  have hfM : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      fM (σ * τ) = fM σ * fM τ := fun σ hσ τ hτ => by
    simp only [hfM_def, hf σ hσ τ hτ, mul_pow]
  have htM : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      tM (σ * τ) = tM σ * tM τ := fun σ hσ τ hτ => by
    simp only [htM_def, ht σ hσ τ hτ, mul_pow]
  have hℓe0 : ℓ ^ e ≠ 0 := pow_ne_zero e hℓ.ne_zero
  have hfMe : ∀ σ ∈ P.inertiaSubgroupIn ℚ, fM σ ^ (ℓ ^ e) = 1 := fun σ hσ => by
    simp only [hfM_def, ← pow_mul, mul_comm M, hmeq, hfm σ hσ]
  have htMe : ∀ σ ∈ P.inertiaSubgroupIn ℚ, tM σ ^ (ℓ ^ e) = 1 := fun σ hσ => by
    simp only [htM_def, ← pow_mul, mul_comm M, hmeq, htm σ hσ]

  have hωM : IsPrimitiveRoot (tM σ₀) (ℓ ^ e) := by
    simp only [htM_def, ht_def]
    exact hω.pow (Nat.pos_of_ne_zero hm0) (by rw [mul_comm]; exact hmeq.symm)

  obtain ⟨j₀, x₀, w₀, hx₀, hw₀, hσ₀eq⟩ := hgen σ₀ hσ₀
  have htσ₀ : tM σ₀ = tM γ ^ j₀ := by
    have h1 : tM σ₀ = tM γ ^ j₀ * tM x₀ ^ (ℓ ^ e) * tM w₀ ^ (ℓ ^ e) := by
      rw [hσ₀eq]; exact map_decomp P tM htM hℓe0 htMe hγ hx₀ hw₀ j₀ (ℓ ^ e)
    rw [h1, htMe x₀ hx₀, htMe w₀ hw₀, mul_one, mul_one]
  have hℓj₀ : ¬ ℓ ∣ j₀ := by
    rintro ⟨c, rfl⟩

    have h1 : tM σ₀ ^ (ℓ ^ (e - 1)) = 1 := by
      rw [htσ₀, ← pow_mul, show ℓ * c * ℓ ^ (e - 1) = ℓ ^ e * c by
        rw [mul_comm ℓ c, mul_assoc, ← pow_succ', Nat.sub_add_cancel he0, mul_comm],
        pow_mul, htMe γ hγ, one_pow]
    have h2 : ℓ ^ e ∣ ℓ ^ (e - 1) := (hωM.pow_eq_one_iff_dvd _).mp h1
    have h3 : ℓ ^ e ≤ ℓ ^ (e - 1) := Nat.le_of_dvd (pow_pos hℓ.pos _) h2
    have h4 : ℓ ^ (e - 1) < ℓ ^ e := Nat.pow_lt_pow_right hℓ.one_lt (Nat.sub_lt he0 Nat.one_pos)
    omega

  have hfσ₀ : fM γ ^ j₀ = 1 := by
    have h1 : fM σ₀ = fM γ ^ j₀ := by
      have h2 : fM σ₀ = fM γ ^ j₀ * fM x₀ ^ (ℓ ^ e) * fM w₀ ^ (ℓ ^ e) := by
        rw [hσ₀eq]; exact map_decomp P fM hfM hℓe0 hfMe hγ hx₀ hw₀ j₀ (ℓ ^ e)
      rw [h2, hfMe x₀ hx₀, hfMe w₀ hw₀, mul_one, mul_one]
    rw [← h1]
    simp only [hfM_def, hf0, one_pow]
  have hcop : Nat.Coprime j₀ (ℓ ^ e) :=
    Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓj₀).symm
  have hfγ : fM γ = 1 := by
    have h := (pow_gcd_eq_one.mpr ⟨hfσ₀, hfMe γ hγ⟩ : fM γ ^ (j₀.gcd (ℓ ^ e)) = 1)
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at h

  have hfτ : fM τ = 1 := by
    obtain ⟨j₁, x₁, w₁, hx₁, hw₁, hτeq⟩ := hgen τ hτ
    have h1 : fM (γ ^ j₁ * x₁ ^ (ℓ ^ e) * w₁ ^ (ℓ ^ e)) = 1 := by
      have h2 : fM (γ ^ j₁ * x₁ ^ (ℓ ^ e) * w₁ ^ (ℓ ^ e))
          = fM γ ^ j₁ * fM x₁ ^ (ℓ ^ e) * fM w₁ ^ (ℓ ^ e) :=
        map_decomp P fM hfM hℓe0 hfMe hγ hx₁ hw₁ j₁ (ℓ ^ e)
      rw [h2, hfMe x₁ hx₁, hfMe w₁ hw₁, mul_one, mul_one, hfγ, one_pow]
    have h2 : fM τ = fM (γ ^ j₁ * x₁ ^ (ℓ ^ e) * w₁ ^ (ℓ ^ e)) := congrArg fM hτeq
    exact h2.trans h1

  have hdM : orderOf (f τ) ∣ M := orderOf_dvd_of_pow_eq_one hfτ
  exact hℓM ((Nat.minFac_dvd _).trans hdM)

private theorem exists_eq_tameCharacter_pow {p : ℕ} (hp : p.Prime) (hP : P.LiesOverPrime p)
    {m : ℕ} (hpm : ¬ p ∣ m) {π : AlgebraicClosure ℚ} (hπ : π ^ m = p)
    (ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ψ (σ * τ) = ψ σ * ψ τ)
    (hord : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ψ σ ^ m = 1) :
    ∃ j : ℕ, j < m ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ψ σ = P.tameCharacter π σ ^ j := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  haveI : NeZero m := ⟨hm0⟩
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hπ
    exact hp0 hπ.symm

  obtain ⟨σ₀, hσ₀, hω⟩ :=
    ValuationSubring.exists_mem_inertiaSubgroupIn_isPrimitiveRoot_tameCharacter P hp hP hpm hπ
  obtain ⟨j, hj, hjeq⟩ := hω.eq_pow_of_pow_eq_one (hord σ₀ hσ₀)
  refine ⟨j, hj, fun σ hσ => ?_⟩

  have htm : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.tameCharacter π τ ^ m = 1 :=
    fun τ => tameCharacter_pow_eq_one P hp0 hπ τ
  have ht0 : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.tameCharacter π τ ≠ 0 :=
    fun τ h0 => by
      have := htm τ
      rw [h0, zero_pow hm0] at this
      exact zero_ne_one this

  set φ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P :=
    fun τ => ψ τ * (P.tameCharacter π τ ^ j)⁻¹ with hφ_def
  have hφmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ,
      φ (σ * τ) = φ σ * φ τ := fun σ hσ τ hτ => by
    simp only [hφ_def, hmul σ hσ τ hτ,
      ValuationSubring.tameCharacter_mul_of_mem_inertiaSubgroupIn P π hπ0 hσ τ, mul_pow, mul_inv]
    ring
  have hφm : ∀ σ ∈ P.inertiaSubgroupIn ℚ, φ σ ^ m = 1 := fun σ hσ => by
    simp only [hφ_def]
    rw [mul_pow, inv_pow, ← pow_mul, mul_comm j m, pow_mul, htm σ, one_pow, inv_one, mul_one,
      hord σ hσ]
  have hφ0 : φ σ₀ = 1 := by
    simp only [hφ_def, ← hjeq]
    exact mul_inv_cancel₀ (pow_ne_zero j (ht0 σ₀))
  have key := eq_one_of_apply_generator P hp hP hpm hπ φ hφmul hφm hσ₀ hω hφ0 hσ

  have hne : P.tameCharacter π σ ^ j ≠ 0 := pow_ne_zero j (ht0 σ)
  have : ψ σ * (P.tameCharacter π σ ^ j)⁻¹ = 1 := key
  rwa [mul_inv_eq_one₀ hne] at this

end TameClassW3

theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime)
    (hP : P.LiesOverPrime p) {m : ℕ} (hpm : ¬ p ∣ m) {π : AlgebraicClosure ℚ} (hπ : π ^ m = p)
    (ψ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → IsLocalRing.ResidueField P)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ψ (σ * τ) = ψ σ * ψ τ)
    (hord : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ψ σ ^ m = 1) :
    ∃ j : ℕ, j < m ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, ψ σ = P.tameCharacter π σ ^ j :=
  TameClassW3.exists_eq_tameCharacter_pow P hp hP hpm hπ ψ hmul hord

end S_ValuationSubring_exists_eq_tameCharacter_pow_of_pow_eq_one
end P2MW
export P2MW.S_ValuationSubring_exists_eq_tameCharacter_pow_of_pow_eq_one (solution)
