-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_generalLinearGroup_forall_mem_localBox_iff_of_inf_eq_of_dvd_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6f0ec876-062f-5bbd-96d7-f2251f4b1eea

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_Matrix_relIndex_inf_conj_diagonal_pow_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_exists_finset_forall_not_mem_localBox_eq
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_relIndex_eq_of_isMaximalOrder_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_generalLinearGroup_forall_mem_localBox_iff_of_inf_eq_of_dvd_of_squarefree
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

noncomputable section

namespace TwinFrame

section Places

open Rat.HeightOneSpectrum

local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

theorem natCast_mem_asIdeal_iff (w : HOS) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ natGenerator w ∣ n := by
  rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_mem_asIdeal (w : HOS) : (natGenerator w : 𝓞 ℚ) ∈ w.asIdeal :=
  (natCast_mem_asIdeal_iff w _).mpr dvd_rfl

theorem natGenerator_injective : Function.Injective (natGenerator (R := 𝓞 ℚ)) := fun v w h =>
  (primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

theorem one_notMem (w : HOS) : ((1 : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [Nat.cast_one]
  exact fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem factorization_natGenerator_eq_of_prod_eq {S : Finset HOS} {f : HOS → ℕ} {N : ℕ}
    (hN : ∏ v ∈ S, natGenerator v ^ f v = N) (hf : ∀ w ∉ S, f w = 0) (w : HOS) :
    N.factorization (natGenerator w) = f w := by
  classical
  have h1 : N.factorization = ∑ v ∈ S, f v • (natGenerator v).factorization := by
    rw [← hN, Nat.factorization_prod (fun v _ => pow_ne_zero _ (prime_natGenerator v).ne_zero)]
    exact Finset.sum_congr rfl fun v _ => Nat.factorization_pow _ _
  rw [h1, Finsupp.finsetSum_apply]
  by_cases hw : w ∈ S
  · rw [Finset.sum_eq_single w]
    · rw [Finsupp.smul_apply, (prime_natGenerator w).factorization, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    · intro v _ hvw
      rw [Finsupp.smul_apply, (prime_natGenerator v).factorization, Finsupp.single_apply,
        if_neg (fun h => hvw (natGenerator_injective h)), smul_zero]
    · intro h; exact absurd hw h
  · rw [hf w hw]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finsupp.smul_apply, (prime_natGenerator v).factorization, Finsupp.single_apply, if_neg, smul_zero]
    intro h
    exact hw (natGenerator_injective h ▸ hv)

end Places

section Local

open Rat.HeightOneSpectrum

local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

variable {a b : ℚ} {q' : ℕ}

theorem isEichlerOrder_one {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) : IsEichlerOrder Λ 1 :=
  ⟨Λ, Λ, hΛ, hΛ, (inf_idem Λ).symm, AddSubgroup.relIndex_self _⟩

theorem one_mem_localBox {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : (1 : ℍ[ℚ, a, b]) ∈ X) (v : HOS) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox X v := by
  rw [Algebra.TensorProduct.one_def]
  exact AddSubgroup.subset_closure ⟨1, hX, 1, one_mem _, rfl⟩

theorem one_mem_localBoxUnits {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : (1 : ℍ[ℚ, a, b]) ∈ X) (v : HOS) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits X v := by
  rw [Submodule.mem_localBoxUnits_iff, inv_one, Units.val_one]
  exact ⟨one_mem_localBox hX v, one_mem_localBox hX v⟩

theorem relIndex_localBox_inf_eq_pow_factorization [Fact q'.Prime]
    (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) (hΛ₂ : IsMaximalOrder Λ₂)
    {N : ℕ} (hidx : (Λ ⊓ Λ₂).toAddSubgroup.relIndex Λ.toAddSubgroup = N) (v : HOS) :
    (Submodule.localBox Λ v ⊓ Submodule.localBox Λ₂ v).relIndex (Submodule.localBox Λ v) =
      natGenerator v ^ N.factorization (natGenerator v) := by
  classical
  have hO : IsOrder Λ := hΛ.1
  have hO₂ : IsOrder Λ₂ := hΛ₂.1
  have hRO : IsOrder (Λ ⊓ Λ₂) := hO.inf hO₂

  have hpow : ∀ w : HOS, ∃ f : ℕ,
      (Submodule.localBox Λ w ⊓ Submodule.localBox Λ₂ w).relIndex (Submodule.localBox Λ w) =
        natGenerator w ^ f := by
    intro w
    by_cases hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, y ≠ 0 → IsUnit y
    · refine ⟨0, ?_⟩
      rw [IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit w hdiv hΛ hΛ₂, inf_idem,
        AddSubgroup.relIndex_self, pow_zero]
    · have hq'w : (q' : 𝓞 ℚ) ∉ w.asIdeal := fun h => hdiv ((hdef.2.2 w).mpr h)
      obtain ⟨φ, hφ, -⟩ := IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef
        (isEichlerOrder_one hΛ) w hq'w (one_notMem w)
      obtain ⟨e, ⟨h, h1, h2⟩, -⟩ :=
        IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers hΛ hΛ₂ w
          (natGenerator w) (prime_natGenerator w) (natGenerator_mem_asIdeal w) φ hφ
      exact ⟨e, Matrix.relIndex_inf_conj_diagonal_pow_eq w (natGenerator w) (prime_natGenerator w)
        (natGenerator_mem_asIdeal w) φ hφ h e _ _ h1 h2⟩
  choose f hf using hpow
  obtain ⟨S, hS⟩ := Submodule.exists_finset_forall_not_mem_localBox_eq Λ Λ₂ hO.fg hO.spanTop hO₂.fg hO₂.spanTop
  have h1S : ∀ w ∉ S,
      (Submodule.localBox Λ w ⊓ Submodule.localBox Λ₂ w).relIndex (Submodule.localBox Λ w) = 1 := by
    intro w hw
    rw [hS w hw, inf_idem, AddSubgroup.relIndex_self]
  have hf0 : ∀ w ∉ S, f w = 0 := by
    intro w hw
    have h1 := h1S w hw
    rw [hf w, Nat.pow_eq_one] at h1
    exact h1.resolve_left (prime_natGenerator w).one_lt.ne'
  have hprod : ∏ᶠ w, (Submodule.localBox Λ w ⊓ Submodule.localBox Λ₂ w).relIndex (Submodule.localBox Λ w) = N := by
    rw [← hidx, Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ (Λ ⊓ Λ₂) hO.fg hO.spanTop
      hRO.fg hRO.spanTop inf_le_left]
    exact finprod_congr fun w => by
      rw [Submodule.localBox_inf Λ Λ₂ hO.fg hO.spanTop hO₂.fg hO₂.spanTop w]
  have hsupp : Function.mulSupport
      (fun w : HOS => (Submodule.localBox Λ w ⊓ Submodule.localBox Λ₂ w).relIndex (Submodule.localBox Λ w)) ⊆
        (S : Set HOS) := by
    intro w hw
    by_contra hwS
    exact hw (h1S w hwS)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp] at hprod
  have hprod' : ∏ w ∈ S, natGenerator w ^ f w = N :=
    (Finset.prod_congr rfl fun w _ => (hf w).symm).trans hprod
  rw [hf v, factorization_natGenerator_eq_of_prod_eq hprod' hf0 v]

end Local

end TwinFrame

end

open TwinFrame Rat.HeightOneSpectrum in
open QuaternionAlgebra CerednikDrinfeld in
theorem solution
    {rbar N : ℕ} [Fact rbar.Prime] [NeZero N] (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ (φ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h : GL (Fin 2) (v.adicCompletion ℚ)),
      (∀ c : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      (∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] v.adicCompletion ℚ, x ∈ Submodule.localBox Λ₁ v ↔ ∀ i j,
        (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] v.adicCompletion ℚ, x ∈ Submodule.localBox Λ₁s v ↔ ∀ i j,
        (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((ℓ : v.adicCompletion ℚ))⁻¹] *
          ((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ x * (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
          Matrix.diagonal ![(1 : v.adicCompletion ℚ), (ℓ : v.adicCompletion ℚ)]) i j ∈ v.adicCompletionIntegers ℚ) := by
  classical
  have hrbP : rbar.Prime := Fact.out

  have hℓgen : natGenerator v = ℓ :=
    ((Nat.prime_dvd_prime_iff_eq (prime_natGenerator v) hℓ).mp ((natCast_mem_asIdeal_iff v ℓ).mp hℓv))
  have hrbv : ((rbar : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    have h1 : natGenerator v = rbar :=
      (Nat.prime_dvd_prime_iff_eq (prime_natGenerator v) hrbP).mp ((natCast_mem_asIdeal_iff v rbar).mp h)
    exact hrbarN (h1 ▸ hℓgen ▸ hℓN)
  obtain ⟨φ, hφ, -⟩ := IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef
    (isEichlerOrder_one hΛ₁) v hrbv (one_notMem v)
  obtain ⟨e, ⟨h, h1, h2⟩, -⟩ :=
    IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers hΛ₁ hΛ₁s v ℓ hℓ hℓv φ hφ

  have hidx : (Λ₁ ⊓ Λ₁s).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N := by
    rw [htwin]
    exact IsEichlerOrder.relIndex_eq_of_isMaximalOrder_of_le hrbP hdef hR₁ hΛ₁ hRΛ₁
  have hloc := relIndex_localBox_inf_eq_pow_factorization hdef hΛ₁ hΛ₁s hidx v
  have hloc' : (Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ₁s v).relIndex (Submodule.localBox Λ₁ v) = ℓ ^ e :=
    Matrix.relIndex_inf_conj_diagonal_pow_eq v ℓ hℓ hℓv φ hφ h e _ _ h1 h2
  have hfac : N.factorization ℓ = 1 := by
    have hle : N.factorization ℓ ≤ 1 := hN.natFactorization_le_one ℓ
    have hpos : 0 < N.factorization ℓ := hℓ.factorization_pos_of_dvd (NeZero.ne N) hℓN
    omega
  have he : e = 1 := by
    rw [hloc, hℓgen, hfac] at hloc'
    exact (Nat.pow_right_injective hℓ.two_le hloc').symm
  subst he
  refine ⟨φ, h, hφ, h1, fun x => ?_⟩
  rw [h2 x, pow_one]

end S_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_generalLinearGroup_forall_mem_localBox_iff_of_inf_eq_of_dvd_of_squarefree
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_generalLinearGroup_forall_mem_localBox_iff_of_inf_eq_of_dvd_of_squarefree (solution)
