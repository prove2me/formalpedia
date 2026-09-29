-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_conjByFiniteIdele_eq_and_conjByFiniteIdele_eq_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/63a5000b-7c38-577c-b43d-78acf71e8a47

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_Matrix_relIndex_inf_conj_diagonal_pow_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_exists_finset_forall_not_mem_localBox_eq
import Theorems.Thm_Submodule_exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_conjByFiniteIdele_eq_and_conjByFiniteIdele_eq_of_squarefree
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

noncomputable section

namespace P2mKcEichlerGenus

section Conj

variable {H : Type*} [Ring H]

def LocConj (g : Hˣ) (A B : AddSubgroup H) : Prop :=
  ∀ x : H, x ∈ A ↔ ∃ y ∈ B, x = (g : H) * y * ((g⁻¹ : Hˣ) : H)

theorem exists_conj_iff (g : Hˣ) (B : AddSubgroup H) (x : H) :
    (∃ y ∈ B, x = (g : H) * y * ((g⁻¹ : Hˣ) : H)) ↔ ((g⁻¹ : Hˣ) : H) * x * (g : H) ∈ B := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : ((g⁻¹ : Hˣ) : H) * ((g : H) * y * ((g⁻¹ : Hˣ) : H)) * (g : H) = y := by
      simp only [← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]
    rw [this]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [← mul_assoc, Units.mul_inv, one_mul, Units.mul_inv_cancel_right]

theorem locConj_iff (g : Hˣ) (A B : AddSubgroup H) :
    LocConj g A B ↔ ∀ x : H, x ∈ A ↔ ((g⁻¹ : Hˣ) : H) * x * (g : H) ∈ B := by
  refine forall_congr' fun x => ?_
  rw [exists_conj_iff]

theorem locConj_one (A : AddSubgroup H) : LocConj 1 A A := by
  rw [locConj_iff]
  intro x
  rw [inv_one, Units.val_one, one_mul, mul_one]

theorem locConj_inf {g : Hˣ} {A A₂ B B₂ : AddSubgroup H} (h₁ : LocConj g A B) (h₂ : LocConj g A₂ B₂) :
    LocConj g (A ⊓ A₂) (B ⊓ B₂) := by
  rw [locConj_iff] at h₁ h₂ ⊢
  intro x
  rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, h₁ x, h₂ x]

theorem units_conj_cancel {M : Type*} [Monoid M] (u w : Mˣ) (W : M) :
    ((u⁻¹ : Mˣ) : M) * (((u : M) * ((w⁻¹ : Mˣ) : M)) * W * ((w : M) * ((u⁻¹ : Mˣ) : M))) * (u : M) =
      ((w⁻¹ : Mˣ) : M) * W * (w : M) := by
  simp only [← mul_assoc, Units.inv_mul, one_mul, Units.inv_mul_cancel_right]

theorem exists_locConj_of_frames {K : Type*} [Field K] (φ : H ≃+* Matrix (Fin 2) (Fin 2) K)
    (P₁ P₂ : Matrix (Fin 2) (Fin 2) K → Prop) (k k' : GL (Fin 2) K) {A A₂ B B₂ : AddSubgroup H}
    (hA : ∀ x, x ∈ A ↔ P₁ (((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * φ x *
      (k : Matrix (Fin 2) (Fin 2) K)))
    (hA₂ : ∀ x, x ∈ A₂ ↔ P₂ (((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * φ x *
      (k : Matrix (Fin 2) (Fin 2) K)))
    (hB : ∀ x, x ∈ B ↔ P₁ (((k'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * φ x *
      (k' : Matrix (Fin 2) (Fin 2) K)))
    (hB₂ : ∀ x, x ∈ B₂ ↔ P₂ (((k'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * φ x *
      (k' : Matrix (Fin 2) (Fin 2) K))) :
    ∃ g : Hˣ, LocConj g A B ∧ LocConj g A₂ B₂ := by
  set g : Hˣ := Units.map (φ.symm : Matrix (Fin 2) (Fin 2) K ≃+* H).toRingHom.toMonoidHom (k * k'⁻¹)
    with hgdef
  have hg : (g : H) = φ.symm ((k : Matrix (Fin 2) (Fin 2) K) *
      ((k'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := rfl
  have hgi : ((g⁻¹ : Hˣ) : H) = φ.symm ((k' : Matrix (Fin 2) (Fin 2) K) *
      ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := rfl
  have key : ∀ x : H,
      ((k'⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * φ (((g⁻¹ : Hˣ) : H) * x * (g : H)) *
          (k' : Matrix (Fin 2) (Fin 2) K) =
        ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * φ x * (k : Matrix (Fin 2) (Fin 2) K) := by
    intro x
    rw [map_mul, map_mul, hg, hgi, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact units_conj_cancel k' k (φ x)
  refine ⟨g, ?_, ?_⟩
  · rw [locConj_iff]
    intro x
    rw [hA x, hB, key x]
  · rw [locConj_iff]
    intro x
    rw [hA₂ x, hB₂, key x]

end Conj

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

theorem exists_locConj_pair [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ Λ₂ Λ' Λ₂' : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : IsMaximalOrder Λ) (hΛ₂ : IsMaximalOrder Λ₂) (hΛ' : IsMaximalOrder Λ') (hΛ₂' : IsMaximalOrder Λ₂')
    {N : ℕ} (hidx : (Λ ⊓ Λ₂).toAddSubgroup.relIndex Λ.toAddSubgroup = N)
    (hidx' : (Λ' ⊓ Λ₂').toAddSubgroup.relIndex Λ'.toAddSubgroup = N) (v : HOS) :
    ∃ g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      LocConj g (Submodule.localBox Λ v) (Submodule.localBox Λ' v) ∧
        LocConj g (Submodule.localBox Λ₂ v) (Submodule.localBox Λ₂' v) := by
  classical
  by_cases hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y
  ·
    refine ⟨1, ?_, ?_⟩
    · rw [IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv hΛ hΛ']
      exact locConj_one _
    · rw [IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv hΛ₂ hΛ₂']
      exact locConj_one _
  ·
    have hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal := fun h => hdiv ((hdef.2.2 v).mpr h)
    obtain ⟨φ, hφ, -⟩ := IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hdef
      (isEichlerOrder_one hΛ) v hq'v (one_notMem v)
    obtain ⟨e, ⟨h, hA, hA₂⟩, -⟩ :=
      IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers hΛ hΛ₂ v
        (natGenerator v) (prime_natGenerator v) (natGenerator_mem_asIdeal v) φ hφ
    obtain ⟨e', ⟨h', hB, hB₂⟩, -⟩ :=
      IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers hΛ' hΛ₂' v
        (natGenerator v) (prime_natGenerator v) (natGenerator_mem_asIdeal v) φ hφ

    have he : e = N.factorization (natGenerator v) := by
      have h1 : (Submodule.localBox Λ v ⊓ Submodule.localBox Λ₂ v).relIndex (Submodule.localBox Λ v) =
          natGenerator v ^ e :=
        Matrix.relIndex_inf_conj_diagonal_pow_eq v (natGenerator v) (prime_natGenerator v)
          (natGenerator_mem_asIdeal v) φ hφ h e _ _ hA hA₂
      rw [relIndex_localBox_inf_eq_pow_factorization hdef hΛ hΛ₂ hidx v] at h1
      exact (Nat.pow_right_injective (prime_natGenerator v).two_le h1).symm
    have he' : e' = N.factorization (natGenerator v) := by
      have h1 : (Submodule.localBox Λ' v ⊓ Submodule.localBox Λ₂' v).relIndex (Submodule.localBox Λ' v) =
          natGenerator v ^ e' :=
        Matrix.relIndex_inf_conj_diagonal_pow_eq v (natGenerator v) (prime_natGenerator v)
          (natGenerator_mem_asIdeal v) φ hφ h' e' _ _ hB hB₂
      rw [relIndex_localBox_inf_eq_pow_factorization hdef hΛ' hΛ₂' hidx' v] at h1
      exact (Nat.pow_right_injective (prime_natGenerator v).two_le h1).symm
    have hee : e' = e := he'.trans he.symm
    subst hee

    set D₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((natGenerator v : v.adicCompletion ℚ) ^ e')⁻¹] with hD₁
    set D₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (natGenerator v : v.adicCompletion ℚ) ^ e'] with hD₂
    have hA₂' : ∀ x, x ∈ Submodule.localBox Λ₂ v ↔ ∀ i j,
        (D₁ * (((h⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ x *
          (h : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) * D₂) i j ∈ v.adicCompletionIntegers ℚ := by
      intro x
      rw [hA₂ x]
      simp only [Matrix.mul_assoc]
    have hB₂' : ∀ x, x ∈ Submodule.localBox Λ₂' v ↔ ∀ i j,
        (D₁ * (((h'⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * φ x *
          (h' : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) * D₂) i j ∈ v.adicCompletionIntegers ℚ := by
      intro x
      rw [hB₂ x]
      simp only [Matrix.mul_assoc]
    exact exists_locConj_of_frames φ
      (fun W => ∀ i j, W i j ∈ v.adicCompletionIntegers ℚ)
      (fun W => ∀ i j, (D₁ * W * D₂) i j ∈ v.adicCompletionIntegers ℚ) h h' hA hA₂' hB hB₂'

theorem exists_family {ι : Type*} {U : ι → Type*} [∀ i, One (U i)] {good : ι → Prop}
    {P : ∀ i, U i → Prop} (hex : ∀ i, ∃ u, P i u) (hgood : ∀ i, good i → P i 1) :
    ∃ G : ∀ i, U i, (∀ i, P i (G i)) ∧ ∀ i, good i → G i = 1 := by
  classical
  refine ⟨fun i => if good i then 1 else Classical.choose (hex i), fun i => ?_, fun i hi => ?_⟩
  · by_cases hi : good i
    · simp only [if_pos hi]; exact hgood i hi
    · simp only [if_neg hi]; exact Classical.choose_spec (hex i)
  · simp only [if_pos hi]

end Local

end P2mKcEichlerGenus

end

open P2mKcEichlerGenus in
set_option maxHeartbeats 3200000 in
theorem solution
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] (hN : Squarefree N)
    (Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛ' : IsMaximalOrder Λ')
    {R R' : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N) (hR' : IsEichlerOrder R' N)
    (hRΛ : R ≤ Λ) (hR'Λ' : R' ≤ Λ') :
    ∃ y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.conjByFiniteIdele R' y = R ∧ Submodule.conjByFiniteIdele Λ' y = Λ := by
  classical

  obtain ⟨Λ₂, hΛ₂, hR2, hidx⟩ :=
    IsEichlerOrder.exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree hdef hN Λ R hΛ hR hRΛ
  obtain ⟨Λ₂', hΛ₂', hR2', hidx'⟩ :=
    IsEichlerOrder.exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree hdef hN Λ' R' hΛ' hR' hR'Λ'
  have hO : IsOrder Λ := hΛ.1
  have hO' : IsOrder Λ' := hΛ'.1
  have hO₂ : IsOrder Λ₂ := hΛ₂.1
  have hO₂' : IsOrder Λ₂' := hΛ₂'.1
  have hRO : IsOrder R := hR.isOrder
  have hRO' : IsOrder R' := hR'.isOrder
  rw [hR2] at hidx
  rw [hR2'] at hidx'

  obtain ⟨S₁, hS₁⟩ := Submodule.exists_finset_forall_not_mem_localBox_eq Λ Λ' hO.fg hO.spanTop hO'.fg hO'.spanTop
  obtain ⟨S₂, hS₂⟩ :=
    Submodule.exists_finset_forall_not_mem_localBox_eq Λ₂ Λ₂' hO₂.fg hO₂.spanTop hO₂'.fg hO₂'.spanTop
  obtain ⟨G, hG, hG1⟩ := exists_family
    (U := fun v : HeightOneSpectrum (𝓞 ℚ) => (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ)
    (good := fun v => Submodule.localBox Λ v = Submodule.localBox Λ' v ∧
      Submodule.localBox Λ₂ v = Submodule.localBox Λ₂' v)
    (P := fun v g => LocConj g (Submodule.localBox Λ v) (Submodule.localBox Λ' v) ∧
      LocConj g (Submodule.localBox Λ₂ v) (Submodule.localBox Λ₂' v))
    (fun v => exists_locConj_pair hdef hΛ hΛ₂ hΛ' hΛ₂' hidx hidx' v)
    (fun v hv => ⟨by rw [hv.1]; exact locConj_one _, by rw [hv.2]; exact locConj_one _⟩)
  have hfin : ∀ X : Submodule ℤ ℍ[ℚ, a, b], (1 : ℍ[ℚ, a, b]) ∈ X →
      ∀ᶠ v in Filter.cofinite, G v ∈ Submodule.localBoxUnits X v := by
    intro X hX
    rw [Filter.eventually_cofinite]
    refine (Finset.finite_toSet (S₁ ∪ S₂)).subset fun v hv => ?_
    by_contra hvS
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hvS
    exact hv (by rw [hG1 v ⟨hS₁ v hvS.1, hS₂ v hvS.2⟩]; exact one_mem_localBoxUnits hX v)

  obtain ⟨β, hβ, -, hβΛ⟩ := Submodule.exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq Λ Λ'
    hO.fg hO.spanTop hO'.fg hO'.spanTop G (hfin Λ' hO'.one_mem) (fun v => (hG v).1)

  have hconjR : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
      x ∈ Submodule.localBox R v ↔ ∃ y ∈ Submodule.localBox R' v,
        x = ((G v : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * y *
          (((G v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
    intro v
    have h1 : LocConj (G v) (Submodule.localBox R v) (Submodule.localBox R' v) := by
      rw [hR2, hR2', Submodule.localBox_inf Λ Λ₂ hO.fg hO.spanTop hO₂.fg hO₂.spanTop v,
        Submodule.localBox_inf Λ' Λ₂' hO'.fg hO'.spanTop hO₂'.fg hO₂'.spanTop v]
      exact locConj_inf (hG v).1 (hG v).2
    exact h1
  obtain ⟨β', hβ', -, hβ'R⟩ := Submodule.exists_units_forall_finiteAdeleEvalAt_eq_conjByFiniteIdele_eq R R'
    hRO.fg hRO.spanTop hRO'.fg hRO'.spanTop G (hfin R' hRO'.one_mem) hconjR

  have hββ' : β = β' := Units.ext (Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun v =>
    (hβ v).trans (hβ' v).symm)
  exact ⟨β, hββ' ▸ hβ'R, hβΛ⟩

end S_QuaternionAlgebra_IsEichlerOrder_exists_conjByFiniteIdele_eq_and_conjByFiniteIdele_eq_of_squarefree
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_conjByFiniteIdele_eq_and_conjByFiniteIdele_eq_of_squarefree (solution)
