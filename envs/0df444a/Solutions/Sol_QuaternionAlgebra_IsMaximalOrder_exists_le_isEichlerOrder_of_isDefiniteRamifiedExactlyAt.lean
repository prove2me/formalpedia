-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c4fe0be9-bb8d-51eb-80dc-e982878cad80

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Matrix_relIndex_inf_conj_diagonal_pow_eq
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace Ws50E4

local notation "Kv" v => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "Ov" v => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v

variable {a b : ℚ}

noncomputable def primeOf (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  (IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose

theorem primeOf_prime (v : HeightOneSpectrum (𝓞 ℚ)) : (primeOf v).Prime :=
  (IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose_spec.1

theorem asIdeal_eq (v : HeightOneSpectrum (𝓞 ℚ)) : v.asIdeal = Ideal.span {((primeOf v : ℕ) : 𝓞 ℚ)} :=
  (IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v).choose_spec.2

theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ primeOf v ∣ n := by
  rw [asIdeal_eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h := congrArg Rat.ringOfIntegersEquiv hc
    rw [map_mul, map_natCast, map_natCast] at h
    have : ((primeOf v : ℕ) : ℤ) ∣ (n : ℤ) := ⟨_, h⟩
    exact_mod_cast this
  · rintro ⟨c, rfl⟩
    exact ⟨c, by push_cast; ring⟩

theorem primeOf_mem_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) : ((primeOf v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  (natCast_mem_asIdeal_iff v _).mpr dvd_rfl

theorem primeOf_injective : Function.Injective primeOf := by
  intro v w h
  have hv := asIdeal_eq v
  have hw := asIdeal_eq w
  rw [← h] at hw
  exact HeightOneSpectrum.ext (hv.trans hw.symm)

theorem exists_primeOf_eq (p : ℕ) (hp : p.Prime) : ∃ v : HeightOneSpectrum (𝓞 ℚ), primeOf v = p := by
  have hprime : (Ideal.span {((p : ℕ) : 𝓞 ℚ)}).IsPrime := by
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have h1 : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
    have h2 : Ideal.span {((p : ℕ) : 𝓞 ℚ)} = (Ideal.span {(p : ℤ)}).map Rat.ringOfIntegersEquiv.symm := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [h2]
    exact Ideal.map_isPrime_of_equiv _
  have hne : Ideal.span {((p : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  let v : HeightOneSpectrum (𝓞 ℚ) := ⟨_, hprime, hne⟩
  refine ⟨v, ?_⟩
  have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := Ideal.subset_span rfl
  have h2 := (natCast_mem_asIdeal_iff v p).mp h1
  exact (Nat.prime_dvd_prime_iff_eq (primeOf_prime v) hp).mp h2

theorem natCast_not_mem_of_not_dvd {q N : ℕ} (hq : q.Prime) (hqN : ¬ q ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hNv : ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
  intro hqv
  rw [natCast_mem_asIdeal_iff] at hNv hqv
  have : primeOf v = q := (Nat.prime_dvd_prime_iff_eq (primeOf_prime v) hq).mp hqv
  exact hqN (this ▸ hNv)

theorem exists_ringEquiv_matrix_of_not_forall_isUnit (ha : a ≠ 0) (hb : b ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv v), x ≠ 0 → IsUnit x) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv v) ≃+* Matrix (Fin 2) (Fin 2) (Kv v),
      ∀ r : Kv v, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (Kv v)) := by

  obtain ⟨φ₀, hφ₀, hφ₀'⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := Kv v) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (Kv v) a) (d₂ := (0 : Kv v)) (d₃ := algebraMap ℚ (Kv v) b) rfl (map_zero _) rfl
    (AlgEquiv.refl (R := Kv v) (A₁ := ℍ[Kv v, algebraMap ℚ (Kv v) a, (0 : Kv v), algebraMap ℚ (Kv v) b]))
  have hnd' : ¬ ∀ x : ℍ[Kv v, algebraMap ℚ (Kv v) a, (0 : Kv v), algebraMap ℚ (Kv v) b], x ≠ 0 → IsUnit x := by
    intro hall
    apply hnd
    intro x hx
    have hx' : φ₀ x ≠ 0 := fun h0 => hx (by simpa using congrArg φ₀.symm h0)
    have := hall (φ₀ x) hx'
    simpa using this.map φ₀.symm
  have hiso := (QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero (Kv v) (algebraMap ℚ (Kv v) a)
    (algebraMap ℚ (Kv v) b)).not.mp hnd'
  simp only [not_forall] at hiso
  obtain ⟨x₀, x₁, x₂, x₃, h0, hne⟩ := hiso
  have ha' : algebraMap ℚ (Kv v) a ≠ 0 := (map_ne_zero (algebraMap ℚ (Kv v))).mpr ha
  have hb' : algebraMap ℚ (Kv v) b ≠ 0 := (map_ne_zero (algebraMap ℚ (Kv v))).mpr hb
  have h2 : (2 : Kv v) ≠ 0 := by
    have := (map_ne_zero (algebraMap ℚ (Kv v))).mpr (two_ne_zero : (2 : ℚ) ≠ 0)
    simpa using this
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero (Kv v) h2
    (algebraMap ℚ (Kv v) a) (algebraMap ℚ (Kv v) b) ha' hb' x₀ x₁ x₂ x₃ hne h0
  obtain ⟨φ, hφ, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := Kv v) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (Kv v) a) (d₂ := (0 : Kv v)) (d₃ := algebraMap ℚ (Kv v) b) rfl (map_zero _) rfl ψ
  exact ⟨φ, hφ⟩

theorem natCast_ne_zero_Kv (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) : (n : Kv v) ≠ 0 := by
  have := (map_ne_zero (algebraMap ℚ (Kv v))).mpr (Nat.cast_ne_zero.mpr hn : (n : ℚ) ≠ 0)
  rwa [map_natCast] at this

section Mat

variable {K : Type*} [Field K]

theorem diagonal_one_inv (c : K) (hc : c ≠ 0) :
    (Matrix.diagonal ![(1 : K), c])⁻¹ = Matrix.diagonal ![(1 : K), c⁻¹] := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc]

theorem sandwich (h : GL (Fin 2) K) (A B M : Matrix (Fin 2) (Fin 2) K) :
    ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (((h : Matrix (Fin 2) (Fin 2) K) * A * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * M *
          ((h : Matrix (Fin 2) (Fin 2) K) * B * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) *
      (h : Matrix (Fin 2) (Fin 2) K) =
    A * (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M * (h : Matrix (Fin 2) (Fin 2) K)) * B := by
  have e1 : ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (h : Matrix (Fin 2) (Fin 2) K) = 1 :=
    Units.inv_mul h
  have e2 : ∀ X : Matrix (Fin 2) (Fin 2) K,
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((h : Matrix (Fin 2) (Fin 2) K) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
  simp only [Matrix.mul_assoc, e1, Matrix.mul_one, e2]

end Mat

set_option maxHeartbeats 3200000 in
theorem assembly {q : ℕ} (hq : q.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) (hN : N ≠ 0) (hqN : ¬ q ∣ N) :
    ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], Λ ≤ Λ₁ ∧ QuaternionAlgebra.IsEichlerOrder Λ N := by
  classical
  have ha : a ≠ 0 := hB.1.ne
  have hb : b ≠ 0 := hB.2.1.ne
  have hΛ₁ : QuaternionAlgebra.IsOrder Λ₁ := h₁.1

  have hI : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]; exact_mod_cast hN
  set S : Finset (HeightOneSpectrum (𝓞 ℚ)) := (Ideal.finite_factors hI).toFinset with hS
  have hmemS : ∀ v, v ∈ S ↔ ((N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

  have key : ∀ v ∈ S, ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv v) ≃+* Matrix (Fin 2) (Fin 2) (Kv v),
      (∀ r : Kv v, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (Kv v))) ∧
      ∃ h : GL (Fin 2) (Kv v), ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv v),
        x ∈ Submodule.localBox Λ₁ v ↔
          ∀ i j, (((h⁻¹ : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)) * φ x *
            (h : Matrix (Fin 2) (Fin 2) (Kv v))) i j ∈ (Ov v) := by
    intro v hv
    have hqv : ((q : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := natCast_not_mem_of_not_dvd hq hqN v ((hmemS v).mp hv)
    have hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv v), x ≠ 0 → IsUnit x := fun h => hqv ((hB.2.2 v).mp h)
    obtain ⟨φ, hφ⟩ := exists_ringEquiv_matrix_of_not_forall_isUnit ha hb v hnd
    obtain ⟨h, hh⟩ :=
      QuaternionAlgebra.IsMaximalOrder.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers h₁ v φ hφ
    exact ⟨φ, hφ, h, hh⟩
  choose φ hφ h hh using key

  let e : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun v => N.factorization (primeOf v)
  have hℓpow : ∀ v, ((primeOf v : Kv v)) ^ e v ≠ 0 := fun v =>
    pow_ne_zero _ (natCast_ne_zero_Kv v (primeOf_prime v).ne_zero)
  let xM : ∀ v, Matrix (Fin 2) (Fin 2) (Kv v) := fun v => Matrix.diagonal ![(1 : Kv v), (primeOf v : Kv v) ^ e v]
  have hxMdet : ∀ v, (xM v).det ≠ 0 := by
    intro v; simp [xM, Matrix.det_diagonal, Fin.prod_univ_two, hℓpow v]
  let xG : ∀ v, GL (Fin 2) (Kv v) := fun v => Matrix.GeneralLinearGroup.mkOfDetNeZero (xM v) (hxMdet v)

  let y : ∀ v : HeightOneSpectrum (𝓞 ℚ), (ℍ[ℚ, a, b] ⊗[ℚ] (Kv v))ˣ := fun v =>
    if hv : v ∈ S then
      Units.map ((φ v hv).symm : Matrix (Fin 2) (Fin 2) (Kv v) ≃+* _).toRingHom.toMonoidHom
        (h v hv * xG v * (h v hv)⁻¹)
    else 1

  obtain ⟨β, hβS, hβ1⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) S y
  set Λ₂ : Submodule ℤ ℍ[ℚ, a, b] := Submodule.conjByFiniteIdele Λ₁ β with hΛ₂
  have h₂ : QuaternionAlgebra.IsMaximalOrder Λ₂ := QuaternionAlgebra.IsMaximalOrder.conjByFiniteIdele h₁ β
  have hΛ₂o : QuaternionAlgebra.IsOrder Λ₂ := h₂.1
  refine ⟨Λ₁ ⊓ Λ₂, inf_le_left, Λ₁, Λ₂, h₁, h₂, rfl, ?_⟩

  have hΛo : QuaternionAlgebra.IsOrder (Λ₁ ⊓ Λ₂) := hΛ₁.inf hΛ₂o
  rw [Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ₁ (Λ₁ ⊓ Λ₂) hΛ₁.fg hΛ₁.spanTop hΛo.fg
    hΛo.spanTop inf_le_left]

  have hloc : ∀ v, (Submodule.localBox (Λ₁ ⊓ Λ₂) v).relIndex (Submodule.localBox Λ₁ v) =
      if v ∈ S then primeOf v ^ e v else 1 := by
    intro v
    rw [Submodule.localBox_inf Λ₁ Λ₂ hΛ₁.fg hΛ₁.spanTop hΛ₂o.fg hΛ₂o.spanTop v]
    have hevβ : ∀ v, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (β : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = y v := by
      intro w
      by_cases hw : w ∈ S
      · exact hβS w hw
      · rw [hβ1 w hw]; simp [y, hw]
    have hevβinv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
        ((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        ((y v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] (Kv v))ˣ) := by
      have hu : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v : _ →ₐ[ℚ] _).toRingHom.toMonoidHom β = y v :=
        Units.ext (hevβ v)
      rw [← hu, Units.coe_map_inv]
      rfl
    have hbox2 : ∀ x, x ∈ Submodule.localBox Λ₂ v ↔ ((y v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] (Kv v))ˣ) * x * (y v) ∈ Submodule.localBox Λ₁ v := by
      intro x
      rw [hΛ₂, Submodule.mem_localBox_conjByFiniteIdele_iff Λ₁ hΛ₁.fg hΛ₁.spanTop β v x, hevβ, hevβinv]
      constructor
      · rintro ⟨y', hy', rfl⟩
        simpa [mul_assoc] using hy'
      · intro hx
        exact ⟨_, hx, by simp [mul_assoc]⟩
    by_cases hv : v ∈ S
    · rw [if_pos hv]

      have hφy : Units.map ((φ v hv : _ ≃+* _).toRingHom.toMonoidHom) (y v) = h v hv * xG v * (h v hv)⁻¹ := by
        apply Units.ext
        simp only [y, dif_pos hv, Units.coe_map, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe,
          MonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
      have hφy1 : (φ v hv) (y v : ℍ[ℚ, a, b] ⊗[ℚ] (Kv v)) =
          (h v hv : Matrix (Fin 2) (Fin 2) (Kv v)) * xM v * ((h v hv)⁻¹ : GL (Fin 2) (Kv v)) := by
        have := congrArg Units.val hφy
        simp [Units.val_mul] at this ⊢
        exact this
      have hφy2 : (φ v hv) ((y v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] (Kv v))ˣ) =
          (h v hv : Matrix (Fin 2) (Fin 2) (Kv v)) * (xM v)⁻¹ * ((h v hv)⁻¹ : GL (Fin 2) (Kv v)) := by
        have h1 : (φ v hv) ((y v)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] (Kv v))ˣ) =
            ((Units.map ((φ v hv : _ ≃+* _).toRingHom.toMonoidHom) (y v))⁻¹ : (Matrix (Fin 2) (Fin 2) (Kv v))ˣ) := by
          rw [Units.coe_map_inv]; rfl
        rw [h1, hφy, show (h v hv * xG v * (h v hv)⁻¹)⁻¹ = h v hv * (xG v)⁻¹ * (h v hv)⁻¹ by group,
          Units.val_mul, Units.val_mul, Matrix.coe_units_inv (xG v)]
        rfl
      have hO' : ∀ x, x ∈ Submodule.localBox Λ₂ v ↔ ∀ i j,
          (Matrix.diagonal ![(1 : Kv v), (((primeOf v : Kv v)) ^ e v)⁻¹] *
            ((h v hv)⁻¹ : GL (Fin 2) (Kv v)) * (φ v hv) x * (h v hv : Matrix (Fin 2) (Fin 2) (Kv v)) *
            Matrix.diagonal ![(1 : Kv v), (primeOf v : Kv v) ^ e v]) i j ∈ (Ov v) := by
        intro x
        rw [hbox2, hh v hv, map_mul, map_mul, hφy1, hφy2, ← diagonal_one_inv _ (hℓpow v)]
        rw [show (Matrix.diagonal ![(1 : Kv v), (primeOf v : Kv v) ^ e v]) = xM v from rfl, sandwich]
        simp only [Matrix.mul_assoc]
      exact Matrix.relIndex_inf_conj_diagonal_pow_eq v (primeOf v) (primeOf_prime v) (primeOf_mem_asIdeal v)
        (φ v hv) (hφ v hv) (h v hv) (e v) _ _ (hh v hv) hO'
    · rw [if_neg hv]
      have hy1 : y v = 1 := by simp [y, hv]
      have : Submodule.localBox Λ₂ v = Submodule.localBox Λ₁ v := by
        ext x; rw [hbox2, hy1]; simp
      rw [this, inf_idem, AddSubgroup.relIndex_self]

  rw [finprod_congr hloc]
  have hsupp : (Function.mulSupport fun v => if v ∈ S then primeOf v ^ e v else 1) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    exact hv (if_neg hvS)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  rw [Finset.prod_congr rfl (fun v hv => if_pos hv)]
  have hNf := Nat.prod_factorization_pow_eq_self hN
  rw [Finsupp.prod, Nat.support_factorization] at hNf
  rw [← hNf]
  refine Finset.prod_nbij primeOf (fun v hv => ?_) (fun v _ w _ hvw => primeOf_injective hvw) (fun p hp => ?_)
    (fun v _ => rfl)
  · rw [hmemS] at hv
    exact Nat.mem_primeFactors.mpr ⟨primeOf_prime v, (natCast_mem_asIdeal_iff v N).mp hv, hN⟩
  · rw [Finset.mem_coe, Nat.mem_primeFactors] at hp
    obtain ⟨v, hv⟩ := exists_primeOf_eq p hp.1
    refine ⟨v, ?_, hv⟩
    rw [Finset.mem_coe, hmemS, natCast_mem_asIdeal_iff, hv]
    exact hp.2.1

end Ws50E4

theorem solution
    {a b : ℚ} {q : ℕ} (hq : q.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) (hN : N ≠ 0) (hqN : ¬ q ∣ N) :
    ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], Λ ≤ Λ₁ ∧ QuaternionAlgebra.IsEichlerOrder Λ N := by
  exact Ws50E4.assembly hq hB h₁ N hN hqN

end S_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt (solution)
