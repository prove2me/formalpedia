-- Prove2me | solution 1 for QuaternionAlgebra.localBox_eq_localBox_of_forall_iff_mem_range_of_isMaximalOrder_of_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a3c81b75-b14d-592b-a58f-a706fbfdafa7

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem
import Theorems.Thm_Matrix_bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_localBox_eq_localBox_of_forall_iff_mem_range_of_isMaximalOrder_of_mem_asIdeal
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField

namespace RamTransfer

local notation "Kv" w => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w
local notation "Ov" w => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ w

section Nrd
variable {K : Type*} [CommRing K] {c₁ c₃ : K}

theorem nrd_mul' (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_one' : QuaternionAlgebra.nrd (1 : ℍ[K, c₁, c₃]) = 1 := by
  rw [show (1 : ℍ[K, c₁, c₃]) = ⟨1, 0, 0, 0⟩ from rfl, QuaternionAlgebra.nrd_mk]; ring
end Nrd

variable {a b : ℚ}

theorem exists_coords (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+*
        ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b],
      ∀ (x : ℍ[ℚ, a, b]) (r : Kv w),
        φ (x ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (Kv w) x.re, algebraMap ℚ (Kv w) x.imI,
          algebraMap ℚ (Kv w) x.imJ, algebraMap ℚ (Kv w) x.imK⟩ :
            ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]) := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := Kv w) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (Kv w) a) (d₂ := (0 : Kv w)) (d₃ := algebraMap ℚ (Kv w) b) rfl (map_zero _) rfl
    (AlgEquiv.refl (R := Kv w) (A₁ := ℍ[Kv w, algebraMap ℚ (Kv w) a, (0 : Kv w), algebraMap ℚ (Kv w) b]))
  exact ⟨φ, fun x r => by rw [hφ]; rfl⟩

theorem coords_one_tmul (w : HeightOneSpectrum (𝓞 ℚ))
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]}
    (hφ : ∀ (x : ℍ[ℚ, a, b]) (r : Kv w),
        φ (x ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (Kv w) x.re, algebraMap ℚ (Kv w) x.imI,
          algebraMap ℚ (Kv w) x.imJ, algebraMap ℚ (Kv w) x.imK⟩ :
            ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]))
    (c : Kv w) : φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = algebraMap (Kv w) _ c := by
  rw [hφ, QuaternionAlgebra.algebraMap_eq]
  ext <;> simp

theorem tmul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    {c : Kv w} (hc : c ∈ Ov w) : z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem mul_neg' (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) : x * (-y) = -(x * y) :=
  eq_neg_of_add_eq_zero_left (by rw [← mul_add, neg_add_cancel, mul_zero])

theorem neg_mul' (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) : (-x) * y = -(x * y) :=
  eq_neg_of_add_eq_zero_left (by rw [← add_mul, neg_add_cancel, zero_mul])

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)} (hx : x ∈ Submodule.localBox Λ w) (hy : y ∈ Submodule.localBox Λ w) :
    x * y ∈ Submodule.localBox Λ w := by
  refine AddSubgroup.closure_induction (p := fun y _ => x * y ∈ Submodule.localBox Λ w) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨z', hz', c', hc', rfl⟩
    refine AddSubgroup.closure_induction (p := fun x _ => x * (z' ⊗ₜ[ℚ] c') ∈ Submodule.localBox Λ w) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨z, hz, c, hc, rfl⟩
      beta_reduce
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox (hΛ.mul_mem hz hz') w (mul_mem hc hc')
    · beta_reduce; rw [zero_mul]; exact zero_mem _
    · intro x₁ x₂ _ _ h₁ h₂; beta_reduce; rw [add_mul]; exact add_mem h₁ h₂
    · intro x₁ _ h₁; beta_reduce; rw [neg_mul' w]; exact neg_mem h₁
  · beta_reduce; rw [mul_zero]; exact zero_mem _
  · intro y₁ y₂ _ _ h₁ h₂; beta_reduce; rw [mul_add]; exact add_mem h₁ h₂
  · intro y₁ _ h₁; beta_reduce; rw [mul_neg' w]; exact neg_mem h₁

theorem localBox_mul_one_tmul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)} (hx : x ∈ Submodule.localBox Λ w) {c : Kv w} (hc : c ∈ Ov w) :
    x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ w := by
  refine AddSubgroup.closure_induction (p := fun x _ => x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ w)
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨z, hz, c', hc', rfl⟩
    beta_reduce
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact tmul_mem_localBox hz w (mul_mem hc' hc)
  · beta_reduce; rw [zero_mul]; exact zero_mem _
  · intro x₁ x₂ _ _ h₁ h₂; beta_reduce; rw [add_mul]; exact add_mem h₁ h₂
  · intro x₁ _ h₁; beta_reduce; rw [neg_mul' w]; exact neg_mem h₁

noncomputable abbrev ℓ (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)

theorem ℓ_prime (w : HeightOneSpectrum (𝓞 ℚ)) : (ℓ w).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w).2

theorem intCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℤ) : (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (ℓ w : ℤ) ∣ z := by
  rw [← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_intCast,
    ← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, Int.cast_id]
  rfl

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : (n : 𝓞 ℚ) ∈ w.asIdeal ↔ ℓ w ∣ n := by
  rw [show (n : 𝓞 ℚ) = ((n : ℤ) : 𝓞 ℚ) from (Int.cast_natCast n).symm, intCast_mem_asIdeal_iff, Int.natCast_dvd_natCast]

theorem ℓ_eq_of_prime_mem (w : HeightOneSpectrum (𝓞 ℚ)) {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal) : ℓ w = p :=
  (Nat.prime_dvd_prime_iff_eq (ℓ_prime w) hp).mp ((natCast_mem_asIdeal_iff w p).mp hpw)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) :
    Valued.v (algebraMap ℚ (Kv w) q) = w.valuation ℚ q := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q

theorem valuation_natCast_lt_one_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : w.valuation ℚ (n : ℚ) < 1 ↔ ℓ w ∣ n := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_dvd,
    Ideal.dvd_span_singleton, natCast_mem_asIdeal_iff]

theorem v_natCast_lt_one (w : HeightOneSpectrum (𝓞 ℚ)) {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    Valued.v ((p : ℕ) : Kv w) < 1 := by
  rw [← map_natCast (algebraMap ℚ (Kv w)), valued_algebraMap, valuation_natCast_lt_one_iff,
    ℓ_eq_of_prime_mem w hp hpw]

theorem forall_mulVec_mem {n : Type*} [Fintype n] [DecidableEq n] (w : HeightOneSpectrum (𝓞 ℚ))
    (M : Matrix n n (Kv w)) :
    (∀ i j, M i j ∈ Ov w) ↔ ∀ v : n → Kv w, (∀ i, v i ∈ Ov w) → ∀ i, (M.mulVec v) i ∈ Ov w := by
  constructor
  · intro hM v hv i
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (hM i j) (hv j)
  · intro h i j
    have := h (Pi.single j 1) (fun i' => by
      by_cases hi : i' = j
      · subst hi; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hi]; exact zero_mem _) i
    simpa [Matrix.mulVec_single_one] using this

theorem exists_mul_pow_le_one {γ δ : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (hγ0 : γ ≠ 0) (hδ : δ ≠ 0) :
    ∃ m : ℕ, δ * γ ^ (2 * m) ≤ 1 := by
  obtain ⟨zγ, rfl⟩ : ∃ z : ℤ, γ = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    ⟨Multiplicative.toAdd (WithZero.unzero hγ0), by simp [WithZero.coe_unzero hγ0]⟩
  obtain ⟨zδ, rfl⟩ : ∃ z : ℤ, δ = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    ⟨Multiplicative.toAdd (WithZero.unzero hδ), by simp [WithZero.coe_unzero hδ]⟩
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt] at hγ
  refine ⟨zδ.toNat, ?_⟩
  rw [← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe,
    ← ofAdd_nsmul, ← ofAdd_add, ← ofAdd_zero, Multiplicative.ofAdd_le, nsmul_eq_mul]
  have h1 : (zδ : ℤ) ≤ (zδ.toNat : ℤ) := Int.self_le_toNat zδ
  push_cast
  nlinarith

theorem coords_one_tmul' (w : HeightOneSpectrum (𝓞 ℚ))
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]}
    (hφ : ∀ (x : ℍ[ℚ, a, b]) (r : Kv w),
        φ (x ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (Kv w) x.re, algebraMap ℚ (Kv w) x.imI,
          algebraMap ℚ (Kv w) x.imJ, algebraMap ℚ (Kv w) x.imK⟩ :
            ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]))
    (c : Kv w) : φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
      c • (1 : ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]) := by
  rw [hφ]
  ext <;> simp

noncomputable def algHomOfCoords (w : HeightOneSpectrum (𝓞 ℚ)) {N : Type} [Fintype N] [DecidableEq N]
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b])
    (hφ1 : ∀ c : Kv w, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
      c • (1 : ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]))
    (f : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) →+* Matrix N N (Kv w))
    (hf : ∀ c : Kv w, f ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix N N (Kv w))) :
    ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b] →ₐ[Kv w] Matrix N N (Kv w) :=
  AlgHom.mk (f.comp φ.symm.toRingHom) (fun c => by
    have h1 : algebraMap (Kv w) ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b] c =
        c • (1 : ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]) := Algebra.algebraMap_eq_smul_one c
    have h2 : algebraMap (Kv w) (Matrix N N (Kv w)) c = c • (1 : Matrix N N (Kv w)) :=
      Algebra.algebraMap_eq_smul_one c
    show f (φ.symm (algebraMap (Kv w) _ c)) = algebraMap (Kv w) _ c
    rw [h1, h2, ← hφ1 c, RingEquiv.symm_apply_apply, hf])

theorem algHomOfCoords_apply (w : HeightOneSpectrum (𝓞 ℚ)) {N : Type} [Fintype N] [DecidableEq N]
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b])
    (hφ1 : ∀ c : Kv w, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
      c • (1 : ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]))
    (f : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) →+* Matrix N N (Kv w))
    (hf : ∀ c : Kv w, f ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix N N (Kv w)))
    (d : ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]) :
    algHomOfCoords w φ hφ1 f hf d = f (φ.symm d) := rfl

theorem nrd_natCast' {K : Type*} [CommRing K] {c₁ c₃ : K} (n : ℕ) :
    QuaternionAlgebra.nrd ((n : ℕ) : ℍ[K, c₁, c₃]) = (n : K) ^ 2 := by
  rw [show ((n : ℕ) : ℍ[K, c₁, c₃]) = ⟨(n : K), 0, 0, 0⟩ by ext <;> simp, QuaternionAlgebra.nrd_mk]; ring

noncomputable def linOfCoords (w : HeightOneSpectrum (𝓞 ℚ)) {a₁ b₁ : ℚ} {V : Type*} [AddCommGroup V] [Module (Kv w) V]
    (φH : ℍ[ℚ, a₁, b₁] ⊗[ℚ] (Kv w) ≃+* ℍ[Kv w, algebraMap ℚ (Kv w) a₁, algebraMap ℚ (Kv w) b₁])
    (hφH1 : ∀ c : Kv w, φH ((1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c) =
      c • (1 : ℍ[Kv w, algebraMap ℚ (Kv w) a₁, algebraMap ℚ (Kv w) b₁]))
    (ξ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] (Kv w) → V)
    (hadd : ∀ x y, ξ (x + y) = ξ x + ξ y)
    (hsmul : ∀ (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] (Kv w)) (c : Kv w), ξ (x * (1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c) = c • ξ x) :
    ℍ[Kv w, algebraMap ℚ (Kv w) a₁, algebraMap ℚ (Kv w) b₁] →ₗ[Kv w] V where
  toFun y := ξ (φH.symm y)
  map_add' y y' := by
    show ξ (φH.symm (y + y')) = ξ (φH.symm y) + ξ (φH.symm y')
    rw [map_add, hadd]
  map_smul' c y := by
    show ξ (φH.symm (c • y)) = c • ξ (φH.symm y)
    have : φH.symm (c • y) = φH.symm y * (1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c := φH.injective (by
      rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply, hφH1, Algebra.mul_smul_comm, mul_one])
    rw [this, hsmul]

theorem linOfCoords_apply (w : HeightOneSpectrum (𝓞 ℚ)) {a₁ b₁ : ℚ} {V : Type*} [AddCommGroup V] [Module (Kv w) V]
    (φH : ℍ[ℚ, a₁, b₁] ⊗[ℚ] (Kv w) ≃+* ℍ[Kv w, algebraMap ℚ (Kv w) a₁, algebraMap ℚ (Kv w) b₁])
    (hφH1 : ∀ c : Kv w, φH ((1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c) =
      c • (1 : ℍ[Kv w, algebraMap ℚ (Kv w) a₁, algebraMap ℚ (Kv w) b₁]))
    (ξ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] (Kv w) → V)
    (hadd : ∀ x y, ξ (x + y) = ξ x + ξ y)
    (hsmul : ∀ (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] (Kv w)) (c : Kv w), ξ (x * (1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c) = c • ξ x)
    (y : ℍ[Kv w, algebraMap ℚ (Kv w) a₁, algebraMap ℚ (Kv w) b₁]) :
    linOfCoords w φH hφH1 ξ hadd hsmul y = ξ (φH.symm y) := rfl

noncomputable def mulVecHom (w : HeightOneSpectrum (𝓞 ℚ)) {N : Type} [Fintype N] [DecidableEq N]
    (f : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) →+* Matrix N N (Kv w)) (e₀ : N → Kv w) :
    ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) →+ (N → Kv w) where
  toFun d := (f d).mulVec e₀
  map_zero' := by simp only [f.map_zero, Matrix.zero_mulVec]
  map_add' x y := by simp only [f.map_add, Matrix.add_mulVec]

theorem mulVecHom_apply (w : HeightOneSpectrum (𝓞 ℚ)) {N : Type} [Fintype N] [DecidableEq N]
    (f : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) →+* Matrix N N (Kv w)) (e₀ : N → Kv w) (d : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) :
    mulVecHom w f e₀ d = (f d).mulVec e₀ := rfl

noncomputable def nrdHom (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b]) :
    ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) →* Kv w where
  toFun y := QuaternionAlgebra.nrd (φ y)
  map_one' := by simp only [φ.map_one, nrd_one']
  map_mul' x y := by simp only [φ.map_mul, nrd_mul']

theorem nrdHom_apply (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w) ≃+* ℍ[Kv w, algebraMap ℚ (Kv w) a, algebraMap ℚ (Kv w) b])
    (y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) : nrdHom w φ y = QuaternionAlgebra.nrd (φ y) := rfl

end RamTransfer

open RamTransfer in
open QuaternionAlgebra CerednikDrinfeld in
set_option maxHeartbeats 3200000 in
theorem solution
    {r rbar : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a₁ b₁ rbar)
    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτc : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ m : ℍ[ℚ, a, b], y * j m = j m * y) ↔ y ∈ Set.range τ)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O)
    (Λ₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hrbw : ((rbar : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) :
    Submodule.localBox R w = Submodule.localBox Λ₁ w := by
  classical
  have hrbP : rbar.Prime := Fact.out
  have hrP : r.Prime := Fact.out
  have hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h =>
    hrr ((RamTransfer.ℓ_eq_of_prime_mem w hrbP hrbw).symm.trans (RamTransfer.ℓ_eq_of_prime_mem w hrP h))

  have hτj : ∀ (x : ℍ[ℚ, a₁, b₁]) (m : ℍ[ℚ, a, b]), τ x * j m = j m * τ x :=
    fun x m => (hτc (τ x)).mpr ⟨x, rfl⟩ m
  obtain ⟨τK, jK, hτK1, hjK1, hτKinj, hcomm, hjKint, hRw⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem
      hH' O hO j τ hτ hτj R hRiff w hrw

  have hdivB : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x := (hB.2 w).mpr (Or.inr hrbw)
  have hdivH : ∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x := (hdef.2.2 w).mpr hrbw

  obtain ⟨φB, hφB⟩ := RamTransfer.exists_coords (a := a) (b := b) w
  obtain ⟨φH, hφH⟩ := RamTransfer.exists_coords (a := a₁) (b := b₁) w
  have hΛw : ∀ y, y ∈ Submodule.localBox Λ w ↔ QuaternionAlgebra.nrd (φB y) ∈ w.adicCompletionIntegers ℚ :=
    fun y => QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ w hdivB φB hφB y
  have hΛ₁w : ∀ x, x ∈ Submodule.localBox Λ₁ w ↔ QuaternionAlgebra.nrd (φH x) ∈ w.adicCompletionIntegers ℚ :=
    fun x => QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ₁ w hdivH φH hφH x
  have hdivD : ∀ d : ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      d ≠ 0 → IsUnit d := by
    intro d hd
    have h := hdivB (φB.symm d) (fun h0 => hd (by simpa using congrArg φB h0))
    simpa using h.map φB

  have hφB1 := RamTransfer.coords_one_tmul' w hφB
  have hφH1 := RamTransfer.coords_one_tmul' w hφH
  obtain ⟨ι, hι⟩ : ∃ ι : ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]
      →ₐ[w.adicCompletion ℚ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ), ∀ d, ι d = jK (φB.symm d) :=
    ⟨RamTransfer.algHomOfCoords w φB hφB1 jK hjK1, fun _ => rfl⟩
  have hιφ : ∀ y, ι (φB y) = jK y := fun y => by rw [hι, φB.symm_apply_apply]
  have hdim : Module.finrank (w.adicCompletion ℚ)
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b] =
        Fintype.card (Fin 2 × Fin 2) := by
    rw [QuaternionAlgebra.finrank_eq_four]; simp

  obtain ⟨e₀, he₀def⟩ : ∃ e : Fin 2 × Fin 2 → w.adicCompletion ℚ, e = Pi.single ((0 : Fin 2), (0 : Fin 2)) 1 := ⟨_, rfl⟩
  have he₀ : e₀ ≠ 0 := by
    intro h; have := congrFun h ((0 : Fin 2), (0 : Fin 2)); simp [he₀def] at this
  have he₀int : ∀ I, e₀ I ∈ w.adicCompletionIntegers ℚ := by
    intro I; by_cases hI : I = ((0 : Fin 2), (0 : Fin 2))
    · subst hI; simp only [he₀def, Pi.single_eq_same]; exact one_mem _
    · simp only [he₀def, Pi.single_eq_of_ne hI]; exact zero_mem _
  obtain ⟨hbij, hcom⟩ :=
    Matrix.bijective_mulVec_and_forall_exists_mulVec_eq_of_forall_isUnit_of_finrank_eq_card hdivD hdim ι e₀ he₀

  have hcomτ : ∀ x d, τK x * ι d = ι d * τK x := fun x d => by rw [hι, hcomm]
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ →
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      ∀ x d, (τK x).mulVec ((ι d).mulVec e₀) = (ι (d * ξ x)).mulVec e₀ :=
    ⟨fun x => (hcom (τK x) (hcomτ x)).choose, fun x => (hcom (τK x) (hcomτ x)).choose_spec⟩
  have hξ0 : ∀ x, (τK x).mulVec e₀ = (ι (ξ x)).mulVec e₀ := fun x => by
    have := hξ x 1; rwa [map_one ι, Matrix.one_mulVec, one_mul] at this
  have huniq : ∀ d d', (ι d).mulVec e₀ = (ι d').mulVec e₀ → d = d' := fun d d' h => hbij.1 h
  have hξ_one : ξ 1 = 1 := huniq _ _ (by rw [← hξ0 1, τK.map_one, map_one ι])
  have hξ_mul : ∀ x y, ξ (x * y) = ξ y * ξ x := fun x y => huniq _ _ (by
    rw [← hξ0 (x * y), τK.map_mul, ← Matrix.mulVec_mulVec, hξ0 y, hξ x (ξ y)])
  have hξ_add : ∀ x y, ξ (x + y) = ξ x + ξ y := fun x y => huniq _ _ (by
    rw [← hξ0 (x + y), τK.map_add, Matrix.add_mulVec, hξ0 x, hξ0 y, map_add ι, Matrix.add_mulVec])
  have hξ_scalar : ∀ c : w.adicCompletion ℚ,
      ξ ((1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c) = c • (1 : ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
        algebraMap ℚ (w.adicCompletion ℚ) b]) := fun c => huniq _ _ (by
    rw [← hξ0, hτK1, map_smul, map_one])
  have hξ_inj : ∀ x y, ξ x = ξ y → x = y := by
    intro x y hxy
    apply hτKinj
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    obtain ⟨d, rfl⟩ := hbij.2 v
    simp only [hξ, hxy]

  have hξ_smul : ∀ (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) (c : w.adicCompletion ℚ),
      ξ (x * (1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c) = c • ξ x := fun x c => huniq _ _ (by
    rw [← hξ0 (x * (1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c), τK.map_mul, hτK1, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul, map_smul ι, Matrix.smul_mulVec, hξ0 x])
  obtain ⟨η, hη⟩ : ∃ η : ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a₁, algebraMap ℚ (w.adicCompletion ℚ) b₁]
      →ₗ[w.adicCompletion ℚ] ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      ∀ y, η y = ξ (φH.symm y) := ⟨RamTransfer.linOfCoords w φH hφH1 ξ hξ_add hξ_smul, fun _ => rfl⟩
  have hη1 : η 1 = 1 := by rw [hη, map_one, hξ_one]
  have hηinj : Function.Injective η := fun y y' h => by
    rw [hη, hη] at h
    exact φH.symm.injective (hξ_inj _ _ h)
  have hηsq : ∀ y, η (y * y) = η y * η y := fun y => by rw [hη, map_mul, hξ_mul, hη]
  have hnrdξ : ∀ x, QuaternionAlgebra.nrd (ξ x) = QuaternionAlgebra.nrd (φH x) := fun x => by
    have := QuaternionAlgebra.nrd_apply_eq_nrd_of_map_one_of_map_mul_self_of_injective η hη1 hηinj hηsq (φH x)
    rwa [hη, φH.symm_apply_apply] at this

  obtain ⟨NB, hNB⟩ : ∃ NB : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →* w.adicCompletion ℚ,
      ∀ y, NB y = QuaternionAlgebra.nrd (φB y) := ⟨RamTransfer.nrdHom w φB, fun _ => rfl⟩
  have hΛw' : ∀ y, y ∈ Submodule.localBox Λ w ↔ NB y ∈ w.adicCompletionIntegers ℚ := fun y => by rw [hNB]; exact hΛw y
  have hNBu : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ, NB u ≠ 0 ∧ NB (↑u⁻¹) = (NB u)⁻¹ := by
    intro u
    have h := NB.map_mul (u : _) (↑u⁻¹ : _)
    rw [Units.mul_inv, NB.map_one] at h
    have h0 : NB u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact one_ne_zero h
    exact ⟨h0, ((mul_eq_one_iff_inv_eq₀ h0).mp h.symm).symm⟩

  have hjKbox : ∀ d ∈ Submodule.localBox Λ w, ∀ I J, jK d I J ∈ w.adicCompletionIntegers ℚ := by
    intro d hd
    refine AddSubgroup.closure_induction (p := fun d _ => ∀ I J, jK d I J ∈ w.adicCompletionIntegers ℚ) ?_ ?_ ?_ ?_ hd
    · rintro d ⟨z, hz, c, hc, rfl⟩; beta_reduce; intro I J; exact hjKint z c (hj ⟨z, hz⟩) hc I J
    · beta_reduce; intro I J; rw [jK.map_zero]; exact zero_mem _
    · intro x y _ _ hx hy; beta_reduce at hx hy ⊢; intro I J; rw [jK.map_add]; exact add_mem (hx I J) (hy I J)
    · intro x _ hx; beta_reduce at hx ⊢; intro I J; rw [jK.map_neg]; exact neg_mem (hx I J)

  obtain ⟨F, hF'⟩ : ∃ F : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →+ (Fin 2 × Fin 2 → w.adicCompletion ℚ),
      ∀ d, F d = (jK d).mulVec e₀ :=
    ⟨RamTransfer.mulVecHom w jK e₀, fun _ => rfl⟩
  obtain ⟨ΛL, hΛL⟩ : ∃ S : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ),
      ∀ d, d ∈ S ↔ ∀ I, ((jK d).mulVec e₀) I ∈ w.adicCompletionIntegers ℚ := by
    refine ⟨(AddSubgroup.pi Set.univ (fun _ => (w.adicCompletionIntegers ℚ).toSubring.toAddSubgroup)).comap F,
      fun d => ?_⟩
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_pi, hF']
    simp only [Set.mem_univ, true_implies, Subring.mem_toAddSubgroup, ValuationSubring.mem_toSubring]
  have h1L : (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ ΛL := by
    rw [hΛL]; intro I; rw [jK.map_one, Matrix.one_mulVec]; exact he₀int I
  have hleft : ∀ d₀ ∈ Submodule.localBox Λ w, ∀ d ∈ ΛL, d₀ * d ∈ ΛL := by
    intro d₀ hd₀ d hd
    rw [hΛL] at hd ⊢
    intro I
    rw [jK.map_mul, ← Matrix.mulVec_mulVec]
    exact (RamTransfer.forall_mulVec_mem w (jK d₀)).1 (hjKbox d₀ hd₀) _ hd I

  have hFsc : ∀ (d : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) (c : w.adicCompletion ℚ),
      (jK (d * (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)).mulVec e₀ = c • (jK d).mulVec e₀ := fun d c => by
    rw [jK.map_mul, hjK1, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul]
  have hF : Function.Bijective (fun d : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ => (jK d).mulVec e₀) := by
    have : (fun d : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ => (jK d).mulVec e₀) = (fun d' => (ι d').mulVec e₀) ∘ φB := by
      funext d; simp only [Function.comp_apply, hιφ]
    rw [this]; exact hbij.comp φB.bijective
  obtain ⟨g, hg⟩ : ∃ g : Fin 2 × Fin 2 → ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
      ∀ I, (jK (g I)).mulVec e₀ = Pi.single I 1 :=
    ⟨fun I => (hF.2 (Pi.single I 1)).choose, fun I => (hF.2 (Pi.single I 1)).choose_spec⟩

  have hexp : ∀ d : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ,
      d = ∑ I, g I * (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((jK d).mulVec e₀) I) := by
    intro d
    apply hF.1
    show (jK d).mulVec e₀ = (jK (∑ I, g I * (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (((jK d).mulVec e₀) I))).mulVec e₀
    rw [← hF' (∑ I, _), map_sum F]
    simp only [hF', hFsc, hg]
    ext J
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  have hvrb : Valued.v ((rbar : ℕ) : w.adicCompletion ℚ) < 1 := RamTransfer.v_natCast_lt_one w hrbP hrbw
  have hrb0 : ((rbar : ℕ) : w.adicCompletion ℚ) ≠ 0 := by
    have : ((rbar : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hrbP.ne_zero
    have h := (map_ne_zero (algebraMap ℚ (w.adicCompletion ℚ))).mpr this
    rwa [map_natCast] at h
  have hg0 : ∀ I, g I ≠ 0 := by
    intro I h
    have h1 := hg I
    rw [h, jK.map_zero, Matrix.zero_mulVec] at h1
    have h2 := congrFun h1 I
    simp at h2
  have hNBg : ∀ I, Valued.v (NB (g I)) ≠ 0 := by
    intro I
    obtain ⟨u, hu⟩ := hdivB (g I) (hg0 I)
    rw [Valuation.ne_zero_iff, ← hu]
    exact (hNBu u).1
  have hcast : ((rbar : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) =
      ((rbar : ℕ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
    exact Algebra.TensorProduct.natCast_def _
  have hNBrb : NB ((rbar : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = ((rbar : ℕ) : w.adicCompletion ℚ) ^ 2 := by
    rw [hcast, hNB, hφB, one_smul, QuaternionAlgebra.nrd_mk]
    simp only [QuaternionAlgebra.re_natCast, QuaternionAlgebra.imI_natCast, QuaternionAlgebra.imJ_natCast,
      QuaternionAlgebra.imK_natCast, map_natCast, map_zero]
    ring
  have hgpow : ∀ I, ∃ m : ℕ, ((rbar : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ^ m * g I ∈ Submodule.localBox Λ w := by
    intro I
    obtain ⟨m, hm⟩ := RamTransfer.exists_mul_pow_le_one hvrb ((Valuation.ne_zero_iff _).mpr hrb0) (hNBg I)
    refine ⟨m, ?_⟩
    rw [hΛw', NB.map_mul, NB.map_pow, hNBrb, ← pow_mul, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
      map_pow, mul_comm]
    exact hm
  obtain ⟨m, hm⟩ : ∃ m : Fin 2 × Fin 2 → ℕ,
      ∀ I, ((rbar : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ^ m I * g I ∈ Submodule.localBox Λ w :=
    ⟨fun I => (hgpow I).choose, fun I => (hgpow I).choose_spec⟩

  have hnatΛ : ∀ k : ℕ, ((rbar : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ^ k ∈ Submodule.localBox Λ w := by
    intro k
    rw [hcast, Algebra.TensorProduct.tmul_pow, one_pow, ← Nat.cast_pow]
    refine RamTransfer.tmul_mem_localBox ?_ w (one_mem _)
    rw [← Nat.smul_one_eq_cast]
    exact Λ.toAddSubmonoid.nsmul_mem hΛ.isOrder.one_mem _
  have hbdd : ∃ n : ℕ, ∀ d ∈ ΛL,
      ((rbar : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ^ n * d ∈ Submodule.localBox Λ w := by
    refine ⟨∑ I, m I, fun d hd => ?_⟩
    rw [hexp d, Finset.mul_sum]
    refine sum_mem fun I _ => ?_
    rw [← mul_assoc]
    have hle : m I ≤ ∑ J, m J := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
    have h1 : ((rbar : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ^ (∑ J, m J) * g I ∈ Submodule.localBox Λ w := by
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact RamTransfer.localBox_mul_mem hΛ.isOrder w (hnatΛ _) (hm I)
    exact RamTransfer.localBox_mul_one_tmul_mem w h1 ((hΛL d).1 hd I)

  obtain ⟨x₀, hx₀L, hx₀u, hgen⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_isUnit_forall_mem_iff_exists_mem_localBox_eq_mul_of_forall_isUnit
      hΛ w hdivB hrbw ΛL ⟨1, h1L, one_ne_zero⟩ hleft hbdd
  obtain ⟨u₀, hu₀⟩ := hx₀u
  have hNBx₀ : NB x₀ ≠ 0 := by rw [← hu₀]; exact (hNBu u₀).1

  have hkey : ∀ (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) (d : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ),
      (jK (d * φB.symm (ξ x))).mulVec e₀ = (τK x).mulVec ((jK d).mulVec e₀) := by
    intro x d
    have h1 : ι (φB d * ξ x) = jK (d * φB.symm (ξ x)) := by
      rw [hι, φB.symm.map_mul, φB.symm_apply_apply]
    rw [← h1, ← hιφ d]
    exact (hξ x (φB d)).symm
  have hNBζ : ∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ, NB (φB.symm (ξ x)) = QuaternionAlgebra.nrd (ξ x) := fun x => by
    rw [hNB, φB.apply_symm_apply]

  refine AddSubgroup.ext fun x => ?_
  rw [hRw x]
  rw [hΛ₁w x]
  rw [← hnrdξ x]
  rw [RamTransfer.forall_mulVec_mem w (τK x)]
  constructor
  · intro hT
    have h1 : x₀ * φB.symm (ξ x) ∈ ΛL := by
      rw [hΛL, hkey]; exact hT _ ((hΛL x₀).1 hx₀L)
    obtain ⟨d', hd', hd'eq⟩ := (hgen _).1 h1
    have h2 : NB (φB.symm (ξ x)) = NB d' := by
      have h3 := congrArg NB hd'eq
      rw [NB.map_mul, NB.map_mul, mul_comm (NB d')] at h3
      exact mul_left_cancel₀ hNBx₀ h3
    rw [← hNBζ, h2]
    exact (hΛw' d').1 hd'
  · intro hn v hv
    obtain ⟨d, rfl⟩ := hF.2 v
    have hdL : d ∈ ΛL := (hΛL d).2 hv
    obtain ⟨d₁, hd₁, rfl⟩ := (hgen d).1 hdL
    rw [← hkey]
    have hc : x₀ * φB.symm (ξ x) * ↑u₀⁻¹ ∈ Submodule.localBox Λ w := by
      rw [hΛw', NB.map_mul, NB.map_mul, (hNBu u₀).2, hu₀, mul_assoc, mul_comm (NB _) (NB x₀)⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hNBx₀, one_mul, hNBζ]
      exact hn
    have heq : d₁ * x₀ * φB.symm (ξ x) = (d₁ * (x₀ * φB.symm (ξ x) * ↑u₀⁻¹)) * x₀ := by
      rw [← hu₀, mul_assoc, mul_assoc, mul_assoc, Units.inv_mul, mul_one, ← mul_assoc]
    rw [heq]
    exact (hΛL _).1 ((hgen _).2 ⟨_, RamTransfer.localBox_mul_mem hΛ.isOrder w hd₁ hc, rfl⟩)

end S_QuaternionAlgebra_localBox_eq_localBox_of_forall_iff_mem_range_of_isMaximalOrder_of_mem_asIdeal
end P2MW
export P2MW.S_QuaternionAlgebra_localBox_eq_localBox_of_forall_iff_mem_range_of_isMaximalOrder_of_mem_asIdeal (solution)
