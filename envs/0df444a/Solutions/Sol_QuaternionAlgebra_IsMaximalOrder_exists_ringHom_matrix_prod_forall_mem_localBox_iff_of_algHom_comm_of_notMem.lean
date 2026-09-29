-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f75fe538-50a5-5d2d-b6c0-92f472022705

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_ringEquiv_mem_localBox_iff_of_notMem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace LocalMatrixFrame

section generic

variable {D : Type} [Ring D] [Algebra ℚ D] {L : Type} [CommRing L] [Algebra ℚ L]
  (φ : D ⊗[ℚ] L ≃+* Matrix (Fin 2) (Fin 2) L)

noncomputable def f₀ : Matrix (Fin 2) (Fin 2) D →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) L :=
  (Matrix.compRingEquiv (Fin 2) (Fin 2) L).toRingHom.comp
    ((φ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom).mapMatrix)

theorem f₀_apply (m : Matrix (Fin 2) (Fin 2) D) (i s l t : Fin 2) :
    f₀ φ m (i, s) (l, t) = φ (m i l ⊗ₜ[ℚ] (1 : L)) s t := rfl

noncomputable def Θ : Matrix (Fin 2) (Fin 2) D ⊗[ℚ] L →ₐ[ℚ] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) L :=
  Algebra.TensorProduct.lift (f₀ φ).toRatAlgHom
    (IsScalarTower.toAlgHom ℚ L (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) L))
    (fun x y => Algebra.commute_algebraMap_right y _)

theorem Θ_tmul (m : Matrix (Fin 2) (Fin 2) D) (c : L) : Θ φ (m ⊗ₜ[ℚ] c) = c • f₀ φ m := by
  rw [Θ, Algebra.TensorProduct.lift_tmul]
  change f₀ φ m * algebraMap L (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) L) c = c • f₀ φ m
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]

variable (hφ : ∀ r : L, φ ((1 : D) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) L))

include hφ in

theorem Θ_apply (y : Matrix (Fin 2) (Fin 2) D ⊗[ℚ] L) (i s l t : Fin 2) :
    Θ φ y (i, s) (l, t) = φ ((Matrix.entryLinearMap ℚ D i l).rTensor L y) s t := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, Matrix.zero_apply, Matrix.zero_apply]
  | tmul m c =>
    rw [Θ_tmul, Matrix.smul_apply, f₀_apply, LinearMap.rTensor_tmul, Matrix.entryLinearMap_apply]
    have hmc : m i l ⊗ₜ[ℚ] c = (m i l ⊗ₜ[ℚ] (1 : L)) * ((1 : D) ⊗ₜ[ℚ] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hmc, map_mul, hφ, mul_smul_comm, mul_one, Matrix.smul_apply]
  | add x y hx hy =>
    rw [map_add, Matrix.add_apply, hx, hy, map_add, map_add, Matrix.add_apply]

theorem eq_sum_single_rTensor (y : Matrix (Fin 2) (Fin 2) D ⊗[ℚ] L) :
    y = ∑ i, ∑ l, (Matrix.singleLinearMap ℚ i l).rTensor L ((Matrix.entryLinearMap ℚ D i l).rTensor L y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finset.sum_const_zero]
  | tmul m c =>
    simp_rw [LinearMap.rTensor_tmul, Matrix.entryLinearMap_apply, Matrix.singleLinearMap_apply,
      ← TensorProduct.sum_tmul]
    rw [← Matrix.matrix_eq_sum_single]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_add, map_add]

theorem eq_zero_of_forall_entry (y : Matrix (Fin 2) (Fin 2) D ⊗[ℚ] L)
    (h : ∀ i l, (Matrix.entryLinearMap ℚ D i l).rTensor L y = 0) : y = 0 := by
  rw [eq_sum_single_rTensor y]
  simp only [h, map_zero, Finset.sum_const_zero]

variable {A : Type} [Ring A] [Algebra ℚ A]

noncomputable def ψK (ψ : A →ₐ[ℚ] Matrix (Fin 2) (Fin 2) D) :
    A ⊗[ℚ] L →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) L :=
  ((Θ φ).comp (Algebra.TensorProduct.map ψ (AlgHom.id ℚ L))).toRingHom

theorem ψK_def (ψ : A →ₐ[ℚ] Matrix (Fin 2) (Fin 2) D) (x : A ⊗[ℚ] L) :
    ψK φ ψ x = Θ φ (Algebra.TensorProduct.map ψ (AlgHom.id ℚ L) x) := rfl

theorem map_eq_rTensor (ψ : A →ₐ[ℚ] Matrix (Fin 2) (Fin 2) D) (x : A ⊗[ℚ] L) :
    Algebra.TensorProduct.map ψ (AlgHom.id ℚ L) x = ψ.toLinearMap.rTensor L x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z c => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul, AlgHom.id_apply, AlgHom.toLinearMap_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem ψK_one_tmul (ψ : A →ₐ[ℚ] Matrix (Fin 2) (Fin 2) D) (c : L) :
    ψK φ ψ ((1 : A) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) L) := by
  rw [ψK_def, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, Θ_tmul, map_one]

include hφ in
theorem ψK_apply (ψ : A →ₐ[ℚ] Matrix (Fin 2) (Fin 2) D) (x : A ⊗[ℚ] L) (i s l t : Fin 2) :
    ψK φ ψ x (i, s) (l, t) =
      φ (((Matrix.entryLinearMap ℚ D i l ∘ₗ ψ.toLinearMap).rTensor L) x) s t := by
  rw [ψK_def, Θ_apply φ hφ, map_eq_rTensor, LinearMap.rTensor_comp, LinearMap.comp_apply]

include hφ in
theorem ψK_injective (ψ : A →ₐ[ℚ] Matrix (Fin 2) (Fin 2) D) (hψ : Function.Injective ψ) :
    Function.Injective (ψK φ ψ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : ∀ i l, (Matrix.entryLinearMap ℚ D i l).rTensor L (ψ.toLinearMap.rTensor L x) = 0 := by
    intro i l
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← φ.map_eq_zero_iff]
    ext s t
    rw [← ψK_apply φ hφ, hx, Matrix.zero_apply, Matrix.zero_apply]
  have h2 : ψ.toLinearMap.rTensor L x = 0 := eq_zero_of_forall_entry _ h1
  have h3 := Module.Flat.rTensor_preserves_injective_linearMap (M := L) ψ.toLinearMap hψ
  exact h3 (by rw [h2, map_zero])

theorem ψK_comm (τ : A →ₐ[ℚ] Matrix (Fin 2) (Fin 2) D) {B : Type} [Ring B] [Algebra ℚ B]
    (j : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) D) (hτj : ∀ (x : A) (m : B), τ x * j m = j m * τ x)
    (x : A ⊗[ℚ] L) (y : B ⊗[ℚ] L) : ψK φ τ x * ψK φ j y = ψK φ j y * ψK φ τ x := by
  rw [ψK_def, ψK_def, ← map_mul, ← map_mul]
  congr 1
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_mul, mul_zero]
  | tmul z c =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, zero_mul, mul_zero]
    | tmul m c' =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, AlgHom.id_apply, AlgHom.id_apply, hτj, mul_comm c c']
    | add y₁ y₂ h₁ h₂ => rw [map_add, mul_add, add_mul, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => rw [map_add, add_mul, mul_add, h₁, h₂]

end generic

section local_frame

variable {c d : ℚ} (w : HeightOneSpectrum (𝓞 ℚ))
  (φ : ℍ[ℚ, c, d] ⊗[ℚ] w.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
  (hφ : ∀ r : w.adicCompletion ℚ,
    φ ((1 : ℍ[ℚ, c, d]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)))
  (O : Submodule ℤ ℍ[ℚ, c, d])
  (hφO : ∀ x : ℍ[ℚ, c, d] ⊗[ℚ] w.adicCompletion ℚ,
    x ∈ Submodule.localBox O w ↔ ∀ i j, φ x i j ∈ w.adicCompletionIntegers ℚ)

include hφ hφO in
theorem ψK_integral {B : Type} [Ring B] [Algebra ℚ B] (j : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (m : B) (c' : w.adicCompletion ℚ) (hm : ∀ i l : Fin 2, j m i l ∈ O)
    (hc' : c' ∈ w.adicCompletionIntegers ℚ) (I J : Fin 2 × Fin 2) :
    ψK φ j (m ⊗ₜ[ℚ] c') I J ∈ w.adicCompletionIntegers ℚ := by
  obtain ⟨i, s⟩ := I
  obtain ⟨l, t⟩ := J
  rw [ψK_apply φ hφ, LinearMap.rTensor_tmul, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    Matrix.entryLinearMap_apply]
  refine (hφO _).mp ?_ s t
  exact AddSubgroup.subset_closure ⟨j m i l, hm i l, c', hc', rfl⟩

include hφ hφO in
theorem ψK_mem_iff {a₁ b₁ : ℚ} (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    (hτ : Function.Injective τ) (hO : IsOrder O)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O)
    (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) :
    x ∈ Submodule.localBox R w ↔ ∀ I J : Fin 2 × Fin 2, ψK φ τ x I J ∈ w.adicCompletionIntegers ℚ := by
  rw [IsOrder.mem_localBox_iff_forall_rTensor_entryLinearMap_comp_mem_localBox τ hτ O hO R hRiff w x]
  constructor
  · rintro h ⟨i, s⟩ ⟨l, t⟩
    rw [ψK_apply φ hφ]
    exact (hφO _).mp (h i l) s t
  · intro h i l
    refine (hφO _).mpr fun s t => ?_
    rw [← ψK_apply φ hφ]
    exact h (i, s) (l, t)

end local_frame

theorem main {r : ℕ} [Fact r.Prime]
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    {a b : ℚ} (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    {a₁ b₁ : ℚ} (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτj : ∀ (x : ℍ[ℚ, a₁, b₁]) (m : ℍ[ℚ, a, b]), τ x * j m = j m * τ x)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    ∃ (τK : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))
      (jK : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ)),
      (∀ c' : w.adicCompletion ℚ, τK ((1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c') = c' • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))) ∧
      (∀ c' : w.adicCompletion ℚ, jK ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c') = c' • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))) ∧
      Function.Injective τK ∧
      (∀ (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) (y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ), τK x * jK y = jK y * τK x) ∧
      (∀ (m : ℍ[ℚ, a, b]) (c' : w.adicCompletion ℚ), (∀ i l : Fin 2, j m i l ∈ O) → c' ∈ w.adicCompletionIntegers ℚ →
        ∀ I J : Fin 2 × Fin 2, jK (m ⊗ₜ[ℚ] c') I J ∈ w.adicCompletionIntegers ℚ) ∧
      (∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R w ↔ ∀ I J : Fin 2 × Fin 2, τK x I J ∈ w.adicCompletionIntegers ℚ) := by
  have hE : IsEichlerOrder O 1 :=
    ⟨O, O, hO, hO, (inf_idem O).symm, AddSubgroup.relIndex_self _⟩
  have h1w : ((1 : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    rw [Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
  obtain ⟨φ, hφ, hφO⟩ := IsEichlerOrder.exists_ringEquiv_mem_localBox_iff_of_notMem hH' hE w hrw h1w
  refine ⟨ψK φ τ, ψK φ j, fun c' => ψK_one_tmul φ τ c', fun c' => ψK_one_tmul φ j c',
    ψK_injective φ hφ τ hτ, fun x y => ψK_comm φ τ j hτj x y,
    fun m c' hm hc' I J => ψK_integral w φ hφ O hφO j m c' hm hc' I J,
    fun x => ψK_mem_iff w φ hφ O hφO τ hτ hO.isOrder R hRiff x⟩

end LocalMatrixFrame

theorem solution
    {r : ℕ} [Fact r.Prime]
    {c d : ℚ} (hH' : IsDefiniteRamifiedExactlyAt c d r)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O)
    {a b : ℚ} (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
    {a₁ b₁ : ℚ} (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτj : ∀ (x : ℍ[ℚ, a₁, b₁]) (m : ℍ[ℚ, a, b]), τ x * j m = j m * τ x)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hrw : ((r : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    ∃ (τK : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))
      (jK : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ →+* Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ)),
      (∀ c' : w.adicCompletion ℚ, τK ((1 : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] c') = c' • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))) ∧
      (∀ c' : w.adicCompletion ℚ, jK ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c') = c' • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (w.adicCompletion ℚ))) ∧
      Function.Injective τK ∧
      (∀ (x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ) (y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ), τK x * jK y = jK y * τK x) ∧
      (∀ (m : ℍ[ℚ, a, b]) (c' : w.adicCompletion ℚ), (∀ i l : Fin 2, j m i l ∈ O) → c' ∈ w.adicCompletionIntegers ℚ →
        ∀ I J : Fin 2 × Fin 2, jK (m ⊗ₜ[ℚ] c') I J ∈ w.adicCompletionIntegers ℚ) ∧
      (∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] w.adicCompletion ℚ,
        x ∈ Submodule.localBox R w ↔ ∀ I J : Fin 2 × Fin 2, τK x I J ∈ w.adicCompletionIntegers ℚ) := by
  exact LocalMatrixFrame.main hH' O hO j τ hτ hτj R hRiff w hrw

end S_QuaternionAlgebra_IsMaximalOrder_exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ringHom_matrix_prod_forall_mem_localBox_iff_of_algHom_comm_of_notMem (solution)
