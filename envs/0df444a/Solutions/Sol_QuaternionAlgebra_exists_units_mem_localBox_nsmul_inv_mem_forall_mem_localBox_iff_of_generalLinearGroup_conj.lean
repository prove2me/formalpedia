-- Prove2me | solution 1 for QuaternionAlgebra.exists_units_mem_localBox_nsmul_inv_mem_forall_mem_localBox_iff_of_generalLinearGroup_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/390ed232-a271-5a62-a91e-ec86d0ca1562

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_units_mem_localBox_nsmul_inv_mem_forall_mem_localBox_iff_of_generalLinearGroup_conj

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField

namespace LocalEndNormal

theorem exists_entry_forall_inv_mul_apply_mem
    {K : Type*} [Field K] (𝒪 : ValuationSubring K) {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (g : GL n K) :
    ∃ i₀ j₀ : n, (g : Matrix n n K) i₀ j₀ ≠ 0 ∧
      ∀ i j, ((g : Matrix n n K) i₀ j₀)⁻¹ * (g : Matrix n n K) i j ∈ 𝒪 := by
  classical
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (n × n))
      (fun ij : n × n => 𝒪.valuation ((g : Matrix n n K) ij.1 ij.2)) Finset.univ_nonempty
  have hc : (g : Matrix n n K) i₀ j₀ ≠ 0 := by
    intro hc
    apply Units.ne_zero g
    ext i j
    have hij := hmax ⟨i, j⟩ (Finset.mem_univ _)
    simp only [hc, map_zero, le_zero_iff, map_eq_zero] at hij
    simpa using hij
  refine ⟨i₀, j₀, hc, fun i j => ?_⟩
  obtain ⟨a, ha⟩ := (𝒪.valuation_le_iff _ _).mp (hmax ⟨i, j⟩ (Finset.mem_univ _))
  simp only at ha
  rw [← ha, ← mul_assoc, mul_comm _ (a : K), mul_assoc, inv_mul_cancel₀ hc, mul_one]
  exact a.2

theorem conj_single_apply {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n K) (k l p q : n) (c : K) :
    (A * Matrix.single k l c * B) p q = A p k * c * B l q := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.single_mul_apply_same, mul_assoc]
  · intro s _ hs
    rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hs, mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem exists_generalLinearGroup_mem_nsmul_inv_mem_conj_eq
    {K : Type*} [Field K] (𝒪 : ValuationSubring K) {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (H : GL n K) (N : ℕ)
    (hN : ∀ X : Matrix n n K, (∀ i j, X i j ∈ 𝒪) →
      ∀ i j, (N • (((H⁻¹ : GL n K) : Matrix n n K) * X * (H : Matrix n n K))) i j ∈ 𝒪) :
    ∃ M : GL n K, (∀ i j, (M : Matrix n n K) i j ∈ 𝒪) ∧
      (∀ i j, (N • ((M⁻¹ : GL n K) : Matrix n n K)) i j ∈ 𝒪) ∧
      ∀ Y : Matrix n n K, ((M⁻¹ : GL n K) : Matrix n n K) * Y * (M : Matrix n n K) =
        ((H⁻¹ : GL n K) : Matrix n n K) * Y * (H : Matrix n n K) := by
  obtain ⟨i₀, j₀, hc, hdiv⟩ := exists_entry_forall_inv_mul_apply_mem 𝒪 H

  let M : GL n K :=
    ⟨((H : Matrix n n K) i₀ j₀)⁻¹ • (H : Matrix n n K),
      (H : Matrix n n K) i₀ j₀ • ((H⁻¹ : GL n K) : Matrix n n K),
      by rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, Units.mul_inv],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, Units.inv_mul]⟩
  have hM : (M : Matrix n n K) = ((H : Matrix n n K) i₀ j₀)⁻¹ • (H : Matrix n n K) := rfl
  have hM' : ((M⁻¹ : GL n K) : Matrix n n K) =
      (H : Matrix n n K) i₀ j₀ • ((H⁻¹ : GL n K) : Matrix n n K) := rfl
  refine ⟨M, ?_, ?_, ?_⟩
  · intro i j
    rw [hM, Matrix.smul_apply, smul_eq_mul]
    exact hdiv i j
  · intro i j
    rw [hM', Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

    have h1 := hN (Matrix.single j i₀ 1) (fun k l => by
      show (if j = k ∧ i₀ = l then (1 : K) else 0) ∈ 𝒪
      split_ifs
      exacts [one_mem _, zero_mem _]) i j₀
    rwa [Matrix.smul_apply, conj_single_apply, mul_one] at h1
  · intro Y
    rw [hM, hM', smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul, inv_mul_cancel₀ hc,
      one_smul]

end LocalEndNormal

open LocalEndNormal in
theorem solution
    {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (h₁ : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox Λ₁ v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    (H : GL (Fin 2) (v.adicCompletion ℚ))
    (h₂ : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox Λ₂ v ↔
        ∀ i j, (((H⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) *
          φ x * (H : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ)
    (N : ℕ) (hN : ∀ x ∈ Submodule.localBox Λ₁ v, N • x ∈ Submodule.localBox Λ₂ v) :
    ∃ m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      (m : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ₁ v ∧
      N • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈
        Submodule.localBox Λ₁ v ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox Λ₂ v ↔
          ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x * m ∈
            Submodule.localBox Λ₁ v := by
  have hφN : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, φ (N • y) = N • φ y := map_nsmul φ N

  have hN' : ∀ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) →
      ∀ i j, (N • (((H⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) * X *
        (H : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))) i j ∈ v.adicCompletionIntegers ℚ := by
    intro X hX i j
    have hx : φ.symm X ∈ Submodule.localBox Λ₁ v :=
      (h₁ _).mpr fun k l => by rw [RingEquiv.apply_symm_apply]; exact hX k l
    have := (h₂ _).mp (hN _ hx) i j
    rwa [hφN, RingEquiv.apply_symm_apply, Matrix.mul_smul, Matrix.smul_mul] at this

  obtain ⟨M, hM, hNM, hconj⟩ :=
    exists_generalLinearGroup_mem_nsmul_inv_mem_conj_eq (v.adicCompletionIntegers ℚ) H N hN'

  let m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
    Units.map (φ.symm : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) ≃+* _).toRingHom.toMonoidHom M
  have hm : (m : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
      φ.symm (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := rfl
  have hm' : ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) =
      φ.symm ((M⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := rfl
  refine ⟨m, ?_, ?_, ?_⟩
  ·
    rw [h₁, hm, RingEquiv.apply_symm_apply]; exact hM
  ·
    rw [h₁, hm', hφN, RingEquiv.apply_symm_apply]; exact hNM
  ·
    intro x
    rw [h₂, h₁, hm, hm', map_mul φ, map_mul φ, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, hconj]

end S_QuaternionAlgebra_exists_units_mem_localBox_nsmul_inv_mem_forall_mem_localBox_iff_of_generalLinearGroup_conj
end P2MW
export P2MW.S_QuaternionAlgebra_exists_units_mem_localBox_nsmul_inv_mem_forall_mem_localBox_iff_of_generalLinearGroup_conj (solution)
