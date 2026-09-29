-- Prove2me | solution 1 for QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/34881b88-8507-5947-90d7-37052ac58dad

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder
import Theorems.Thm_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val QuaternionAlgebra.ClassSet.map_mk"

set_option autoImplicit false

open scoped Quaternion TensorProduct
open QuaternionAlgebra IsDedekindDomain NumberField

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {c d : ℚ} (hH : IsDefiniteRamifiedExactlyAt c d q)
    (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsMaximalOrder O) :
    ∃ (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d])
      (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O),
      ∀ (F : Type) [Field F] [CharP F q] (χ : ↥O → F),
        (∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, χ ⟨1, h⟩ = 1) →
        (∀ x y : ↥O, χ (x + y) = χ x + χ y) →
        (∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
          χ ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = χ x * χ y) →
        ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          χ ⟨j (m : ℍ[ℚ, a, b]) 0 0, hj m 0 0⟩ + χ ⟨j (m : ℍ[ℚ, a, b]) 1 1, hj m 1 1⟩ = (n : F) := by

  have hBq : ∀ v : HeightOneSpectrum (𝓞 ℚ), (q : 𝓞 ℚ) ∈ v.asIdeal →
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x :=
    fun v hv => (hB.2 v).2 (Or.inl hv)

  obtain ⟨j₀, -, hj₀⟩ :=
    QuaternionAlgebra.exists_algHom_matrix_injective_forall_apply_mem_of_isOrder_of_isMaximalOrder q hH hBq Λ hΛ.1 O hO

  obtain ⟨j, γ, γ', -, -, -, hj, hspec⟩ :=
    QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_of_apply_mem_of_isIndefiniteRamifiedExactlyAt
      hB Λ hΛ hH O hO j₀ hj₀
  exact ⟨j, hj, hspec⟩

end S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_exists_algHom_matrix_apply_mem_and_trace_of_isMaximalOrder_of_isDefiniteRamifiedExactlyAt (solution)
