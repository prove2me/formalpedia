-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/55909370-60aa-53b3-92bd-4aff00fdf19c

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsOrder_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_exists_ne_neg_one_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem solution
    {a b : ℚ} (hind : 0 < a ∨ 0 < b) (hD : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (y : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hy : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd
          (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
            (y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) = 1) :
    ∃ (β : (ℍ[ℚ, a, b])ˣ) (u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      QuaternionAlgebra.nrd (β : ℍ[ℚ, a, b]) = 1 ∧
      u ∈ Submodule.finiteIdeleStabilizer O ∧
      y = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β * u := by

  have ha : a ≠ 0 := by
    intro ha0
    have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := fun h => by
      have := congrArg QuaternionAlgebra.imI h; simp at this
    obtain ⟨u, hu⟩ := hD _ hi
    have hsq : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 1, 0, 0⟩ = 0 := by
      ext <;> simp [ha0]
    have : (u * u : (ℍ[ℚ, a, b])ˣ) = (u * u) := rfl
    have h0 : ((u * u : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 0 := by rw [Units.val_mul, hu, hsq]
    exact (u * u).ne_zero h0
  have hb : b ≠ 0 := by
    intro hb0
    have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ≠ 0 := fun h => by
      have := congrArg QuaternionAlgebra.imJ h; simp at this
    obtain ⟨u, hu⟩ := hD _ hj
    have hsq : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) * ⟨0, 0, 1, 0⟩ = 0 := by
      ext <;> simp [hb0]
    have h0 : ((u * u : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 0 := by rw [Units.val_mul, hu, hsq]
    exact (u * u).ne_zero h0
  refine QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_of_forall_exists_nrd_eq_one_tmul_eq_add_smul
    ha hb hO ?_ y hy
  intro w hsplit s' hs'
  obtain ⟨s, hs1, hs2, hsn, hsapp⟩ :=
    QuaternionAlgebra.IsOrder.exists_ne_neg_one_forall_exists_nrd_eq_one_tmul_eq_add_smul_of_forall_isUnit hind hD hO w hsplit
  exact QuaternionAlgebra.IsOrder.forall_exists_nrd_eq_one_tmul_eq_add_smul_of_exists_ne_neg_one_of_ne_zero
    ha hb hO w hsplit ⟨s, hs1, hs2, hsn, hsapp⟩ s' hs'

end S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit (solution)
