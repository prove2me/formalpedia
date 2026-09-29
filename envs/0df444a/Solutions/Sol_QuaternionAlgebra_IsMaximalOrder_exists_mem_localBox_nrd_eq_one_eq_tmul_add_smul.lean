-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2ba8e85f-7251-5dfd-b8cf-71d2ce55ca9f

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_BaseChange
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_nrd_eq_det_of_ringEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_mem_localBox_iff_of_isIndefiniteRamifiedExactlyAt_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

noncomputable section

namespace LocalSlTarget

variable {a b : ℚ}

def coord (v : HeightOneSpectrum (𝓞 ℚ)) :
    ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b] :=
  (QuaternionAlgebra.baseChangeRight (R := ℚ) (S := v.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    rfl (map_zero _) rfl).toRingEquiv

theorem coord_tmul (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ) :
    coord v (z ⊗ₜ[ℚ] r) = ⟨r * algebraMap ℚ _ z.re, r * algebraMap ℚ _ z.imI, r * algebraMap ℚ _ z.imJ,
      r * algebraMap ℚ _ z.imK⟩ := by
  show QuaternionAlgebra.baseChangeRight _ _ _ (z ⊗ₜ[ℚ] r) = _
  rw [QuaternionAlgebra.baseChangeRight_tmul]

theorem coord_formula (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ) :
    coord v (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
      algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
        ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) := by
  rw [coord_tmul]; ext <;> simp [smul_eq_mul]

theorem nrd_coord_tmul_one (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    nrd (coord v (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) = algebraMap ℚ (v.adicCompletion ℚ) (nrd z) := by
  rw [coord_tmul, nrd_mk, nrd]
  simp only [one_mul, map_sub, map_add, map_mul, map_pow]

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem ratSmul_eq_mul (v : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    r • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) r) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z t =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

end LocalSlTarget

end

open LocalSlTarget in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hqv : (q : 𝓞 ℚ) ∉ v.asIdeal) (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal)
    {N : ℕ} (hNv : (N : 𝓞 ℚ) ∈ v.asIdeal)
    (c : ℍ[ℚ, a, b]) (hc : c ∈ Λ) (k : ℤ) (hnrd : nrd c = 1 + (N : ℚ) * (k : ℚ)) :
    ∃ s ∈ Submodule.localBox Λ v,
      (∀ ψ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
          ψ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re,
            algebraMap ℚ (v.adicCompletion ℚ) z.imI, algebraMap ℚ (v.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
              ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a,
                algebraMap ℚ (v.adicCompletion ℚ) b])) →
        nrd (ψ s) = 1) ∧
      ∃ z ∈ Submodule.localBox Λ v, s = c ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) + (N : ℚ) • z := by
  classical
  obtain ⟨φ, hφr, hφΛ⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_mem_localBox_iff_of_isIndefiniteRamifiedExactlyAt_of_prime
      hB hΛ v hqv hq'v
  have hdetnrd : ∀ x, nrd (coord v x) = (φ x).det := fun x =>
    QuaternionAlgebra.nrd_eq_det_of_ringEquiv v φ hφr (coord v) (coord_formula v) x
  have hcmem : c ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
    AddSubgroup.subset_closure ⟨c, hc, 1, one_mem _, rfl⟩
  have hCint : ∀ i j, φ (c ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ := (hφΛ _).1 hcmem

  have hvN : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (N : ℚ)) < 1 := by
    rw [valued_algebraMap, show ((N : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (N : 𝓞 ℚ) from (map_natCast _ _).symm,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 hNv
  have hvk : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (k : ℚ)) ≤ 1 := by
    rw [valued_algebraMap, show ((k : ℤ) : ℚ) = algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ) from (map_intCast _ _).symm,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _
  have hkO : algebraMap ℚ (v.adicCompletion ℚ) (k : ℚ) ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hvk
  set aN : v.adicCompletion ℚ := algebraMap ℚ (v.adicCompletion ℚ) (N : ℚ) with haN
  set ak : v.adicCompletion ℚ := algebraMap ℚ (v.adicCompletion ℚ) (k : ℚ) with hak
  set d : v.adicCompletion ℚ := 1 + aN * ak with hd
  have hd' : algebraMap ℚ (v.adicCompletion ℚ) (nrd c) = d := by
    rw [hnrd, map_add, map_one, map_mul]
  have hvNk : Valued.v (aN * ak) < 1 := by
    rw [map_mul]
    calc Valued.v aN * Valued.v ak ≤ Valued.v aN * 1 := mul_le_mul_right hvk _
      _ = Valued.v aN := mul_one _
      _ < 1 := hvN
  have hvd : Valued.v d = 1 := by rw [hd]; exact Valuation.map_one_add_of_lt _ hvNk
  have hd0 : d ≠ 0 := fun h => by rw [h, map_zero] at hvd; exact zero_ne_one hvd
  have hdinvO : d⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hvd, inv_one]

  set C : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := φ (c ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) with hC
  have hCdet : C.det = d := by rw [hC, ← hdetnrd, nrd_coord_tmul_one, hd']
  set F : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![-ak * d⁻¹, 0] with hF
  set D : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := Matrix.diagonal ![d⁻¹, 1] with hD
  have hDeq : D = 1 + aN • F := by
    have h00 : d⁻¹ = 1 + aN * (-ak * d⁻¹) := by
      field_simp
      rw [hd]; ring
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [hD, hF, Matrix.diagonal, Matrix.one_apply]
    linear_combination h00
  have hSdet : (C * D).det = 1 := by
    rw [Matrix.det_mul, hCdet, hD, Matrix.det_diagonal]
    simp [Fin.prod_univ_two, hd0]
  have hSint : ∀ i j, (C * D) i j ∈ v.adicCompletionIntegers ℚ := by
    intro i j
    rw [hD, Matrix.mul_diagonal]
    fin_cases j
    · simpa using mul_mem (hCint i 0) hdinvO
    · simpa using hCint i 1
  have hFint : ∀ i j, (C * F) i j ∈ v.adicCompletionIntegers ℚ := by
    intro i j
    rw [hF, Matrix.mul_diagonal]
    fin_cases j
    · simpa using mul_mem (hCint i 0) (mul_mem (neg_mem hkO) hdinvO)
    · simp
  set s := φ.symm (C * D) with hs
  have hφs : φ s = C * D := φ.apply_symm_apply _
  have hsΛ : s ∈ Submodule.localBox Λ v := (hφΛ s).2 (by rw [hφs]; exact hSint)
  set z := φ.symm (C * F) with hz
  have hφz : φ z = C * F := φ.apply_symm_apply _
  have hzΛ : z ∈ Submodule.localBox Λ v := (hφΛ z).2 (by rw [hφz]; exact hFint)
  refine ⟨s, hsΛ, fun ψ hψ => ?_, z, hzΛ, ?_⟩
  · rw [QuaternionAlgebra.nrd_eq_det_of_ringEquiv v φ hφr ψ hψ s, hφs, hSdet]
  · apply φ.injective
    rw [φ.map_add, hφs, ratSmul_eq_mul v (N : ℚ) z, φ.map_mul, hφr, hφz, smul_mul_assoc, one_mul, ← hC, hDeq,
      mul_add, mul_one, Matrix.mul_smul]

end S_QuaternionAlgebra_IsMaximalOrder_exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_mem_localBox_nrd_eq_one_eq_tmul_add_smul (solution)
