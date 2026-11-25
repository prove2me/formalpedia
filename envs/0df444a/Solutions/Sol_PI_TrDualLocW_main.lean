-- Prove2me | solution 1 for PI.TrDualLocW.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:08.287801+00:00
-- url     : https://prove2.me/submissions/00bc6653-e362-4be4-8cdd-8e63044609f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralNatCast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_TraceOfKer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_T2SpaceOfNonarchimedeanLocalField
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_Imports
import Theorems.Thm_P2M_PI_CntNotIntW_t2Space_of_nonarchimedeanLocalField__ad798eed03bb
import Theorems.Thm_PI_CntNotIntW_piMap_one_tmul
import Theorems.Thm_PI_CntNotIntW_trace_of_ker
import Theorems.Thm_PI_CntNotIntW_trace_one_tmul
import Theorems.Thm_PI_TrDualLocW_BA_repr_natPow_mul
import Theorems.Thm_PI_TrDualLocW_mem_S
import Theorems.Thm_PI_TrDualLocW_mem_S_of_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.TrDualLocW
open NumberField ValuativeRel PI.CntNotIntW
open scoped TensorProduct
namespace PI.TrDualLocW
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime] {Fp : Type} [Field Fp]
    [CharZero Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp]
    (hc : Continuous (algebraMap ℚ_[ℓ] Fp)) (hfin : FiniteDimensional ℚ_[ℓ] Fp) (ι : K →+* Fp)
    (hsurj : Function.Surjective (piMap K ℓ Fp ι)) (t : K)
    (ht : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) (c : Fp) (hcO : c ∈ 𝒪[Fp]) :
    ‖Algebra.trace ℚ_[ℓ] Fp (c * ι t)‖ ≤ 1 := by
  let π := piMap K ℓ Fp ι
  have hπ1 : ∀ y : K, π (1 ⊗ₜ y) = ι y := piMap_one_tmul K ℓ Fp ι
  let b := NumberField.integralBasis K
  let bd := (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) b
  have hdb : ∀ i j, Algebra.trace ℚ K (bd i * b j) = if j = i then 1 else 0 := by
    intro i j
    have := (Algebra.traceForm ℚ K).apply_dualBasis_left (traceForm_nondegenerate ℚ K) b i j
    rwa [Algebra.traceForm_apply] at this
  let BD := Algebra.TensorProduct.basis ℚ_[ℓ] bd
  have hBD : ∀ i, BD i = 1 ⊗ₜ bd i := fun i => Algebra.TensorProduct.basis_apply bd i
  have : FiniteDimensional ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) := Module.Finite.of_basis BD
  have htb : ∀ i j, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) ((1 ⊗ₜ bd i) * (1 ⊗ₜ b j)) =
      if j = i then 1 else 0 := by
    intro i j
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul, hdb]
    split_ifs <;> simp
  have hnd : ∀ γ : ℚ_[ℓ] ⊗[ℚ] K,
      (∀ j, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (γ * (1 ⊗ₜ b j)) = 0) → γ = 0 := by
    intro γ hγ
    have hexp := BD.sum_repr γ
    have hc0 : ∀ j, BD.repr γ j = 0 := by
      intro j
      have h := hγ j
      rw [← hexp, Finset.sum_mul, map_sum] at h
      simpa only [smul_mul_assoc, map_smul, hBD, htb, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true] using h
    rw [← hexp]
    simp [hc0]
  let φ : ℚ_[ℓ] ⊗[ℚ] K →ₗ[ℚ_[ℓ]] ℚ_[ℓ] := (Algebra.trace ℚ_[ℓ] Fp).comp π.toLinearMap
  have hφ : ∀ x, φ x = Algebra.trace ℚ_[ℓ] Fp (π x) := fun x => rfl
  let β : ℚ_[ℓ] ⊗[ℚ] K := ∑ i, φ (1 ⊗ₜ b i) • (1 ⊗ₜ bd i)
  have hβ : ∀ x, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (β * x) = φ x := by
    have hL : (Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K)).comp (LinearMap.mulLeft ℚ_[ℓ] β) = φ := by
      apply (BA K ℓ).ext
      intro j
      rw [BA_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      have htb' : ∀ i, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) ((1 ⊗ₜ bd i) * (1 ⊗ₜ integralBasis K j)) =
          if j = i then 1 else 0 := fun i => htb i j
      simp only [β, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, htb', smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl
    intro x
    exact congrArg (fun L => L x) hL
  have hker : ∀ x, π x = 0 → β * x = 0 := by
    intro x hx
    apply hnd
    intro j
    rw [mul_assoc, hβ, hφ, map_mul π, hx, zero_mul, map_zero]
  have htr : ∀ x, Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (β * x) =
      Algebra.trace ℚ_[ℓ] Fp (π β * π x) := by
    intro x
    rw [trace_of_ker π hsurj (β * x), map_mul]
    intro y hy
    rw [mul_comm β x, mul_assoc, hker y hy, mul_zero]
  have hπβ : π β = 1 := by
    by_contra hne
    have hd0 : π β - 1 ≠ 0 := sub_ne_zero.2 hne
    obtain ⟨x, hx⟩ := hsurj (π β - 1)⁻¹
    have e1 : Algebra.trace ℚ_[ℓ] Fp ((π β - 1) * π x) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← htr, hβ, hφ, sub_self]
    rw [hx, mul_inv_cancel₀ hd0, ← map_one (algebraMap ℚ_[ℓ] Fp), Algebra.trace_algebraMap, nsmul_eq_mul,
      mul_one] at e1
    exact (Nat.cast_ne_zero.2 Module.finrank_pos.ne') e1
  have hidem : β * β = β := by
    have h0 := hker (β - 1) (by rw [map_sub, hπβ, map_one, sub_self])
    rwa [mul_sub, mul_one, sub_eq_zero] at h0
  obtain ⟨g, hg⟩ := π.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  have hg' : ∀ x, π (g x) = x := fun x => LinearMap.congr_fun hg x
  let σ : Fp →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] K := (LinearMap.mulLeft ℚ_[ℓ] β) ∘ₗ g
  have hσ : ∀ x, σ x = β * g x := fun x => rfl
  have hσpow : ∀ (x : Fp) (n : ℕ), σ x ^ (n + 1) = σ (x ^ (n + 1)) := by
    intro x n
    rw [hσ, hσ, mul_pow, IsIdempotentElem.pow_succ_eq n hidem]
    have h0 := hker (g x ^ (n + 1) - g (x ^ (n + 1))) (by rw [map_sub, map_pow, hg', hg', sub_self])
    rwa [mul_sub, sub_eq_zero] at h0

  haveI : ContinuousSMul ℚ_[ℓ] Fp := continuousSMul_of_algebraMap ℚ_[ℓ] Fp hc
  haveI : T2Space Fp := t2Space_of_nonarchimedeanLocalField' Fp
  let F : Fp → (Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℚ_[ℓ]) := fun x i => (BA K ℓ).repr (σ x) i
  have hF : Continuous F := by
    refine continuous_pi fun i => ?_
    exact (((BA K ℓ).coord i).comp σ).continuous_of_finiteDimensional
  have hK : IsCompact (𝒪[Fp] : Set Fp) := isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[Fp]))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  obtain ⟨D, hD⟩ := pow_unbounded_of_one_lt C hℓ1
  have hbound : ∀ x ∈ 𝒪[Fp], (ℓ : ℚ_[ℓ] ⊗[ℚ] K) ^ D * σ x ∈ S K ℓ := by
    intro x hx
    rw [mem_S]
    intro i
    rw [BA_repr_natPow_mul, PadicInt.mem_subring_iff, norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hxi : ‖(BA K ℓ).repr (σ x) i‖ ≤ C := (norm_le_pi_norm (F x) i).trans (hC x hx)
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ D := pow_pos (by linarith) D
    rw [inv_mul_le_one₀ hpos]
    linarith
  have hy : σ c ∈ S K ℓ := by
    refine mem_S_of_pow (σ c) D fun n => ?_
    cases n with
    | zero =>
      rw [pow_zero, mul_one]
      exact Subring.pow_mem _ (natCast_mem _ ℓ) D
    | succ k =>
      rw [hσpow]
      exact hbound _ (pow_mem hcO _)

  have etr : Algebra.trace ℚ_[ℓ] Fp (c * ι t) =
      Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (σ c * (1 ⊗ₜ t)) := by
    rw [hσ, mul_assoc, hβ, hφ, map_mul π, hg', hπ1]
  have e : Algebra.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] K) (σ c * (1 ⊗ₜ t)) =
      ∑ i, (BA K ℓ).repr (σ c) i * algebraMap ℚ ℚ_[ℓ] (Algebra.trace ℚ K (integralBasis K i * t)) := by
    conv_lhs => rw [← (BA K ℓ).sum_repr (σ c)]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, BA_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul,
      smul_eq_mul]
  rw [etr, e, ← PadicInt.mem_subring_iff]
  refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ (mem_S.1 hy i) ?_
  obtain ⟨z, hz⟩ := ht (RingOfIntegers.basis K i)
  rw [integralBasis_apply, mul_comm, hz, map_intCast]
  exact intCast_mem _ z
end PI.TrDualLocW
