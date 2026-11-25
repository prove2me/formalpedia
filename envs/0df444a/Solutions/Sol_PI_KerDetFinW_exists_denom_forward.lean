-- Prove2me | solution 1 for PI.KerDetFinW.exists_denom_forward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:23.264524+00:00
-- url     : https://prove2.me/submissions/855a2689-09c6-43b8-96c0-54316cafb019

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
import Theorems.Thm_PI_KerDetFinW_exists_nat_mul_mem_int_fam


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : Fin 4 → E, (∀ a, x a ∈ I) → ∀ w,
      (N : K) * g₀ x w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨α, hα, hαI⟩ := I.isFractional
  have hα0 : algebraMap (𝓞 E) E α ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hα
      ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 h)
  let b := RingOfIntegers.basis E
  let φ : Fin 4 → Fin 4 × n → (E →ₗ[K] K) := fun a w =>
    LinearMap.proj w ∘ₗ (g₀ : (Fin 4 → E) →ₗ[K] (Fin 4 × n → K)) ∘ₗ
      LinearMap.single K (fun _ : Fin 4 => E) a
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_int_fam
    (fun q : Fin 4 × Module.Free.ChooseBasisIndex ℤ (𝓞 E) × (Fin 4 × n) =>
      φ q.1 q.2.2 ((algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E (b q.2.1)))
  refine ⟨N, hN0, fun x hx w => ?_⟩
  have hxs : g₀ x w = ∑ a, φ a w (x a) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, Finset.sum_apply]
    rfl
  have hterm : ∀ a, (N : K) * φ a w (x a) ∈ (algebraMap (𝓞 K) K).range := by
    intro a
    obtain ⟨z, hz⟩ := hαI (x a) (FractionalIdeal.mem_coe.2 (hx a))
    have hxa : x a = ∑ i, (b.repr z i) • ((algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E (b i)) := by
      have h1 : x a = (algebraMap (𝓞 E) E α)⁻¹ * algebraMap (𝓞 E) E z := by
        rw [hz, Algebra.smul_def, inv_mul_cancel_left₀ hα0]
      rw [h1]
      conv_lhs => rw [← b.sum_repr z]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, mul_smul_comm]
    rw [hxa, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_zsmul, mul_smul_comm]
    exact zsmul_mem (hN (a, i, w)) _
  rw [hxs, Finset.mul_sum]
  exact Subring.sum_mem _ fun a _ => hterm a
end PI.KerDetFinW
