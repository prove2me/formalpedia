-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_squarefree_of_not_dvd_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/d0fdd5ca-c8c2-5354-9f3f-85de5789677a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_conjByFiniteIdele_eq_and_conjByFiniteIdele_eq_of_squarefree
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_eq_finiteIdeleDiagonal_mul_mul_of_ne
import Theorems.Thm_Submodule_conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_squarefree_of_not_dvd_of_ne
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star"

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

namespace P2mKcTypeNumberOneAway

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem localBoxUnits_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBoxUnits Λ v ⊆ Submodule.localBoxUnits Λ' v := by
  intro u hu
  exact ⟨localBox_mono h v hu.1, localBox_mono h v hu.2⟩

theorem finiteIdeleStabilizer_mono {a b : ℚ} {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ : IsOrder Λ) (hΛ' : IsOrder Λ') (h : Λ ≤ Λ') :
    Submodule.finiteIdeleStabilizer Λ ≤ Submodule.finiteIdeleStabilizer Λ' := by
  intro u hu
  rw [IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ] at hu
  rw [IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ' hΛ']
  exact fun v => localBoxUnits_mono h v (hu v)

end P2mKcTypeNumberOneAway

open P2mKcTypeNumberOneAway in
theorem solution
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] (hN : Squarefree N)
    (Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛ' : IsMaximalOrder Λ')
    {R R' : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N) (hR' : IsEichlerOrder R' N)
    (hRΛ : R ≤ Λ) (hR'Λ' : R' ≤ Λ')
    (r : ℕ) [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ (γ : (ℍ[ℚ, a, b])ˣ) (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.conjByFiniteIdele R' (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * g) = R ∧
      Submodule.conjByFiniteIdele Λ' (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] γ * g) = Λ := by

  obtain ⟨y, hyR, hyΛ⟩ :=
    IsEichlerOrder.exists_conjByFiniteIdele_eq_and_conjByFiniteIdele_eq_of_squarefree q' hdef hN Λ Λ' hΛ hΛ' hR hR'
      hRΛ hR'Λ'

  obtain ⟨γ, g, u, hu, hg, hy⟩ :=
    IsEichlerOrder.exists_eq_finiteIdeleDiagonal_mul_mul_of_ne q' hdef hR' r hrq' v hv y
  have hR'o : IsOrder R' := hR'.isOrder
  have hΛ'o : IsOrder Λ' := hΛ'.isOrder

  have huΛ : u ∈ Submodule.finiteIdeleStabilizer Λ' := finiteIdeleStabilizer_mono hR'o hΛ'o hR'Λ' hu
  refine ⟨γ, g, hg, ?_, ?_⟩
  · rw [← Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer R' hR'o.one_mem
      (fun x y hx hy => hR'o.mul_mem hx hy) _ u hu, ← hy, hyR]
  · rw [← Submodule.conjByFiniteIdele_mul_eq_of_mem_finiteIdeleStabilizer Λ' hΛ'o.one_mem
      (fun x y hx hy => hΛ'o.mul_mem hx hy) _ u huΛ, ← hy, hyΛ]

end S_QuaternionAlgebra_IsEichlerOrder_exists_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_squarefree_of_not_dvd_of_ne
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_conjByFiniteIdele_finiteIdeleDiagonal_mul_eq_of_squarefree_of_not_dvd_of_ne (solution)
