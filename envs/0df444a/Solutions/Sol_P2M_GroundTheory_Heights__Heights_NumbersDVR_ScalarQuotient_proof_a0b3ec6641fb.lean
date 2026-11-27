-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_proof_a0b3ec6641fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:05:47.198044+00:00
-- url     : https://prove2.me/submissions/515a23e6-de6f-40c4-8a0b-4a0f83040271

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PScalarQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_isVerticalDivisor_const_b17ca793c6be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ScalarQuotient_pairNum_const_f21d509d558c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_psum_e0d98b62ae64
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_psum_537ba6a9a7c8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ScalarQuotient
theorem _root_.solution (hFI : FlagIndependence.Statement) : ScalarQuotient.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hmod N E _ _ B B' n u hlat w w' x x' f g hpair k Gs hGs
    Q hQ
  have : (pointIdeal O y).IsPrime := hmod.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ pointIdeal O y := by
    intro a ha hmem
    have h1 : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := hmem
    rw [hmod.noTorsion] at h1
    exact ha (Ideal.mem_bot.mp h1)
  have hγ : (u : O) * ϖ ^ n ≠ 0 := mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ.ne_zero)
  have hγΩ : algebraMap O Ω ((u : O) * ϖ ^ n) ≠ 0 := by
    intro h0
    apply hC _ hγ
    change pointConeMap O y (C _) = 0
    rw [pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0, map_zero]
  set γ : Ω := algebraMap O Ω ((u : O) * ϖ ^ n) with hγdef
  let w₂ : Module.Basis (Fin N) Ω E := w.unitsSMul fun _ => Units.mk0 γ hγΩ
  have hrep : ∀ (z : E) (j : Fin N), w₂.repr (γ • z) j = w.repr z j := by
    intro z j
    simp [w₂, Module.Basis.repr_unitsSMul, Units.smul_def, hγΩ]
  have hw₂ : ∀ i, w₂ i = γ • w i := by
    intro i
    simp [w₂, Module.Basis.unitsSMul_apply, Units.smul_def]
  have hpair₂ : IsFlagPair ϖ y B B' w w₂ x x (fun _ => C ((u : O) * ϖ ^ n)) (fun _ => 1) := by
    refine ⟨hpair.flag, ⟨fun c hc i => ?_⟩, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
    · rw [← hpair.flag.graded c hc i]
      ext s
      constructor
      · rintro ⟨v, hv, hz, rfl⟩
        obtain ⟨z₀, hz₀, rfl⟩ := (hlat c hc v).mp hv
        exact ⟨z₀, hz₀, fun j hj => by rw [← hrep]; exact hz j hj, (hrep z₀ i).symm⟩
      · rintro ⟨z₀, hz₀, hz, rfl⟩
        exact ⟨γ • z₀, (hlat c hc _).mpr ⟨z₀, hz₀, rfl⟩, fun j hj => by rw [hrep]; exact hz j hj,
          hrep z₀ i⟩
    · rw [hw₂, map_smul, Module.Basis.repr_self]
      simp [hij.ne]
    · rw [sub_self]
      exact ScalarQuotient.isVerticalDivisor_const _ ϖ u n (hC _ hγ)
    · rw [hw₂, map_smul, Module.Basis.repr_self]
      simp [hγdef]
  have hsame : SameGenericFibre ϖ B B' := by
    intro c hc
    refine ⟨fun v hv => ⟨n, ?_⟩, fun v hv => ⟨0, ?_⟩⟩
    · have h1 : γ • v ∈ B'.lat c := (hlat c hc _).mpr ⟨v, hv, rfl⟩
      have h2 := B'.stable c (algebraMap O Ω ((u⁻¹ : Oˣ) : O)) (Subalgebra.algebraMap_mem _ _) _ h1
      convert h2 using 1
      rw [hγdef, smul_smul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow]
    · obtain ⟨z₀, hz₀, rfl⟩ := (hlat c hc v).mp hv
      rw [pow_zero, one_smul]
      exact B.stable c _ (Subalgebra.algebraMap_mem _ _) _ hz₀
  rw [hFI O ϖ hϖ Ω K ι y d hmod N E B B' hsame w w' w w₂ x x' x x f g _ _ hpair hpair₂ k
    (psum (Fin N) ℤ k) (isHomogeneous_psum N k) (psum_isSymmetric _ _ k) Gs (psumExpansion N k)
    hGs (isPairExpansion_psum N k) Q hQ]
  exact ScalarQuotient.pairNum_const _ hC hϖ.ne_zero u n x k Q
end ScalarQuotient
end GroundTheory.Heights₂.Heights.NumbersDVR
