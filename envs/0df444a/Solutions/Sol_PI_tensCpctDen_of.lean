-- Prove2me | solution 1 for PI.tensCpctDen_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:17:50.928531+00:00
-- url     : https://prove2.me/submissions/1cc611ac-f4cd-4b13-a0e1-b98030b84e20

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactTensorDensity_TensCpctDenOf
import Theorems.Thm_PI_TensCpctDenWork_coordL_tmul
import Theorems.Thm_PI_TensCpctDenWork_exists_nat_mul_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct PI.TensCpctDenWork
namespace PI
theorem _root_.solution (hA : PI.AdCpctDen) : PI.TensCpctDen := by
  intro F E _ _ _ _ _
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  intro C hC
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  set b := Module.finBasis F E with hbdef
  have hcont : ∀ i, Continuous (coordL (R := FiniteAdeleRing (𝓞 F) F) (b.coord i)) := fun i =>
    IsModuleTopology.continuous_of_linearMap _
  choose Nf hNf0 hNf using fun i => hA F _ ((hC.image (hcont i)))
  choose Db hDb0 hDb using fun i => exists_nat_mul_isIntegral (b i)
  set N0 : ℕ := ∏ i, Nf i with hN0
  set D0 : ℕ := ∏ i, Db i with hD0
  have hN0pos : 0 < N0 := Finset.prod_pos fun i _ => hNf0 i
  have hD0pos : 0 < D0 := Finset.prod_pos fun i _ => hDb0 i
  refine ⟨N0 * D0, Nat.mul_pos hN0pos hD0pos, fun e he => ?_⟩
  have hφ : ∀ i, IsIntegral ℤ ((N0 : F) * b.coord i e) := by
    intro i
    have hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.coord i e) ∈
        coordL (R := FiniteAdeleRing (𝓞 F) F) (b.coord i) '' C := by
      refine ⟨_, he, ?_⟩
      show coordL (b.coord i) ((e : E) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) = _
      rw [coordL_tmul, Algebra.smul_def, mul_one]
    have h1 := hNf i (b.coord i e) hmem
    have hsplit : (N0 : F) = ((∏ j ∈ Finset.univ.erase i, Nf j : ℕ) : F) * (Nf i : F) := by
      rw [hN0, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      push_cast
      ring
    rw [hsplit, mul_assoc]
    exact (isIntegral_natCast _).mul h1
  have hb : ∀ i, IsIntegral ℤ ((D0 : E) * b i) := by
    intro i
    have hsplit : (D0 : E) = ((∏ j ∈ Finset.univ.erase i, Db j : ℕ) : E) * (Db i : E) := by
      rw [hD0, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      push_cast
      ring
    rw [hsplit, mul_assoc]
    exact (isIntegral_natCast _).mul (hDb i)
  have he_sum : ((N0 * D0 : ℕ) : E) * e =
      ∑ i, algebraMap F E ((N0 : F) * b.coord i e) * ((D0 : E) * b i) := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Module.Basis.coord_apply]
    push_cast
    ring
  rw [he_sum]
  refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (hb i)
  exact (hφ i).map (IsScalarTower.toAlgHom ℤ F E)
end PI
