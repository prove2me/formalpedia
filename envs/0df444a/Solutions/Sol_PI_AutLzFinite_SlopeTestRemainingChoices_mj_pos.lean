-- Prove2me | solution 1 for PI.AutLzFinite.SlopeTestRemainingChoices.mj_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:40.615846+00:00
-- url     : https://prove2.me/submissions/6a34fa1c-ccc4-4983-ace8-5b315a0e5b88

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MjSmulRight
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_tau_normSq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_herm_swap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)
variable {S}
variable (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) (τ : E →+* ℂ)
  (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
  (hzz : (τ (S.hT z z)).re < 0)
  (hpos : ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
include hstar hPX hzP hzz hpos
namespace PI.AutLzFinite.SlopeTestRemainingChoices
theorem _root_.solution (y : S.V) (hy : y ∈ P) :
    0 ≤ (τ (mj S z y y)).re ∧ ((τ (mj S z y y)).re = 0 → y ∈ X) := by
  have hzz0 : S.hT z z ≠ 0 := by
    intro h; rw [h, map_zero] at hzz; simp at hzz
  set c := S.hT z y / S.hT z z with hc
  set y0 := y - c • z with hy0def
  have h1 : S.hT z y0 = 0 := by
    simp only [y0, map_sub, LinearMap.map_smul, smul_eq_mul, c]
    field_simp; ring
  have hy0 : y0 ∈ P := P.sub_mem hy (P.smul_mem c hzP)
  have h2 : S.hT y0 z = 0 := by rw [herm_swap, h1, star_zero]
  have hm : mj S z y y = S.hT y0 y0 - star c * c * S.hT z z := by
    have hyy : y = y0 + c • z := by simp [y0]
    rw [hyy]
    simp only [mj, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, h1, h2, starRingEnd_apply, RingHom.id_apply]
    field_simp
    ring
  have hq : 0 ≤ (τ (S.hT y0 y0)).re ∧ ((τ (S.hT y0 y0)).re = 0 → y0 ∈ X) := by
    by_cases hX : y0 ∈ X
    · have : S.hT y0 y0 = 0 := hPX y0 hX y0 hy0
      simp [this, hX]
    · have := hpos y0 hy0 h1 hX
      exact ⟨this.le, fun h => absurd h this.ne'⟩
  have hτ : (τ (mj S z y y)).re = (τ (S.hT y0 y0)).re - Complex.normSq (τ c) * (τ (S.hT z z)).re := by
    rw [hm, map_sub, map_mul, tau_normSq (hstar τ), Complex.sub_re, Complex.re_ofReal_mul]
  have hns := Complex.normSq_nonneg (τ c)
  refine ⟨by rw [hτ]; nlinarith, fun h0 => ?_⟩
  rw [hτ] at h0
  have hA : Complex.normSq (τ c) * (τ (S.hT z z)).re = 0 := by nlinarith
  have hB : (τ (S.hT y0 y0)).re = 0 := by nlinarith
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hA with h | h
    · exact τ.injective (by rw [Complex.normSq_eq_zero.mp h, map_zero])
    · exact absurd h hzz.ne
  have : y = y0 := by simp [y0, hc0]
  rw [this]; exact hq.2 hB
end PI.AutLzFinite.SlopeTestRemainingChoices
