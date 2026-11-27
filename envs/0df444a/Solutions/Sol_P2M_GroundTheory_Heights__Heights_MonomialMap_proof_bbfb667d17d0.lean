-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MonomialMap_proof_bbfb667d17d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:13.332299+00:00
-- url     : https://prove2.me/submissions/974e137c-1524-4ff5-b049-eff2c1fc5024

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_mul_874c88085c03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_pow_2c1d068278d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_cast_040b4045ef54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_mul_7d1beff2f443
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_pow_c43df090b05d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n}
namespace GroundTheory.Heights₂.Heights.MonomialMap
theorem _root_.solution : MonomialMap.Statement := by
  intro ι _ _ n P L _ q m r hr g h hg hgs hh hhs
  refine ⟨fun s hs ↦ ?_, fun s₁ s₂ heq ↦ ?_⟩
  · let A := ((L.pow (q * m + r)).mul (L.pow (q - r))).mul ((HermLine.standard n).pow (m + 1))
    let B := ((L.pow q).mul (HermLine.standard n)).pow (m + 1)
    have hdeg : A.deg = B.deg := by
      funext k
      simp only [A, B, HermLine.mul, HermLine.pow, HermLine.standard, Pi.add_apply, Pi.smul_apply,
]
      simp only [nsmul_eq_mul]
      push_cast [Nat.cast_sub hr.le]
      ring
    have hmet : ∀ z, A.metric z = B.metric z := by
      intro z
      simp only [A, B, HermLine.mul, HermLine.pow]
      have hexp : q * m + r + (q - r) = q * (m + 1) := by
        rw [Nat.mul_succ]; omega
      rw [← pow_add, hexp, mul_pow, pow_mul]
    have h₁ := supNormLE_mul (L.pow (q * m + r)) (L.pow (q - r)) s (g.pow (q - r)) hs
      (supNormLE_pow L g hgs (q - r))
    have h₂ := supNormLE_pow (HermLine.standard n) h hhs (m + 1)
    have hA := supNormLE_mul ((L.pow (q * m + r)).mul (L.pow (q - r)))
      ((HermLine.standard n).pow (m + 1)) (s.mul (g.pow (q - r))) (h.pow (m + 1)) h₁ h₂
    have hz : (0 : ℝ) + ((q - r : ℕ) : ℝ) * 0 + ((m + 1 : ℕ) : ℝ) * 0 = 0 := by simp
    rw [hz] at hA
    refine ⟨((s.mul (g.pow (q - r))).mul (h.pow (m + 1))).cast hdeg, ?_, supNormLE_cast A B hdeg hmet _ hA⟩
    change ((s.mul (g.pow (q - r))).mul (h.pow (m + 1))).toFun = _
    rw [toFun_mul, toFun_mul, toFun_pow, toFun_pow]
  · have hne : g.toFun ^ (q - r) * h.toFun ^ (m + 1) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ hh)
    rw [mul_assoc, mul_assoc] at heq
    exact mul_right_cancel₀ hne heq
end GroundTheory.Heights₂.Heights.MonomialMap
