-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_sum_FY__2d9eaf88065a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:30:56.43626+00:00
-- url     : https://prove2.me/submissions/54c0cb7e-dbe4-4ffd-a8be-4f84c33442de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_FY_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsA_sum_bilin_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_toMK_inv_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_casL_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_phiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lhol_lhol_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ)
    {z : Matrix (Fin n) (Fin n) ℂ} (k : KG ε) (hz : toMK k⁻¹ * z * toMK k ∈ OmegaSet n) :
    ∑ a, ∑ b, FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z)) =
      ((casVal lam : ℝ) : ℂ) • (PhiM μ (toMK k⁻¹ * z * toMK k) • (T.op k * projW T * T.op k⁻¹)) := by
  have huv : toMK k⁻¹ * toMK k = 1 := by
    rw [Ps1.toMK_inv_eq, ← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem k.2.1
  have hvu : toMK k * toMK k⁻¹ = 1 := by
    rw [Ps1.toMK_inv_eq, ← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem k.2.1
  have hvu' : ∀ A : Matrix (Fin n) (Fin n) ℂ, toMK k * (toMK k⁻¹ * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hvu, Matrix.one_mul]
  have hF := fun Y : Matrix (Fin n) (Fin n) ℂ => (FY_facts T μ Y k hz).2
  simp only [hF, Equiv.apply_symm_apply, ← Finset.sum_smul]
  rw [smul_smul]
  congr 1
  set zq := toMK k⁻¹ * z * toMK k with hzq
  set D := fderiv ℂ (Ps1.PhiP μ) (Matrix.of.symm zq) with hD
  set D2 := fderiv ℂ (fderiv ℂ (Ps1.PhiP μ)) (Matrix.of.symm zq) with hD2
  have hDadd : ∀ a b : Matrix (Fin n) (Fin n) ℂ,
      D (Matrix.of.symm (a + b)) = D (Matrix.of.symm a) + D (Matrix.of.symm b) := fun a b =>
    D.map_add (Matrix.of.symm a) (Matrix.of.symm b)
  have hDsmul : ∀ (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ),
      D (Matrix.of.symm (c • a)) = c * D (Matrix.of.symm a) := fun c a =>
    D.map_smul c (Matrix.of.symm a)
  have hD2add1 : ∀ (a b : Matrix (Fin n) (Fin n) ℂ) (y : 𝕄),
      D2 (Matrix.of.symm (a + b)) y = D2 (Matrix.of.symm a) y + D2 (Matrix.of.symm b) y := fun a b y =>
    congrArg (fun L : 𝕄 →L[ℂ] ℂ => L y) (D2.map_add (Matrix.of.symm a) (Matrix.of.symm b))
  have hD2smul1 : ∀ (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ) (y : 𝕄),
      D2 (Matrix.of.symm (c • a)) y = c * D2 (Matrix.of.symm a) y := fun c a y =>
    congrArg (fun L : 𝕄 →L[ℂ] ℂ => L y) (D2.map_smul c (Matrix.of.symm a))
  have hD2add2 : ∀ (x : 𝕄) (a b : Matrix (Fin n) (Fin n) ℂ),
      D2 x (Matrix.of.symm (a + b)) = D2 x (Matrix.of.symm a) + D2 x (Matrix.of.symm b) := fun x a b =>
    (D2 x).map_add (Matrix.of.symm a) (Matrix.of.symm b)
  have hD2smul2 : ∀ (x : 𝕄) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ),
      D2 x (Matrix.of.symm (c • a)) = c * D2 x (Matrix.of.symm a) := fun x c a =>
    (D2 x).map_smul c (Matrix.of.symm a)
  let B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun X Y => D (Matrix.of.symm (Y * X * zq)) +
        D2 (Matrix.of.symm (X * zq)) (Matrix.of.symm (Y * zq)))
      (fun X X' Y => by
        simp only [Matrix.mul_add, Matrix.add_mul]
        rw [hDadd, hD2add1]
        ring)
      (fun c X Y => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
        rw [hDsmul, hD2smul1]
        ring)
      (fun X Y Y' => by
        simp only [Matrix.mul_add, Matrix.add_mul]
        rw [hDadd, hD2add2]
        ring)
      (fun c X Y => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
        rw [hDsmul, hD2smul2]
        ring)
  have hB : ∀ X Y, B X Y = D (Matrix.of.symm (Y * X * zq)) +
      D2 (Matrix.of.symm (X * zq)) (Matrix.of.symm (Y * zq)) := fun X Y => rfl
  have hterm : ∀ a b : Fin n,
      D (Matrix.of.symm (toMK k⁻¹ * Matrix.single b a 1 * (Matrix.single a b 1 * z) * toMK k)) +
        D2 (Matrix.of.symm (toMK k⁻¹ * (Matrix.single a b 1 * z) * toMK k))
          (Matrix.of.symm (toMK k⁻¹ * Matrix.single b a 1 * z * toMK k)) =
      B (toMK k⁻¹ * Matrix.single a b 1 * toMK k) (toMK k⁻¹ * Matrix.single b a 1 * toMK k) := by
    intro a b
    rw [hB, hzq]
    simp only [Matrix.mul_assoc, hvu']
  have hLL : ∀ a b : Fin n, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) zq =
      D (Matrix.of.symm (Matrix.single b a 1 * (Matrix.single a b 1 * zq))) +
        D2 (Matrix.of.symm (Matrix.single a b 1 * zq)) (Matrix.of.symm (Matrix.single b a 1 * zq)) :=
    fun a b => lhol_lhol_eq (contDiffAt_phiM μ hz) _ _
  calc ∑ a, ∑ b, (D (Matrix.of.symm (toMK k⁻¹ * Matrix.single b a 1 * (Matrix.single a b 1 * z) * toMK k)) +
        D2 (Matrix.of.symm (toMK k⁻¹ * (Matrix.single a b 1 * z) * toMK k))
          (Matrix.of.symm (toMK k⁻¹ * Matrix.single b a 1 * z * toMK k)))
      = ∑ a, ∑ b, B (toMK k⁻¹ * Matrix.single a b 1 * toMK k) (toMK k⁻¹ * Matrix.single b a 1 * toMK k) := by
        simp only [hterm]
    _ = ∑ a, ∑ b, B (Matrix.single a b 1) (Matrix.single b a 1) := CasPsA.sum_bilin_conj B _ _ huv
    _ = ∑ a, ∑ b, Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (PhiM μ)) zq := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hLL, hB, Matrix.mul_assoc]
    _ = casL (PhiM μ) zq := rfl
    _ = ((casVal lam : ℝ) : ℂ) * PhiM μ zq := casL_phiM μ lam hμ hz
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
