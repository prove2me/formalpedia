-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.phiM_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:35:20.375965+00:00
-- url     : https://prove2.me/submissions/3c0d0452-cefd-43bd-a127-2f1cc4031be8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMoments
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecALogLower
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiDecayCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phi_decay_core
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
private lemma posDef_exp_of_hermitian {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = Y) :
    (NormedSpace.exp Y).PosDef := by
  have hB : (NormedSpace.exp ((2 : ℂ)⁻¹ • Y))ᴴ = NormedSpace.exp ((2 : ℂ)⁻¹ • Y) := by
    rw [← Matrix.exp_conjTranspose]
    congr 1
    simp [hY]
  have hBB : NormedSpace.exp Y =
      (NormedSpace.exp ((2 : ℂ)⁻¹ • Y))ᴴ * 1 * NormedSpace.exp ((2 : ℂ)⁻¹ • Y) := by
    rw [hB, Matrix.mul_one, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
    norm_num
  rw [hBB]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_exp _))
private lemma lead_exp_pos_of_hermitian {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = Y) (i : Fin n) :
    0 < lead ((i : ℕ) + 1) (NormedSpace.exp Y) := by
  have hle : (i : ℕ) + 1 ≤ n := i.isLt
  rw [lead, dif_pos hle]
  exact ((posDef_exp_of_hermitian hY).submatrix (Fin.castLE_injective hle)).det_pos
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) (hμ : IsMu lam μ) (hlam : IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (hq : 1 ≤ q0 ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y) :
    (PhiM μ (NormedSpace.exp Y)).re ≤
      Real.exp (-(h / 8) * min (hs Y) (Real.sqrt (hs Y) / Real.sqrt (2 * q0 ε))) := by
  have hYh : Yᴴ = Y := by
    obtain ⟨h1, h2⟩ := hY
    have h1' : Yᴴ * Jm ε + Jm ε * Y = 0 := h1
    have hJ : Jm ε * Jm ε = 1 := by
      rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      split_ifs <;> norm_num
    have h3 : Yᴴ * Jm ε = Y * Jm ε := by
      rw [h2]
      exact eq_neg_of_add_eq_zero_left h1'
    calc Yᴴ = Yᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = Y * Jm ε * Jm ε := by rw [h3]
      _ = Y := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  have hpos : ∀ i : Fin n, 0 < lead ((i : ℕ) + 1) (NormedSpace.exp Y) := fun i => lead_exp_pos_of_hermitian hYh i
  have hν : Antitone fun i => (μ i : ℝ) := by
    intro a b hab
    show (μ b : ℝ) ≤ μ a
    rw [hμ a, hμ b]
    have h1 := hlam.1.antitone hab
    have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_le.2 (Fin.le_def.1 hab)
    simp only [rho]
    linarith
  have hg : ∀ a b : Fin n, ε a ≠ ε b → b < a → h ≤ (μ b : ℝ) - μ a := by
    intro a b hne hba
    have h1 := hgap a b hne
    have h2 := hlam.1 hba
    rw [abs_of_neg (by linarith)] at h1
    rw [hμ a, hμ b]
    have h3 : ((b : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_le.2 (Fin.le_def.1 hba.le)
    simp only [rho]
    linarith
  have hcore := phi_decay_core (fun i => (μ i : ℝ)) hν hg hq hY
  refine le_trans (le_of_eq ?_) hcore
  have hfac : ∀ i : Fin n, lead ((i : ℕ) + 1) (NormedSpace.exp Y) ^ (-(μ i - muNext μ i)) =
      (((lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re ^
        (-((μ i : ℝ) - nuNext (fun j => (μ j : ℝ)) i)) : ℝ) : ℂ) := by
    intro i
    have him : (lead ((i : ℕ) + 1) (NormedSpace.exp Y)).im = 0 := by
      have := (Complex.lt_def.1 (hpos i)).2
      simpa using this.symm
    have hre : lead ((i : ℕ) + 1) (NormedSpace.exp Y) =
        ((lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    have hexp : (-((μ i : ℝ) - nuNext (fun j => (μ j : ℝ)) i)) = ((-(μ i - muNext μ i) : ℤ) : ℝ) := by
      simp only [nuNext, muNext]
      split_ifs <;> push_cast <;> ring
    rw [hexp, Real.rpow_intCast, Complex.ofReal_zpow, ← hre]
  simp only [PhiM, phiReal]
  rw [Finset.prod_congr rfl fun i _ => hfac i, ← Complex.ofReal_prod, Complex.ofReal_re]
end ReciprocityTheory.ChartRestriction.DS.S7
