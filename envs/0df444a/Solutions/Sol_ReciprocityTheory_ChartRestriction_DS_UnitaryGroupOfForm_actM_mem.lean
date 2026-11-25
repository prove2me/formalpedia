-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm.actM_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:27:58.176398+00:00
-- url     : https://prove2.me/submissions/0d53f84a-5e12-497e-9c6d-de464f5047e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IrredA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_jj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitaryGroupOfForm_jj_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_Jconj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_PolarDecomposition_polar_exp_neg_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
variable {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
theorem _root_.solution (hD : IsDerivedOn ε σ D E) (T : Submodule ℂ H) (hTc : IsClosed (T : Set H))
    (hTG : ∀ g ∈ UJset ε, ∀ x ∈ T, σ g x ∈ T) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X)
    (v : D) (hv : (v : H) ∈ T) : ((actM E X v : D) : H) ∈ T := by
  have hXh : Xᴴ = -(Jm ε * X * Jm ε) := by
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, jj, Matrix.mul_one]
      _ = -(Jm ε * X) * Jm ε := by rw [eq_neg_of_add_eq_zero_left hX]
      _ = -(Jm ε * X * Jm ε) := by rw [Matrix.neg_mul]
  have hexp : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε := by
    intro t
    have hg : (NormedSpace.exp ((t : ℂ) • X))ᴴ = Jm ε * NormedSpace.exp (-((t : ℂ) • X)) * Jm ε := by
      rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hXh, ← PolarDecomposition.polar_exp_Jconj]
      congr 1
      rw [Complex.star_def, Complex.conj_ofReal]
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
    rw [hg]
    simp only [Matrix.mul_assoc]
    rw [jj_mul, PolarDecomposition.polar_exp_neg_mul, Matrix.mul_one]
  have hlim := (hD.deriv X hX v).tendsto_slope_zero
  refine hTc.mem_of_tendsto hlim (Filter.Eventually.of_forall fun t => ?_)
  exact T.smul_of_tower_mem _ (T.sub_mem (hTG _ (hexp _) _ hv) (hTG _ (hexp _) _ hv))
end ReciprocityTheory.ChartRestriction.DS.UnitaryGroupOfForm
