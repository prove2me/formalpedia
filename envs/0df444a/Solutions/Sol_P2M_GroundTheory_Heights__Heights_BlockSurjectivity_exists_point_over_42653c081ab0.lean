-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_point_over_42653c081ab0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:34:26.282638+00:00
-- url     : https://prove2.me/submissions/d4633253-bd95-49a8-b563-b9124b311c4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_evalBlock_apply_ca2f47e524b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_atBlock_apply_5df1ecab43d1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_apply_0f53360b901e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_exists_pow_prod_mem_759ee892cced
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_monomial_mem_of_pow_prod_mem_be9e9091dbb8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_coeffVec_mem_span_26ad69966bfe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_BlockSurjectivity_det_mem_projIdeal_b567b3689f49

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
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution (P : ArithVariety n) (k₀ : ι) (w : Cone (fun _ : Unit ↦ n k₀) ℂ)
    (hw : w ∈ conePoints (P.projIdeal k₀) ℂ) : ∃ z ∈ P.points ℂ, z k₀ = w () := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨N, hJN⟩ := exists_pow_prod_mem P k₀ w (hw.1 ()) hno
  have hmono := monomial_mem_of_pow_prod_mem hJN
  generalize hD : Fintype.card (Coord n) * N = D at hmono
  have hWtop : Submodule.span ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) ''
      homogIn n P k₀ D) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℂ (offMonos n k₀ D)).span_eq, Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    have h1 : coeffVec (offMonos n k₀ D) (monomial μ.1 1) = Pi.basisFun ℂ (offMonos n k₀ D) μ := by
      funext ν
      rw [coeffVec_apply, coeff_monomial, Pi.basisFun_apply, Pi.single_apply]
      by_cases h : μ = ν
      · subst h; simp
      · rw [if_neg (fun h' ↦ h (Subtype.ext h')), if_neg (Ne.symm h)]
    rw [← h1]
    exact coeffVec_mem_span P k₀ w D (hmono μ.1 μ.2)
  obtain ⟨b, hbV, hbspan, hbli⟩ :=
    exists_linearIndependent ℂ ((fun q ↦ coeffVec (offMonos n k₀ D) (atBlock k₀ w q)) '' homogIn n P k₀ D)
  let B : Basis b ℂ (offMonos n k₀ D → ℂ) := Basis.mk hbli (by rw [Subtype.range_coe, hbspan]; exact hWtop.ge)
  let e := (Pi.basisFun ℂ (offMonos n k₀ D)).indexEquiv B
  have hsel : ∀ i : offMonos n k₀ D, ∃ q ∈ homogIn n P k₀ D, coeffVec (offMonos n k₀ D) (atBlock k₀ w q) = (e i : offMonos n k₀ D → ℂ) := by
    intro i
    obtain ⟨q, hq, hqe⟩ := hbV (e i).2
    exact ⟨q, hq, hqe⟩
  choose q hqS hqe using hsel
  have hdet : evalBlock w (Matrix.of fun i (μ : offMonos n k₀ D) ↦ coeff μ.1 (sepBlock k₀ (q i))).det ≠ 0 := by
    rw [RingHom.map_det]
    have hrows : (evalBlock w).mapMatrix (Matrix.of fun i (μ : offMonos n k₀ D) ↦ coeff μ.1 (sepBlock k₀ (q i))) =
        Matrix.of fun i ↦ (e i : offMonos n k₀ D → ℂ) := by
      ext i μ
      show evalBlock w (coeff μ.1 (sepBlock k₀ (q i))) = (e i : offMonos n k₀ D → ℂ) μ
      rw [← hqe i, coeffVec_apply, atBlock_apply, coeff_map]
    rw [hrows]
    have hli : LinearIndependent ℂ (Matrix.of fun i ↦ (e i : offMonos n k₀ D → ℂ)).row := hbli.comp e e.injective
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero
  rw [evalBlock_apply] at hdet
  exact hdet (hw.2 _ (det_mem_projIdeal P k₀ D q hqS))
end GroundTheory.Heights₂.Heights.BlockSurjectivity
