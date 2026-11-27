-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetComass_proof_69d840e2ed25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:24.167287+00:00
-- url     : https://prove2.me/submissions/16bc8c0f-67f9-4440-be88-8f4faf29d41b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetComass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetComassAlt_sheetJac_eq_norm_det_bfc522397957
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_d56f1b066651
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_exists_hessC_bound_adf0c8df653f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_isClosed_zeroSet_fca0401c6138
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_comp
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_mdisc_le_of_abs_le


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
open MvPolynomial Matrix ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SheetComass
theorem _root_.solution : SheetComass.Statement := by
  intro n d J A φ R hφ
  choose U hUo hZU hφU using hφ
  have hK : IsCompact (zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R) :=
    (isCompact_closedBall (0 : Fin n → ℂ) R).inter_left (SheetSumMeasurable.isClosed_zeroSet J)
  obtain ⟨c, hc, hb⟩ := TubeFormComparison.exists_hessC_bound φ _ hK U hUo
    (fun i => Set.inter_subset_left.trans (hZU i))
    (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  refine ⟨(d.factorial : ℝ) * (2 / Real.pi) ^ d * (3 ^ d * c ^ d), fun x hx s hs => ?_⟩
  obtain ⟨V, hV, hyV, hsd, hsx, -, -⟩ := hs
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hV hsd _ hyV
  have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
    rw [hsx]
    exact ((hφU i).contDiffAt ((hUo i).mem_nhds (hZU i hx.1))).of_le (WithTop.coe_le_coe.2 le_top)
  set Jc := ReciprocityTheory.AnForm.A.jacC s (A *ᵥ x) with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hA : ∀ i, hessC (φ i ∘ s) (A *ᵥ x) = Bᴴ * hessC (φ i) x * B := fun i => by
    have h := ReciprocityTheory.AnForm.A.hessC_comp (φ i) s _ hsa (hφx i)
    rw [hsx] at h
    rw [hBJ]
    exact h
  have hle : ∀ k, ((fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k -
      (fun k => hessC (φ k ∘ s) (A *ᵥ x)) k).PosSemidef := fun k => by
    have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC (φ k) x * B =
        Bᴴ * (-hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      abel
    simp only [hA, e]
    exact (hb k x hx).2.conjTranspose_mul_mul_same B
  have hge : ∀ k, ((fun k => hessC (φ k ∘ s) (A *ᵥ x)) k +
      (fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k).PosSemidef := fun k => by
    have e : Bᴴ * hessC (φ k) x * B + (c : ℂ) • (Bᴴ * B) =
        Bᴴ * (hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    simp only [hA, e]
    exact (hb k x hx).1.conjTranspose_mul_mul_same B
  have key := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le _ _ hle hge
  rw [ReciprocityTheory.AnForm.A.mdisc_const, Matrix.det_smul, Fintype.card_fin] at key
  have hconj : Bᴴ * B = (Jcᴴ * Jc).map (starRingEnd ℂ) := by
    rw [hBJ, hB]
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have hdet : ‖(Bᴴ * B).det‖ = sheetJac s (A *ᵥ x) := by
    have hm : ((Jcᴴ * Jc).map (starRingEnd ℂ)).det = starRingEnd ℂ (Jcᴴ * Jc).det :=
      (RingHom.map_det _ _).symm
    rw [SheetComassAlt.sheetJac_eq_norm_det s _ (hsd.differentiableAt (hV.mem_nhds hyV)), hconj, hm,
      Complex.norm_conj]
  have hre : (((c : ℂ) ^ d * (Bᴴ * B).det).re) ≤ c ^ d * sheetJac s (A *ᵥ x) := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc, hdet]
  have hm : |(mdisc fun k => hessC (φ k ∘ s) (A *ᵥ x)).re| ≤ 3 ^ d * (c ^ d * sheetJac s (A *ᵥ x)) :=
    (Complex.abs_re_le_norm _).trans (key.trans (mul_le_mul_of_nonneg_left hre (by positivity)))
  unfold maDens
  rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc _ (3 ^ d * c ^ d), mul_assoc (3 ^ d)]
  exact mul_le_mul_of_nonneg_left hm (by positivity)
end SheetComass
end GroundTheory.Heights₂.Heights
