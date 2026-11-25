-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_cone_rel_fa3848bfc4a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:49.870835+00:00
-- url     : https://prove2.me/submissions/c640d304-8b9e-43bc-ac88-c07be4704ed1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_eval_coneForm_eac9ec1d557b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_segre_one_block_dd98c2024510
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_forall_eval_of_complexFibreIdeal_f6b70a4a7738
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)
open GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
namespace GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
theorem _root_.solution {n e : ℕ} {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hP : IsArithVar P (e + 1))
    (hΨ : IsGoodProj P Ψ) (i : Fin n) :
    ∃ r : ℕ, 0 < r ∧ ∃ H : Fin (e + 1) → MvPolynomial (Fin n) ℂ,
      (∀ j, (H j).totalDegree ≤ r - 1) ∧
      X i ^ r - ∑ j, coneForm Ψ j * H j ∈ (complexFibreIdeal P).radical := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := ReciprocityTheory.ChartRestriction.G.Geo.segre_rel hP.2.1.2.1 Ψ hΨ (fun _ => i)
  refine ⟨r, hr, fun j => rename (fun f : (k : Unit) → PBlk n k => f ()) (G j),
    fun j => (totalDegree_rename_le _ _).trans (hG j), ?_⟩
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
  intro x hx
  have hae : ∀ p : MvPolynomial (Fin n) ℂ, aeval x p = eval x p := fun _ => rfl
  rw [hae]
  have hxP : ∀ q ∈ complexFibreIdeal P, eval x q = 0 := fun q hq => by
    rw [← hae]
    exact hx q hq
  simp only [map_sub, map_pow, eval_X, map_sum, map_mul, eval_coneForm, eval_rename,
    segre_one_block]
  by_cases hx0 : ∃ i0, x i0 ≠ 0
  · obtain ⟨i0, hi0⟩ := hx0
    have hzm : (fun p : Σ k, PBlk n k => x p.2) ∈ mcPts P :=
      ⟨fun _ => ⟨i0, hi0⟩, forall_eval_of_complexFibreIdeal hxP⟩
    have h := hrel _ hzm
    rw [segre_one_block] at h
    rw [sub_eq_zero]
    exact h
  · push Not at hx0
    have hx' : x = 0 := funext hx0
    subst hx'
    have h0 : (fun _ : (k : Unit) → PBlk n k => (0 : ℂ)) = 0 := rfl
    simp only [Pi.zero_apply] at *
    simp [h0, zero_pow hr.ne']
end GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
