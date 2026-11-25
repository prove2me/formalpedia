-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_powerDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:56.92309+00:00
-- url     : https://prove2.me/submissions/59a3c731-435b-43d0-81a7-303a23beec2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_RightHolRightHolEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
open scoped ContDiff
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem contDiff_det_k_type {m : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z.det) := by
  have h : (fun z : Matrix (Fin m) (Fin m) ℂ => z.det) =
      fun z => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, z (σ i) i := by
    funext z
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  rw [h]
  exact ContDiff.sum fun σ _ => contDiff_const.mul
    (contDiff_prod fun i _ => contDiff_pi.1 (contDiff_pi.1 contDiff_id (σ i)) i)
private theorem contDiff_adjugate' {m : ℕ} {k : WithTop ℕ∞} :
    ContDiff ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z.adjugate) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.adjugate_apply]
  have hrow : ContDiff ℂ k
      (fun x : Matrix (Fin m) (Fin m) ℂ => x.updateRow j (Pi.single i 1)) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    by_cases hab : a = j
    · subst hab
      simp only [Matrix.updateRow_self]
      exact contDiff_const
    · simp only [Matrix.updateRow_ne hab]
      exact contDiff_pi.1 (contDiff_pi.1 contDiff_id a) b
  exact contDiff_det_k_type.comp hrow
private theorem contDiffOn_inv_det_ne_zero' {m : ℕ} {k : WithTop ℕ∞} :
    ContDiffOn ℂ k (fun z : Matrix (Fin m) (Fin m) ℂ => z⁻¹) {z | z.det ≠ 0} := by
  have h : (fun z : Matrix (Fin m) (Fin m) ℂ => z⁻¹) = fun z => (z.det)⁻¹ • z.adjugate := by
    funext z
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (contDiff_det_k_type.contDiffOn.inv fun z hz => hz).smul contDiff_adjugate'.contDiffOn
private theorem contDiff_lead_k_type {k : WithTop ℕ∞} (i : ℕ) :
    ContDiff ℂ k (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  by_cases h : i ≤ n
  · simp only [lead, dif_pos h]
    have hs : ContDiff ℂ k
        (fun z : Matrix (Fin n) (Fin n) ℂ => z.submatrix (Fin.castLE h) (Fin.castLE h)) :=
      contDiff_pi.2 fun a => contDiff_pi.2 fun b =>
        contDiff_pi.1 (contDiff_pi.1 contDiff_id (Fin.castLE h a)) (Fin.castLE h b)
    exact contDiff_det_k_type.comp hs
  · simp only [lead, dif_neg h]
    exact contDiff_const
private theorem det_ne_zero_of_mem_omegaP {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaP n) : z.det ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · intro h
    have h0 : z⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit z (by simpa [isUnit_iff_ne_zero] using h)
    have hz' : ∀ i : Fin n, lead ((i : ℕ) + 1) z⁻¹ ≠ 0 := hz
    have h1 : 1 ≤ n := hn
    exact hz' ⟨0, hn⟩ (by rw [h0]; simp [lead, h1])
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiP μ) (OmegaP n) := by
  have hinv : ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => z⁻¹) (OmegaP n) :=
    contDiffOn_inv_det_ne_zero'.mono fun z hz => det_ne_zero_of_mem_omegaP hz
  show ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ =>
    ∏ i : Fin n, lead ((i : ℕ) + 1) z⁻¹ ^ (-(μ i - muNext μ i))) (OmegaP n)
  refine contDiffOn_prod fun i _ => ?_
  have hg : ContDiffOn ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z⁻¹) (OmegaP n) :=
    (contDiff_lead_k_type _).comp_contDiffOn hinv
  have hne : ∀ z ∈ OmegaP n, lead ((i : ℕ) + 1) z⁻¹ ≠ 0 := fun z hz =>
    (show ∀ j : Fin n, lead ((j : ℕ) + 1) z⁻¹ ≠ 0 from hz) i
  rcases Int.eq_nat_or_neg (-(μ i - muNext μ i)) with ⟨k, hk | hk⟩
  · simp only [hk, zpow_natCast]
    exact hg.pow k
  · simp only [hk, _root_.zpow_neg, zpow_natCast]
    exact (hg.pow k).inv fun z hz => pow_ne_zero _ (hne z hz)
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
