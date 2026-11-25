-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_of_mem_minimalPrimes_chartIdeal_a7d2838e47ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:44.96837+00:00
-- url     : https://prove2.me/submissions/247011ce-b18e-4789-8564-a7952a62b30a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_le_of_mem_minimalPrimes_sup_span_5974699e55b6
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_quotient_le_of_chartIdeal_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.SegreChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open ReciprocityTheory.AnForm.R (chartIdeal conePts affCoord)
namespace GroundTheory.Heights₂.Heights.SegreChartDim
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) {𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h𝔮 : 𝔮 ∈ (chartIdeal P p).minimalPrimes) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = e := by
  classical
  have : 𝔮.IsPrime := h𝔮.1.1
  have hup := ReciprocityTheory.AnForm.R.ringKrullDim_quotient_le_of_chartIdeal_le hP e hdim p 𝔮 h𝔮.1.2
  obtain ⟨Q, hQ, hQ𝔮⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans h𝔮.1.2)
  have hQp : Q.IsPrime := hQ.1.1
  let s : Finset (MvPolynomial (Σ k, ι k) ℂ) := Finset.univ.image fun k => X ⟨k, p k⟩ - 1
  have hs : (s : Set (MvPolynomial (Σ k, ι k) ℂ)) = Set.range fun k => X ⟨k, p k⟩ - 1 := by
    simp [s]
  have hmin : 𝔮 ∈ (Q ⊔ Ideal.span (s : Set (MvPolynomial (Σ k, ι k) ℂ))).minimalPrimes := by
    rw [hs]
    refine ⟨⟨‹_›, sup_le hQ𝔮 (le_sup_right.trans h𝔮.1.2)⟩, fun Z ⟨hZp, hZ⟩ hZ𝔮 => ?_⟩
    exact h𝔮.2 ⟨hZp, sup_le (hQ.1.2.trans (le_sup_left.trans hZ)) (le_sup_right.trans hZ)⟩ hZ𝔮
  have hlow := ringKrullDim_le_of_mem_minimalPrimes_sup_span s Q 𝔮 hQp hmin
  rw [hdim Q hQ] at hlow
  have hcard : s.card ≤ Fintype.card K := Finset.card_image_le.trans (by simp)
  have hne : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) ≠ ⊥ := by
    have : Nontrivial (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.mpr this.ne_top
    exact ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  refine le_antisymm hup ?_
  generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = d at hup hlow hne
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hne
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd hup (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) ≤ (e : ℕ∞)) by simp))
    | coe d =>
      have h1 : e + Fintype.card K ≤ d + s.card := by exact_mod_cast hlow
      exact_mod_cast (show e ≤ d by omega)
end GroundTheory.Heights₂.Heights.SegreChartDim
