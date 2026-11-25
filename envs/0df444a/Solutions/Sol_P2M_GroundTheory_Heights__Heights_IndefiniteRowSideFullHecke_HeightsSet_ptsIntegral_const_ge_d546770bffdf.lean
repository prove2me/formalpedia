-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_ptsIntegral_const_ge_d546770bffdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:26.60465+00:00
-- url     : https://prove2.me/submissions/9d56d71b-f21b-4733-889a-7ed8136bf6cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSmoothHermConstLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_maDensity_fin_zero_86460df5dcd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_segre_torus_smul_168b7b47e649

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
theorem _root_.solution (P : Ideal (MRing ι)) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {t : ℝ}
    (ht : t ≤ 0) (hP : 0 < degC P) : t * degC P ≤ ptsIntegral P φ (fun _ ↦ t) := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · set Ψ := hΨ.choose
    have hvol : (volume : Measure (Fin 0 → ℂ)) = Measure.dirac (fun i ↦ i.elim0) := by
      rw [volume_pi]
      exact Measure.pi_of_empty _
    rw [hvol, integral_dirac]
    set y₀ : Fin 0 → ℂ := fun i ↦ i.elim0
    unfold degC at hP ⊢
    obtain ⟨-, hfinQ⟩ := Nat.card_pos_iff.mp hP

    let r := fun z z' : mcPts P ↦
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p
    let G : Quot r → (((k : K) → ι k) → ℂ) := Quot.lift
      (fun z : mcPts P ↦ (Ψ (segre (z : (Σ k, ι k) → ℂ)) 0)⁻¹ • segre (z : (Σ k, ι k) → ℂ))
      (by
        rintro z z' ⟨c, hc, hz'⟩
        rw [hz', segre_torus_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv]
        have hμ : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
        congr 1
        field_simp)
    let F : fibre P Ψ y₀ → Quot r := fun w ↦ Quot.mk r ⟨w.2.choose, w.2.choose_spec.1⟩
    have hGF : ∀ w, G (F w) = w := by
      intro w
      obtain ⟨h1, h2, h3⟩ := w.2.choose_spec
      show (Ψ (segre w.2.choose) 0)⁻¹ • segre w.2.choose = (w : ((k : K) → ι k) → ℂ)
      rw [h2, h3]
      simp
    have hinj : Function.Injective F := fun a b hab ↦ Subtype.ext (by
      rw [← hGF a, ← hGF b, hab])
    have : Finite (fibre P Ψ y₀) := Finite.of_injective F hinj
    have hcard := Nat.card_le_card_of_injective F hinj
    have hfin : (fibre P Ψ y₀).Finite := Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hterm : ∀ w ∈ hfin.toFinset, t ≤ sheetDensity P Ψ φ (fun _ ↦ t) y₀ w := by
      intro w _
      unfold sheetDensity
      split_ifs
      · rw [maDensity_fin_zero, mul_one]
      · exact ht
    have hsum := Finset.card_nsmul_le_sum _ _ t hterm
    rw [nsmul_eq_mul] at hsum
    have hc : (hfin.toFinset.card : ℝ) ≤ Nat.card (Quot r) := by
      rw [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq]
      exact_mod_cast hcard
    nlinarith
  · have : (0 : ℝ) ≤ degC P := Nat.cast_nonneg _
    nlinarith
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
