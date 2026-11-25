-- Prove2me | solution 1 for PI.IdealLatticeWork.assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:07.566593+00:00
-- url     : https://prove2.me/submissions/74febd7b-bf21-40bb-b738-261339c0d01b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdealLattice
import Definitions.Def_Formalism_PeriodIntegrals_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_IdealBasisAlt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AreaLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdealLatticeBasis_Assemble
import Theorems.Thm_PI_IdealLatticeWork_im_comb
import Theorems.Thm_PI_IdealLatticeWork_im_scale
import Theorems.Thm_PI_IdealLatticeWork_phi_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.IdealLatticeWork
namespace PI.IdealLatticeWork
theorem _root_.solution : Assemble := by
  intro hA hI hB hL K _ _ φ h2 hcx cc δ hcc hδ
  obtain ⟨b⟩ := hB K h2
  obtain ⟨c₁, hc₁, c₂, hc₂, hspan, p, q, r, s, hc1, hc2, hdet⟩ := hI K b cc hcc
  have hgen : AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ (c : K)} =
      AddSubgroup.closure {δ * φ (c₁ : K), δ * φ (c₂ : K)} := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro w ⟨c, hc, rfl⟩
      obtain ⟨m, n, rfl⟩ := hspan c hc
      rw [phi_comb φ m n c₁ c₂]
      have e : δ * ((m : ℂ) * φ (c₁ : K) + (n : ℂ) * φ (c₂ : K)) =
          m • (δ * φ (c₁ : K)) + n • (δ * φ (c₂ : K)) := by
        simp only [zsmul_eq_mul]
        ring
      rw [e]
      exact AddSubgroup.add_mem _
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) m)
        (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by simp)) n)
    · rw [AddSubgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact AddSubgroup.subset_closure ⟨c₁, hc₁, rfl⟩
      · exact AddSubgroup.subset_closure ⟨c₂, hc₂, rfl⟩
  have hφc : ∀ c : 𝓞 K, ∀ x y : ℤ, c = x • b 0 + y • b 1 →
      φ (c : K) = (x : ℂ) * φ (b 0 : K) + (y : ℂ) * φ (b 1 : K) := by
    rintro c x y rfl
    exact phi_comb φ x y (b 0) (b 1)
  have him : ((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im =
      ‖δ‖ ^ 2 * (((p * s - q * r : ℤ) : ℝ) * ((starRingEnd ℂ) (φ (b 0 : K)) * φ (b 1 : K)).im) := by
    rw [im_scale, hφc c₁ p q hc1, hφc c₂ r s hc2, im_comb]
  have hA' := hA K φ h2 hcx b
  have hd : (0 : ℝ) < Real.sqrt |(NumberField.discr K : ℝ)| / 2 := by
    have h0 : (NumberField.discr K : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero K
    exact div_pos (Real.sqrt_pos.mpr (abs_pos.mpr h0)) two_pos
  have hn : Ideal.absNorm cc ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hδ2 : (0 : ℝ) < ‖δ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hδ) 2
  have habs : |((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im| =
      ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) := by
    rw [him, abs_mul, abs_mul, hA', abs_of_pos hδ2, ← hdet, Nat.cast_natAbs, Int.cast_abs]
    ring
  have hpos : (0 : ℝ) < ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt |(NumberField.discr K : ℝ)| / 2) :=
    mul_pos (mul_pos hδ2 (by exact_mod_cast Nat.pos_of_ne_zero hn)) hd
  have hne : ((starRingEnd ℂ) (δ * φ (c₁ : K)) * (δ * φ (c₂ : K))).im ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at habs
    linarith
  refine ⟨⟨δ * φ (c₁ : K), δ * φ (c₂ : K), hne, hgen⟩, ?_⟩
  rw [hgen]
  change area (PI.lat2 _ _) = _
  rw [(hL _ _ hne).1, habs]
  ring
end PI.IdealLatticeWork
