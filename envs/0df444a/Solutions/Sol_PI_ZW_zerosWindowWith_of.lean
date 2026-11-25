-- Prove2me | solution 1 for PI.ZW.zerosWindowWith_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:51.014328+00:00
-- url     : https://prove2.me/submissions/6b77e094-9a83-4345-aaf4-146e85ada108

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem
import Theorems.Thm_P2M_PI_ZW_finsum_mem_le_of_subset__d846247134c2
import Theorems.Thm_P2M_PI_ZW_finsum_mem_le_finsum_mem__57f47eb1a398
import Theorems.Thm_PI_ZW_ne_one_or_of_isPrimitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution (C : ℝ) (hR : RightHalfWith C) (hT : Transfer) :
    PI.ZerosWindowWith (2 * C) := by
  intro N _ χ hχ t
  have hχ' : χ ≠ 1 ∨ N = 1 := ne_one_or_of_isPrimitive hχ
  have hχi : χ⁻¹ ≠ 1 ∨ N = 1 := hχ'.imp (fun h h' => h (inv_eq_one.mp h')) id
  obtain ⟨hA, hAs⟩ := hR N χ hχ' t
  obtain ⟨hB, hBs⟩ := hR N χ⁻¹ hχi (-t)
  rw [abs_neg] at hBs
  have hZrA : ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re} ⊆ RightNear χ t :=
    fun ρ ⟨⟨_, h1, h2, h3⟩, h4⟩ => ⟨h4, h1, h2, h3⟩
  have hZl : ∀ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}, 1 - ρ ∈ RightNear χ⁻¹ (-t) := by
    rintro ρ ⟨⟨h0, h1, h2, h3⟩, h4⟩
    simp only [Set.mem_setOf_eq] at h4
    refine ⟨by simp; linarith, by simp; linarith, ?_, (hT N χ hχ ρ h0 h1 h3).1⟩
    simp only [Complex.sub_im, Complex.one_im, zero_sub]
    rw [show -ρ.im - -t = -(ρ.im - t) by ring, abs_neg]
    exact h2
  have hsplit : ZerosNear χ t = (ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re}) ∪ (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}) :=
    Set.ext fun ρ => ⟨fun h => (le_or_gt (1 / 2) ρ.re).imp (fun h' => ⟨h, h'⟩) (fun h' => ⟨h, h'⟩),
      fun h => h.elim (·.1) (·.1)⟩
  have hBimg : ((fun σ : ℂ => 1 - σ) '' RightNear χ⁻¹ (-t)).Finite := hB.image _
  have hZfin : (ZerosNear χ t).Finite := by
    rw [hsplit]
    refine (hA.subset hZrA).union (hBimg.subset fun ρ hρ => ⟨1 - ρ, hZl ρ hρ, by ring⟩)
  refine ⟨hZfin, ?_⟩
  have hdisj : Disjoint (ZerosNear χ t ∩ {ρ | 1 / 2 ≤ ρ.re}) (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}) :=
    Set.disjoint_left.mpr fun ρ h1 h2 => absurd (show (1 / 2 : ℝ) ≤ ρ.re from h1.2) (not_le.mpr (show ρ.re < 1 / 2 from h2.2))
  have hfl : (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}).Finite := hZfin.subset Set.inter_subset_left
  rw [hsplit, finsum_mem_union hdisj (hZfin.subset Set.inter_subset_left) hfl]
  have e1 := finsum_mem_le_of_subset' (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
    (fun _ => Nat.cast_nonneg _) hA hZrA
  have e2 : ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2},
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) ≤
      ∑ᶠ σ ∈ RightNear χ⁻¹ (-t), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) := by
    calc ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
        ≤ ∑ᶠ ρ ∈ ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) (1 - ρ) : ℝ) :=
          finsum_mem_le_finsum_mem' _ _ hfl fun ρ hρ => by
            exact_mod_cast (hT N χ hχ ρ hρ.1.1 hρ.1.2.1 hρ.1.2.2.2).2
      _ = ∑ᶠ σ ∈ (fun σ : ℂ => 1 - σ) '' (ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2}), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) :=
          (finsum_mem_image (f := fun σ => (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ))
            (g := fun σ : ℂ => 1 - σ) (s := ZerosNear χ t ∩ {ρ | ρ.re < 1 / 2})
            (fun a _ b _ h => by simpa using h)).symm
      _ ≤ ∑ᶠ σ ∈ RightNear χ⁻¹ (-t), (analyticOrderNatAt (DirichletCharacter.LFunction χ⁻¹) σ : ℝ) :=
          finsum_mem_le_of_subset' _ (fun _ => Nat.cast_nonneg _) hB (by
            rintro _ ⟨ρ, hρ, rfl⟩
            exact hZl ρ hρ)
  linarith
end PI.ZW
