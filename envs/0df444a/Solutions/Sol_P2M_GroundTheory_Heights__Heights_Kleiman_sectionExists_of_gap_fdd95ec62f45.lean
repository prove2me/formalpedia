-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_sectionExists_of_gap_fdd95ec62f45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:30.948568+00:00
-- url     : https://prove2.me/submissions/f9ec928c-5817-4227-9ae2-19ef405e6f50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmplePowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_pos_of_eventually_lower_cf01f4457600
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_lineBundle_twistMul_fe4f7be26a50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twistMul_e492a93d5146


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (hcount : SectionCount.Statement.{u, w})
    (hlead : LeadingCoeffPos.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {d : ℕ} {M : LineBundle k x} {t s' : ℚ}
    (hZ : IsSubvar x (primeOf (S := k) x) (d + 1)) (hM : Nef M.toSubSystem) (hs' : 0 < s')
    {Q : ℕ} {mQ : ℤ} (hQ : 0 < Q) (hmQ : (mQ : ℚ) = Q * t)
    (hva : IsVeryAmple (twistMul M.toSubSystem Q mQ))
    (hgap : 1 < (Q : ℚ) * (t / (d + 1) - s')) :
    ∃ (p : ℕ) (m c₁ : ℤ), 1 ≤ p ∧ (m : ℚ) = p * (t - s') ∧ 1 ≤ c₁ ∧
      ∃ σ ∈ (twistMul M.toSubSystem p (m - c₁)).secs, σ ≠ 0 := by
  obtain ⟨Nb, hNb⟩ := exists_lineBundle_twistMul M Q mQ
  have hvaN : IsVeryAmple Nb.toSubSystem := hNb ▸ hva

  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = ⌊(Q : ℚ) * s'⌋₊ + 1 := ⟨_, rfl⟩
  have hQs'0 : 0 ≤ (Q : ℚ) * s' := by positivity
  have hb_gt : (Q : ℚ) * s' < b := by rw [hb]; push_cast; exact Nat.lt_floor_add_one _
  have hb_le : (b : ℚ) ≤ Q * s' + 1 := by rw [hb]; push_cast; linarith [Nat.floor_le hQs'0]
  have hd0 : (d : ℚ) + 1 ≠ 0 := by positivity
  have hd : (0 : ℚ) < d + 1 := by positivity
  have hbT : (b : ℚ) < Q * (t / (d + 1)) := by
    have := hgap
    rw [mul_sub] at this
    linarith
  have hbm : ((d + 1 : ℕ) : ℤ) * b < mQ := by
    have h1 : ((d : ℚ) + 1) * b < (d + 1) * (Q * (t / (d + 1))) := mul_lt_mul_of_pos_left hbT hd
    have h2 : ((d : ℚ) + 1) * (Q * (t / (d + 1))) = Q * t := by field_simp
    have h3 : ((((d + 1 : ℕ) : ℤ) * b : ℤ) : ℚ) < (mQ : ℚ) := by
      push_cast
      rw [hmQ]
      linarith
    exact_mod_cast h3
  have hb1 : 1 ≤ b := by omega
  obtain ⟨C, hC⟩ := hcount k Ω N x d Nb b hZ hvaN hb1
  have hcoef := hlead k Ω N x d M Nb Q mQ b hZ hM hNb hvaN hbm

  have hden := Rat.mul_den_eq_num ((Q : ℚ) * s')
  have hD1 : 0 < ((Q : ℚ) * s').den := Rat.den_pos _
  generalize ((Q : ℚ) * s').den = D at hden hD1
  generalize ((Q : ℚ) * s').num = E at hden
  obtain ⟨n₁, hn₁, hpos⟩ := exists_pos_of_eventually_lower hcoef hC D hD1
  have hne : (twistMul Nb.toSubSystem (D * n₁) (-(((D * n₁ : ℕ) : ℤ) * b))).secs ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    simp at hpos
  obtain ⟨σ, hσ, hσne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [hNb, twistMul_twistMul] at hσ
  refine ⟨D * n₁ * Q, ((D * n₁ : ℕ) : ℤ) * mQ - n₁ * E, ((D * n₁ : ℕ) : ℤ) * b - n₁ * E,
    Nat.mul_pos (Nat.mul_pos hD1 hn₁) hQ, ?_, ?_, σ, ?_, hσne⟩
  · push_cast
    rw [hmQ, ← hden]
    ring
  · have hDn : (0 : ℚ) < (D : ℚ) * n₁ := by positivity
    have hpos' : (0 : ℚ) < ((((D * n₁ : ℕ) : ℤ) * b - n₁ * E : ℤ) : ℚ) := by
      push_cast
      rw [← hden]
      have key : (D : ℚ) * n₁ * (b - Q * s') = D * n₁ * b - n₁ * (Q * s' * D) := by ring
      have := mul_pos hDn (sub_pos.mpr hb_gt)
      linarith
    have : (0 : ℤ) < ((D * n₁ : ℕ) : ℤ) * b - n₁ * E := by exact_mod_cast hpos'
    omega
  · have hm : ((D * n₁ : ℕ) : ℤ) * mQ - n₁ * E - (((D * n₁ : ℕ) : ℤ) * b - n₁ * E) =
        ((D * n₁ : ℕ) : ℤ) * mQ + -(((D * n₁ : ℕ) : ℤ) * b) := by ring
    rw [hm]
    exact hσ
end GroundTheory.Heights₂.Heights.Kleiman
