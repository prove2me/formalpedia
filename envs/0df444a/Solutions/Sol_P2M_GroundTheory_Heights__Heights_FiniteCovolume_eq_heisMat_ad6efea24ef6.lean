-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisMat_ad6efea24ef6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:05:44.20181+00:00
-- url     : https://prove2.me/submissions/c691777e-257f-4121-8f8a-0cdaab24eb52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_left_21ed53f20908
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_right_73a7d76a7d0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_left_c1f6b63ea674
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_right_b5b6ef42f985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_mulVec_debb3da7c3fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisMat_unitary_b973147ebfea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_of_mulVec_partner_ab8825d1922e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable [DecidableEq ι]
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {b : ι → ℂ} (hb : hForm H b b = 0) (hab : hForm H a b = 1)
    {n : Matrix ι ι ℂ} (hn : nᴴ * H * n = H) (hna : n *ᵥ a = a)
    (hn' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, n *ᵥ z = z + c • a) :
    hForm H a (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    hForm H b (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    hForm H b (n *ᵥ b - b) + starRingEnd ℂ (hForm H b (n *ᵥ b - b)) +
      hForm H (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a)
        (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) = 0 ∧
    n = heisMat H a (n *ᵥ b - b - hForm H b (n *ᵥ b - b) • a) (hForm H b (n *ᵥ b - b)) := by
  have hba : hForm H b a = 1 := by rw [← hForm_conj hH, hab, map_one]
  set u := n *ᵥ b - b with hu
  set s := hForm H b u with hs
  set y := u - s • a with hy
  have hanb : hForm H a (n *ᵥ b) = 1 := by
    conv_lhs => rw [← hna]
    rw [hForm_mulVec_of_unitary H hn, hab]
  have hau : hForm H a u = 0 := by rw [hu, hForm_sub_right, hanb, hab, sub_self]
  have h1 : hForm H a y = 0 := by rw [hy, hForm_sub_right, hForm_smul_right, hau, ha]; ring
  have h2 : hForm H b y = 0 := by rw [hy, hForm_sub_right, hForm_smul_right, hba, ← hs]; ring
  have hya : hForm H y a = 0 := by rw [← hForm_conj hH, h1, map_zero]
  have hbb := hForm_mulVec_of_unitary H hn b b
  have hnb : n *ᵥ b = b + u := by rw [hu]; abel
  rw [hnb, hb] at hbb
  have hub : hForm H u b = starRingEnd ℂ s := by rw [hs, hForm_conj hH]
  have huu : hForm H u u = hForm H y y := by
    have : u = y + s • a := by rw [hy]; abel
    rw [this]
    simp only [hForm_add_right, hForm_add_left, hForm_smul_right, hForm_smul_left, h1, hya, ha]
    ring
  have h3 : s + starRingEnd ℂ s + hForm H y y = 0 := by
    simp only [hForm_add_right, hForm_add_left, hb, hub, ← hs, huu] at hbb
    linear_combination hbb
  refine ⟨h1, h2, h3, ?_⟩
  refine eq_of_mulVec_partner hH hab hn (heisMat_unitary hH ha h1 h3) hna hn' ?_ ?_
  · intro z hz
    refine ⟨-hForm H y z, ?_⟩
    rw [heisMat_mulVec, hz]
    simp only [zero_smul, add_zero, neg_smul, sub_eq_add_neg]
  · have hyb : hForm H y b = 0 := by rw [← hForm_conj hH, h2, map_zero]
    rw [heisMat_mulVec, hab, hyb, hnb, hy]
    simp only [one_smul, zero_smul, sub_zero, sub_add_cancel]
end GroundTheory.Heights₂.Heights.FiniteCovolume
