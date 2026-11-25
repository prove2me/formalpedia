-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_of_mulVec_partner_ab8825d1922e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:27.163552+00:00
-- url     : https://prove2.me/submissions/ba20a62f-b2e0-46e1-b686-a1d12472808f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_add_right_73a7d76a7d0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_sub_right_ae1f47de359a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_smul_right_b5b6ef42f985
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_mulVec_of_unitary_4c2fa1afaeb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_matrix_ext_mulVec_52bd164b4cc0

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
omit ha
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {b : ι → ℂ} (hab : hForm H a b = 1) {n m : Matrix ι ι ℂ}
    (hn : nᴴ * H * n = H) (hm : mᴴ * H * m = H)
    (hna : n *ᵥ a = a)
    (hn' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, n *ᵥ z = z + c • a)
    (hm' : ∀ z, hForm H a z = 0 → ∃ c : ℂ, m *ᵥ z = z + c • a) (hnb : n *ᵥ b = m *ᵥ b) :
    n = m := by
  have hba : hForm H b a = 1 := by rw [← hForm_conj hH, hab, map_one]
  have hnba : hForm H (n *ᵥ b) a = 1 := by
    conv_lhs => rw [← hna]
    rw [hForm_mulVec_of_unitary H hn, hba]
  refine matrix_ext_mulVec fun p => ?_
  set p' := p - hForm H a p • b with hp'
  have hap' : hForm H a p' = 0 := by
    rw [hp', hForm_sub_right, hForm_smul_right, hab, mul_one, sub_self]
  have hp : p = p' + hForm H a p • b := by rw [hp']; abel
  obtain ⟨c, hc⟩ := hn' p' hap'
  obtain ⟨d, hd⟩ := hm' p' hap'
  have e1 := hForm_mulVec_of_unitary H hn b p'
  have e2 := hForm_mulVec_of_unitary H hm b p'
  rw [hc] at e1
  rw [hd, ← hnb] at e2
  rw [hForm_add_right, hForm_smul_right, hnba] at e1 e2
  have hcd : c = d := by linear_combination e1 - e2
  rw [hp, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hc, hd, hcd, hnb]
end GroundTheory.Heights₂.Heights.FiniteCovolume
