-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.M_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:13.439053+00:00
-- url     : https://prove2.me/submissions/eba63b34-1f1f-4ab9-af4e-e6f388d3d07d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_left
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_smul_left
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_zero_left
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_unitary
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_g_perp
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_gw_decomp
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open Matrix
open scoped ComplexOrder
namespace PI.ScPiBuildW.Loc
open PI.ScPiExists
section Basic
variable {n : ℕ} (ε : Fin n → Bool)
end Basic
namespace LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
section Grp
variable {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
include hg hS
end Grp
private lemma hJ_sum_left_lemma_2 {ι : Type*} (s : Finset ι) (y : Fin n → ℂ) (c : ι → ℂ)
    (u : ι → Fin n → ℂ) : hJ ε (∑ i ∈ s, c i • u i) y = ∑ i ∈ s, star (c i) * hJ ε (u i) y := by
  classical
  refine Finset.induction_on s (by simp [hJ_zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hJ_add_left, hJ_smul_left, ih]
end LocFrame
end PI.ScPiBuildW.Loc
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder
open PI PI.ScPiBuildW PI.ScPiBuildW.Loc
open PI.ScPiExists
open PI.ScPiBuildW.Loc.LocFrame
variable {n r k : ℕ} {ε : Fin n → Bool} (L : LocFrame n r k ε)
namespace PI.ScPiBuildW.Loc.LocFrame
theorem _root_.solution {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g) :
    (L.M g)ᴴ * L.M g = 1 := by
  ext a b
  have h1 : hJ ε (g *ᵥ L.w a) (g *ᵥ L.w b) = if a = b then 1 else 0 := by
    rw [hJ_unitary ε hg, L.ww]
  rw [L.gw_decomp hg hS a, hJ_add_left, hJ_sum_left_lemma_2, hJ_sum_left_lemma_2] at h1
  simp only [L.g_perp hg hS (fun a' => L.ew a' b), mul_zero, Finset.sum_const_zero, add_zero] at h1
  rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.conjTranspose_apply]
  rfl
end PI.ScPiBuildW.Loc.LocFrame
