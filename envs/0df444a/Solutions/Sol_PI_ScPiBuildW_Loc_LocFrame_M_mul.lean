-- Prove2me | solution 1 for PI.ScPiBuildW.Loc.LocFrame.M_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:48.253208+00:00
-- url     : https://prove2.me/submissions/68b2329d-9a49-432f-a8d9-b6b59ea43b37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_add_right
import Theorems.Thm_PI_ScPiBuildW_Loc_hJ_sum_right
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_we
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_e_mem
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_hJ_X_right
import Theorems.Thm_PI_ScPiBuildW_Loc_LocFrame_gX
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
private lemma mulVec_sum_lemma {ι : Type*} (s : Finset ι) (g : Matrix (Fin n) (Fin n) ℂ) (c : ι → ℂ)
    (u : ι → Fin n → ℂ) : g *ᵥ (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i • (g *ᵥ u i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, Matrix.mulVec_smul, ih]
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
theorem _root_.solution {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (hS : InS L.e L.z g)
    (hg' : Formalism.REAL.inUJ ε g') (hS' : InS L.e L.z g') : L.M (g * g') = L.M g * L.M g' := by
  ext c b
  have hXr : ∀ a, hJ ε (L.w c) (g *ᵥ L.e a) = 0 := fun a =>
    L.hJ_X_right (L.gX hS (L.e_mem a)) (fun a' => L.we c a')
  have e1 : L.M (g * g') c b = hJ ε (L.w c) (g *ᵥ (g' *ᵥ L.w b)) := by
    show hJ ε (L.w c) ((g * g') *ᵥ L.w b) = _
    rw [Matrix.mulVec_mulVec]
  rw [e1, L.gw_decomp hg' hS' b, Matrix.mulVec_add, hJ_add_right, mulVec_sum_lemma, mulVec_sum_lemma,
    hJ_sum_right, hJ_sum_right]
  simp only [hXr, mul_zero, Finset.sum_const_zero, add_zero, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_comm]
  rfl
end PI.ScPiBuildW.Loc.LocFrame
