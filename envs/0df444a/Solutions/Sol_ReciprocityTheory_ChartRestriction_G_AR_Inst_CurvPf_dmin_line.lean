-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.dmin_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:38:47.463375+00:00
-- url     : https://prove2.me/submissions/32a6a229-13b8-4675-86dc-dde091644014

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LminorMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_mat_line
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_upper_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_det_sub_map_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_lminor_LMU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_lminor_map_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_tr_D_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution (x0 b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (z u : V (nd X)) (τ : X.Ψ)
    (hgram : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (ζ : ℂ) (k : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 (z + ζ • u)) τ k =
      ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt)) (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det *
        starRingEnd ℂ (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) ζ).det *
        starRingEnd ℂ ((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
          (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det := by
  have hk := Nat.le_of_lt_succ k.isLt
  have hL : ∀ a c : Fin r, c < a → (mat b τ)⁻¹ a c = 0 :=
    upper_inv (mat b τ) (hb τ).1 (fun a c h => (hb τ).2 a c h)
  have hU : ∀ a c : Fin r, c < a → ((mat b τ)⁻¹.map (starRingEnd ℂ)) a c = 0 := by
    intro a c h
    rw [Matrix.map_apply, hL a c h, map_zero]
  have hgram' : gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) = diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ) := hgram
  have hre : ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
        ((1 + ζ • Yd X b z u τ) * (mat b τ)⁻¹).map (starRingEnd ℂ) =
      ((mat b τ)⁻¹)ᵀ * ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
        (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) * (mat b τ)⁻¹.map (starRingEnd ℂ) := by
    rw [Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  calc dmin X.Gm (cpt X x0 (z + ζ • u)) τ k
      = lminor (((mat b τ)⁻¹)ᵀ * ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
          (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) * (mat b τ)⁻¹.map (starRingEnd ℂ)) k := by
        show lminor (gram τ.1 X.Gm (mat (cpt X x0 (z + ζ • u)) τ)) k = _
        rw [mat_line X x0 b hb z u τ ζ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul, hgram', hre]
    _ = ((mat b τ)⁻¹.submatrix (Fin.castLE hk) (Fin.castLE hk)).det *
          lminor ((1 + ζ • Yd X b z u τ)ᵀ * (diagonal fun a : Fin r => ((Dsg X a : ℝ) : ℂ)) *
            (1 + ζ • Yd X b z u τ).map (starRingEnd ℂ)) k *
          (((mat b τ)⁻¹.map (starRingEnd ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det :=
        lminor_LMU _ _ _ hL hU k
    _ = _ := by
        rw [tr_D_conj, lminor_map_conj, det_sub_map_conj (mat b τ)⁻¹ hk]
        rfl
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
