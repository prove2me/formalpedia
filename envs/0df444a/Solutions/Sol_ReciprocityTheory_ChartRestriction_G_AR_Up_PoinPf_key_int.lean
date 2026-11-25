-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.key_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:03:45.278805+00:00
-- url     : https://prove2.me/submissions/66746658-98f5-4276-bff3-a86785bc5f81

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfC
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_cont_cpt__b03189f8567d
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_isOpen_Bset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_pow_half_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_supR_ne_top
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


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private theorem apply_cc_eq_starRingEnd_apply (τ : E →+* ℂ) (z : E) : τ (cc z) = starRingEnd ℂ (τ z) := by
  unfold cc
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj τ z
    | exact NumberField.IsCMField.complexEmbedding_complexConj E τ z
    | exact NumberField.IsCMField.complexEmbedding_complexConj (K := E) τ z
    | simp
private theorem gram_eq_transpose_mul_mul_map_conj (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  all_goals rw [Finset.sum_comm]
private theorem transpose_mul_mul_map_cc_eq_of_isUStab' {γ : GL (Fin r) E} {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} (h : IsUStab G Λ γ) :
    (γ : Matrix (Fin r) (Fin r) E).transpose * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
  ext p q
  have hcs : ∀ b, cc ((Pi.single q (1 : E) : Fin r → E) b) = (Pi.single q (1 : E) : Fin r → E) b := by
    intro b
    by_cases hb : b = q
    · subst hb
      simp [cc]
    · simp [cc, hb, Pi.single_apply]
  have hv : ∀ (j a : Fin r), ((γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single j (1 : E) : Fin r → E)) a =
      (γ : Matrix (Fin r) (Fin r) E) a j := by
    intro j a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h2 : ∑ a, ∑ b, (Pi.single p (1 : E) : Fin r → E) a * G a b * (Pi.single q (1 : E) : Fin r → E) b =
      G p q := by
    simp [Pi.single_apply]
  have h1 := h.1 (Pi.single p (1 : E) : Fin r → E) (Pi.single q (1 : E) : Fin r → E)
  simp only [herm, hv, hcs] at h1
  rw [h2] at h1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact h1
private theorem gram_mat_lact (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r)
    (τ : X.Ψ) : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat (lact γ x) τ) = ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (mat x τ) := by
  have hU := transpose_mul_mul_map_cc_eq_of_isUStab' (X.Γ_stab γ hγ)
  have hA : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    ext a b
    simp only [Matrix.map_apply]
    exact (apply_cc_eq_starRingEnd_apply τ.1 _).symm
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have hU' : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 = X.Gm.map τ.1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  have key : ∀ Y : Matrix (Fin r) (Fin r) ℂ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).transpose *
      (X.Gm.map τ.1 * (((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 * Y)) = X.Gm.map τ.1 * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU']
  rw [gram_eq_transpose_mul_mul_map_conj, gram_eq_transpose_mul_mul_map_conj, hm, Matrix.transpose_mul, Matrix.map_mul, hA]
  simp only [Matrix.mul_assoc]
  rw [key]
private theorem lact_mem_dom_of_mem_Γ (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : lact γ x ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨h1, h2⟩ := hx τ
  refine ⟨?_, fun i => ?_⟩
  · show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ h1
    have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
      (RingHom.map_det τ.1 _).symm
    rw [hd]
    exact (map_ne_zero τ.1).mpr ((Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit).ne_zero
  · have hd : dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
      unfold dmin
      rw [gram_mat_lact X hγ x τ]
    rw [hd]
    exact h2 i
private theorem differentiable_lact_upper_bounds (X : Data E r) (γ : GL (Fin r) E) :
    Differentiable ℂ (fun y : Frame X.Ψ r => lact γ y) := by
  refine differentiable_pi.mpr fun τ => differentiable_pi.mpr fun a =>
    differentiable_pi.mpr fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  first
    | fun_prop
    | exact Differentiable.sum fun k _ => ((differentiable_apply b).comp
        ((differentiable_apply k).comp (differentiable_apply τ))).const_mul _
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (hW : IsMetricW X la W)
    {c : ℝ} (hc : 0 < c) (hcW : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x)
    (P : Frame X.Ψ r → ℂ) (hP : DifferentiableOn ℂ P X.dom) {x : Frame X.Ψ r} {ρ : ℝ}
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hI : ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 * W (lact γ (cpt X x w)) ≠ ⊤) :
    ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) ≤
      supR X la W ρ x ^ 2 * ∫⁻ w in Bset X x ρ, ‖P (lact γ (cpt X x w))‖ₑ ^ 2 * W (lact γ (cpt X x w)) := by
  unfold IsMetricW at hW
  have hS : supR X la W ρ x ≠ ⊤ := supR_ne_top X la W hc hcW ρ x
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hS)]
  have hBm : MeasurableSet (Bset X x ρ) := (isOpen_Bset X x ρ).measurableSet
  have hgc : Continuous fun w => lact γ (cpt X x w) :=
    (differentiable_lact_upper_bounds X γ).continuous.comp (cont_cpt' X x)
  have hmaps : ∀ w ∈ Bset X x ρ, lact γ (cpt X x w) ∈ X.dom := fun w hw =>
    lact_mem_dom_of_mem_Γ X hγ (show ‖w‖ < ρ ∧ cpt X x w ∈ X.dom from hw).2
  have hPc : ContinuousOn (fun w => P (lact γ (cpt X x w))) (Bset X x ρ) :=
    hP.continuousOn.comp hgc.continuousOn hmaps
  have hmeas : AEMeasurable (fun w => ‖P (lact γ (cpt X x w))‖ₑ ^ 2 * W (lact γ (cpt X x w)))
      (volume.restrict (Bset X x ρ)) :=
    ((hPc.aemeasurable hBm).enorm.pow_const 2).mul (hW.1.comp hgc.measurable).aemeasurable
  have hfin := ae_lt_top' hmeas hI
  refine lintegral_mono_ae ?_
  filter_upwards [hfin, ae_restrict_mem hBm] with w hw hwB
  have hwB' : ‖w‖ < ρ ∧ cpt X x w ∈ X.dom := hwB
  have hy : cpt X x w ∈ X.dom := hwB'.2
  have hWγ : W (lact γ (cpt X x w)) = W (cpt X x w) := hW.2.2 γ hγ _ hy
  rw [hWγ] at hw ⊢
  have hW0 : W (cpt X x w) ≠ 0 := by
    have h1 := hcW _ hy
    intro h0
    rw [h0] at h1
    have h2 : (0 : ℝ≥0∞) < ENNReal.ofReal (c * Real.exp (-phla X la (cpt X x w))) :=
      ENNReal.ofReal_pos.mpr (mul_pos hc (Real.exp_pos _))
    exact absurd h1 (not_le.mpr h2)
  have h1 : (ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) / W (cpt X x w)) ^ (1 / 2 : ℝ) ≤
      supR X la W ρ x := by
    unfold supR
    exact le_iSup_of_le w (le_iSup_of_le hwB'.1 (le_iSup_of_le hy le_rfl))
  set f := ‖P (lact γ (cpt X x w))‖ₑ ^ 2
  set e := ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))
  by_cases hf0 : f = 0
  · rw [hf0]
    simp
  · have hWT : W (cpt X x w) ≠ ⊤ := by
      intro hT
      rw [hT, ENNReal.mul_top hf0] at hw
      exact lt_irrefl _ hw
    have hle : e / W (cpt X x w) ≤ supR X la W ρ x ^ 2 := by
      calc e / W (cpt X x w) = ((e / W (cpt X x w)) ^ (1 / 2 : ℝ)) ^ 2 := (pow_half_sq _).symm
        _ ≤ supR X la W ρ x ^ 2 := by
          first
            | exact pow_le_pow_left' h1 2
            | exact pow_le_pow_left₀ (zero_le _) h1 2
            | gcongr
    have he : e ≤ supR X la W ρ x ^ 2 * W (cpt X x w) := by
      calc e = e / W (cpt X x w) * W (cpt X x w) := (ENNReal.div_mul_cancel hW0 hWT).symm
        _ ≤ supR X la W ρ x ^ 2 * W (cpt X x w) := by gcongr
    calc f * e ≤ f * (supR X la W ρ x ^ 2 * W (cpt X x w)) := by gcongr
      _ = supR X la W ρ x ^ 2 * (f * W (cpt X x w)) := by ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
