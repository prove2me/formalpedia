-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_B2x8_cf_heis__t_8476e10eaf02
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:14.842204+00:00
-- url     : https://prove2.me/submissions/2c36080d-50f9-4d41-82b9-5b15c98841f0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_herm_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Hpk_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_im
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_add_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_eq_hb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_heisenberg_three_block
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (x₀ : HPar k r') (p : ℂ × HPar k r') (h1 : p.1 ≠ 0) :
    heis0 k r' x₀ *ᵥ Ψt k r' p = Ψt k r' (Tn k r' x₀ p) := by
  obtain ⟨c, y, s⟩ := p
  obtain ⟨y₀, s₀⟩ := x₀
  have hp1 : conj c ≠ 0 := (map_ne_zero _).2 h1
  unfold Ψt Tn
  rw [heisenberg_three_block]
  dsimp only at h1 ⊢
  set B : ℂ := hb k r' y s - conj c * herm (Hpk k r') y y₀ + (‖c‖ ^ 2 : ℝ) * hb k r' y₀ s₀ with hB
  have hnorm : ((‖c‖ ^ 2 : ℝ) : ℂ) = c * conj c := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsum : B + conj B = - herm (Hpk k r') (y + c • y₀) (y + c • y₀) := by
    have e1 := hb_add_conj (k := k) (r' := r') y s
    have e2 := hb_add_conj (k := k) (r' := r') y₀ s₀
    have e3 : conj (herm (Hpk k r') y y₀) = herm (Hpk k r') y₀ y := herm_conj _ (Hpk_herm k r') _ _
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
    rw [hB]
    simp only [map_add, map_sub, map_mul, Complex.conj_conj, Complex.conj_ofReal, e3]
    rw [hnorm]
    linear_combination e1 + c * conj c * e2
  have him : B.im = s - (conj c * herm (Hpk k r') y y₀).im + ‖c‖ ^ 2 * s₀ := by
    rw [hB]
    simp only [Complex.add_im, Complex.sub_im, hb_im, Complex.im_ofReal_mul]
  have hBB := eq_hb hsum
  rw [him] at hBB
  rw [← hBB]
  congr 1
  rw [hB, hnorm]
  field_simp
end Formalism.FourierDecayAlt.P.B2x8
