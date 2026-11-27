-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeBranchDimOne_proof_890c33f94c33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:54.040473+00:00
-- url     : https://prove2.me/submissions/15efea7c-a830-45ad-a000-7398f1edb8e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeBranchDimOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalDimDomain_proof_aafc8deef599
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MaximalIdealHeightFG_proof_60a444887d99


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace PrimeBranchDimOne
theorem _root_.solution : PrimeBranchDimOne.Statement := by
  intro n J q c hJ hloc

  have hq : q ∈ zeroSet J := by
    have := c.mapsTo (Metric.mem_ball_self c.radius_pos)
    rwa [c.map_zero] at this

  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    have h1 := ringKrullDim_quotient_le J
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (e : ℕ) := by
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at hle hnn
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hnn (by simp)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hle
        exact absurd (WithBot.coe_le_coe.mp h3) (by simp)
      | coe e => exact ⟨e, rfl⟩
  have hdim : ringKrullDim (localRingAt J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have he1 : e ≤ 1 := by
    have h2 : ((e : ℕ) : WithBot ℕ∞) ≤ 1 := hdim ▸ hloc
    exact_mod_cast h2
  rw [he]
  obtain h0 | h1 : e = 0 ∨ e = 1 := by omega
  swap
  · rw [h1]
  exfalso
  subst h0

  have hfield : IsField (MvPolynomial (Fin n) ℂ ⧸ J) := by
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (ringKrullDimZero_iff_ringKrullDim_eq_zero).2 (by simpa using he)
    exact Ring.KrullDimLE.isField_of_isDomain
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hfield
  have hJM : J = RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    hmax.eq_of_le (RingHom.ker_ne_top _) (fun f hf => RingHom.mem_ker.mpr (hq f hf))

  have hZ : ∀ x ∈ zeroSet J, x = q := by
    intro x hx
    funext i
    have hmem : X i - C (q i) ∈ J := by
      rw [hJM, RingHom.mem_ker]
      simp
    have := hx _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.mp this

  set r := c.radius
  let v : Fin 1 → ℂ := fun _ => ((r / 2 : ℝ) : ℂ)
  have hv : v ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff c.radius_pos]
    intro i
    simp only [v, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos c.radius_pos)]
    exact half_lt_self c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := Metric.mem_ball_self c.radius_pos
  have heq : c.toFun v = c.toFun 0 := by
    rw [hZ _ (c.mapsTo hv), hZ _ (c.mapsTo h0)]
  have := congrFun (c.injOn hv h0 heq) 0
  simp only [v, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  exact (half_pos c.radius_pos).ne' this
end PrimeBranchDimOne
end GroundTheory.Heights₂.Heights
