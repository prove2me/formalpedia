-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.DjC.det_sub_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:36:57.557379+00:00
-- url     : https://prove2.me/submissions/6018a3b1-e874-4d39-baaf-fcbcb707797f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjCurveB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_smul_real_eq
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_exp_add_real
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_hasDerivAt_det_of_one
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_hasDerivAt_exp_entry
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_pres_exp
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_DjC_pres_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.DjC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {N j : ℕ}
namespace PI.UnitaryCorollaryDerivatives.DjC
theorem _root_.solution (e : Fin j ↪ Fin N) (S : Set (Fin N)) (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Pres S Y)
    (hm : ∀ E F : Matrix (Fin N) (Fin N) ℂ, Pres S E → Pres S F → sub e (E * F) = sub e E * sub e F) (t : ℝ) :
    (sub e (NormedSpace.exp ((t : ℂ) • Y))).det = Complex.exp (t * (sub e Y).trace) := by
  have hsub1 : sub e (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    ext a b
    simp [sub, Matrix.one_apply, e.injective.eq_iff]
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℂ, f = fun s : ℝ => (sub e (NormedSpace.exp ((s : ℂ) • Y))).det := ⟨_, rfl⟩
  have hpres : ∀ s : ℝ, Pres S (NormedSpace.exp ((s : ℂ) • Y)) := fun s => pres_exp (pres_smul hY _)
  have hmul : ∀ s u : ℝ, f (s + u) = f s * f u := by
    intro s u
    rw [hf]
    simp only
    rw [exp_add_real, hm _ _ (hpres s) (hpres u), Matrix.det_mul]
  have hf0 : f 0 = 1 := by
    rw [hf]
    simp [hsub1]
  have hd0 : HasDerivAt f (sub e Y).trace 0 := by
    rw [hf]
    apply hasDerivAt_det_of_one (fun s : ℝ => sub e (NormedSpace.exp ((s : ℂ) • Y))) (sub e Y)
    · simp [hsub1]
    · intro a b
      have hfun : (fun s : ℝ => sub e (NormedSpace.exp ((s : ℂ) • Y)) a b) =
          fun s : ℝ => (NormedSpace.exp (s • Y)) (e a) (e b) := by
        funext s
        rw [smul_real_eq]
        rfl
      rw [hfun]
      exact hasDerivAt_exp_entry Y (e a) (e b)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (sub e Y).trace := ⟨_, rfl⟩
  rw [← hc] at hd0
  have hd : ∀ s, HasDerivAt f (c * f s) s := by
    intro s
    have h1 : f = fun u => f s * f (u - s) := by
      funext u
      rw [← hmul, add_sub_cancel]
    have h2 : HasDerivAt (fun u => f (u - s)) c s := by
      have h3 := hd0
      rw [← sub_self s] at h3
      exact h3.comp_sub_const s s
    have h4 := h2.const_mul (f s)
    have h5 : HasDerivAt f (f s * c) s :=
      h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => congrFun h1 u)
    rw [mul_comm]
    exact h5
  have hl : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := fun u => Complex.ofRealCLM.hasDerivAt
  have hg : ∀ u : ℝ, HasDerivAt (fun u : ℝ => f u * Complex.exp (-(c * u))) 0 u := by
    intro u
    have he : HasDerivAt (fun u : ℝ => Complex.exp (-(c * u))) (Complex.exp (-(c * u)) * (-c)) u := by
      have h := ((hl u).const_mul c).neg.cexp
      simpa using h
    have := (hd u).mul he
    exact this.congr_deriv (by ring)
  have hconst : ∀ u : ℝ, f u * Complex.exp (-(c * u)) = 1 := by
    intro u
    have := is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) u 0
    rw [this, hf0]
    simp
  have key : f t = Complex.exp (c * t) := by
    have h1 := hconst t
    calc f t = f t * Complex.exp (-(c * t)) * Complex.exp (c * t) := by
          rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = Complex.exp (c * t) := by rw [h1, one_mul]
  have hft : f t = (sub e (NormedSpace.exp ((t : ℂ) • Y))).det := by rw [hf]
  rw [← hft, key, hc, mul_comm]
end PI.UnitaryCorollaryDerivatives.DjC
