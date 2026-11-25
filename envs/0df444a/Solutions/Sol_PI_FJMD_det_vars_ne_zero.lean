-- Prove2me | solution 1 for PI.FJMD.det_vars_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:09.506626+00:00
-- url     : https://prove2.me/submissions/1891a5b6-6550-471e-b37c-a8a62298b4de

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM
namespace PI.FJMD
theorem _root_.solution {σ : Type*} {n : ℕ} (f : Fin n × Fin n → σ) (hf : Function.Injective f) :
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)).det ≠ 0 := by
  classical
  intro h0
  have hg : ∀ i j, (if ∃ i', f (i', i') = f (i, j) then (1 : ℂ) else 0) =
      if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos ⟨i, rfl⟩, if_pos rfl]
    · rw [if_neg hij, if_neg]
      rintro ⟨i', hi'⟩
      have hpair := hf hi'
      simp only [Prod.mk.injEq] at hpair
      exact hij (hpair.1.symm.trans hpair.2)
  have hmap : (MvPolynomial.eval (fun x : σ => if ∃ i', f (i', i') = x then (1 : ℂ) else 0)).mapMatrix
      (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.one_apply]
    exact hg i j
  have hdet := RingHom.map_det (MvPolynomial.eval (fun x : σ => if ∃ i', f (i', i') = x then (1 : ℂ) else 0))
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ))
  rw [h0, map_zero, hmap, Matrix.det_one] at hdet
  exact zero_ne_one hdet
end PI.FJMD
