-- Prove2me | solution 1 for PI.IsoFunVW.key_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:12:13.569591+00:00
-- url     : https://prove2.me/submissions/ee429b59-43fe-4c1f-a16c-fbbe00e22fc5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoFunV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_DetSubmatrixNoninj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryFunctionSpace_InstFintypeOE
import Theorems.Thm_PI_IsoFunVW_minY_map
import Theorems.Thm_PI_IsoFunVW_prod_sum_cc
import Theorems.Thm_PI_IsoFunVW_det_mul_eq_sum_oe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MvPolynomial
noncomputable section
open PI PI.IsoFunVW
open PI.IsoFunV
namespace PI.IsoFunVW
theorem _root_.solution {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (x : Lt → Fin N → ℕ → ℂ) (I : ColChoice N' nu) :
    ∑ J : ColChoice N nu, PIJ tp nu s I J * C (minY N nu J x) = minY N' nu I (yfr tp s x) := by
  have hR : ∀ J : ColChoice N nu, PIJ tp nu s I J * C (minY N nu J x) =
      ∏ z, ∏ c : Fin ((nu z).rowLen 0),
        (Matrix.of fun i k : Fin ((nu z).colLen c) =>
          C (s (tp z)) * X ((tp z, I z c i, J z c k) : Idx T N N')).det *
        (Matrix.of fun i j : Fin ((nu z).colLen c) =>
          (C (x z (J z c i) (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)).det := by
    intro J
    rw [minY_map]
    simp only [PIJ, minY, ← Finset.prod_mul_distrib]
  have hL : minY N' nu I (yfr tp s x) = ∏ z, ∏ c : Fin ((nu z).rowLen 0),
      ∑ Jc : Fin ((nu z).colLen c) ↪o Fin N,
        (Matrix.of fun i k : Fin ((nu z).colLen c) =>
          C (s (tp z)) * X ((tp z, I z c i, Jc k) : Idx T N N')).det *
        (Matrix.of fun i j : Fin ((nu z).colLen c) =>
          (C (x z (Jc i) (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)).det := by
    simp only [minY]
    refine Finset.prod_congr rfl (fun z _ => Finset.prod_congr rfl (fun c _ => ?_))
    have hcb := det_mul_eq_sum_oe
      (Matrix.of fun (i : Fin ((nu z).colLen c)) (b : Fin N) =>
        C (s (tp z)) * X ((tp z, I z c i, b) : Idx T N N'))
      (Matrix.of fun (b : Fin N) (j : Fin ((nu z).colLen c)) =>
        (C (x z b (j : ℕ)) : MvPolynomial (Idx T N N') ℂ))
    have hm : (Matrix.of fun i j : Fin ((nu z).colLen c) => yfr tp s x z (I z c i) (j : ℕ)) =
        (Matrix.of fun (i : Fin ((nu z).colLen c)) (b : Fin N) =>
          C (s (tp z)) * X ((tp z, I z c i, b) : Idx T N N')) *
        (Matrix.of fun (b : Fin N) (j : Fin ((nu z).colLen c)) =>
          (C (x z b (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.of_apply, yfr]
    rw [hm, hcb]
    rfl
  rw [hL, prod_sum_cc]
  exact Finset.sum_congr rfl (fun J _ => hR J)
end PI.IsoFunVW
