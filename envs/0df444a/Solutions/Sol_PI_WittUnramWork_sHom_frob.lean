-- Prove2me | solution 1 for PI.WittUnramWork.sHom_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:32:55.459603+00:00
-- url     : https://prove2.me/submissions/0ac584fa-4422-42e3-afd2-bd99d041bc9f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittUnramified_GhostComponentG
import Theorems.Thm_PI_WittUnramWork_G_frob
import Theorems.Thm_PI_WittUnramWork_sHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
section Restrict
end Restrict
section Dwork
variable (p Qq) [Invertible (p : Qq)] (F : W →+* W)
variable (hF : ∀ x : W, ∃ y : W, F x = x ^ p + (p : W) * y)
include hF
private theorem map_frobenius' (f : W →+* Qq) (w : WittVector p W) :
    WittVector.map f (frobenius w) = frobenius (WittVector.map f w) := by
  have key : ∀ P : MvPolynomial ℕ ℤ,
      f (MvPolynomial.aeval w.coeff P) = MvPolynomial.aeval (fun i => f (w.coeff i)) P := by
    intro P
    first
      | exact DFunLike.congr_fun (MvPolynomial.comp_aeval (f := w.coeff) f.toIntAlgHom) P
      | exact DFunLike.congr_fun (MvPolynomial.comp_aeval w.coeff f.toIntAlgHom) P
      | (induction P using MvPolynomial.induction_on with
          | C a => simp [MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast, map_intCast]
          | add P Q hP hQ => simp only [map_add, hP, hQ]
          | mul_X P i hP => simp only [map_mul, hP, MvPolynomial.aeval_X])
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_frobenius, WittVector.coeff_frobenius, key]
  congr 1
  try (funext i; exact (WittVector.map_coeff f w i).symm)
end Dwork
end PI.WittUnramWork
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WittUnramWork
open WittVector Finset
variable {p : ℕ} [hp : Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
variable (p Qq) [Invertible (p : Qq)] (F : W →+* W)
variable (hF : ∀ x : W, ∃ y : W, F x = x ^ p + (p : W) * y)
include hF
namespace PI.WittUnramWork
theorem _root_.solution (hinj : Function.Injective (algebraMap W Qq)) (x : W) :
    sHom p Qq F hF hinj (F x) = frobenius (sHom p Qq F hF hinj x) := by
  apply WittVector.map_injective _ hinj
  rw [sHom_apply, map_sFun, G_frob, map_frobenius' p Qq F hF (algebraMap W Qq), sHom_apply, map_sFun]
end PI.WittUnramWork
