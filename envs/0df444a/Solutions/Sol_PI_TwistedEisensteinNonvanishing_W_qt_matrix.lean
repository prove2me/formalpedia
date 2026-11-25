-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:36:08.445942+00:00
-- url     : https://prove2.me/submissions/e0015e8d-c166-4b5c-a402-9a81bd72c342

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_id
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_transvec
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_diag
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_comp
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_congr
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function Matrix
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (M : Matrix ι ι E) (hM : M.det ≠ 0) :
    QT P (fun v => M *ᵥ v) ((qOf P : K) ^ vq P M.det) := by
  classical
  obtain ⟨L, L', D, hMLD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hlist : ∀ l : List (TransvectionStruct ι E),
      QT P (fun v => (l.map TransvectionStruct.toMatrix).prod *ᵥ v) (1 : K) := by
    intro l
    induction l with
    | nil => exact qt_congr qt_id (fun v => by simp) rfl
    | cons t l ih =>
      refine qt_congr (qt_comp (qt_transvec hN hp hq hK t) ih) (fun v => by simp [Matrix.mulVec_mulVec]) ?_
      rw [t.det, vq_one, zpow_zero, one_mul]
      all_goals assumption
  have hl1 : ∀ l : List (TransvectionStruct ι E), ((l.map TransvectionStruct.toMatrix).prod).det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => simp [Matrix.det_mul, t.det, ih]
  have hdetM : M.det = (diagonal D).det := by
    rw [hMLD, Matrix.det_mul, Matrix.det_mul, hl1, hl1, one_mul, mul_one]
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    apply hM
    rw [hdetM, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  refine qt_congr (qt_comp (hlist L) (qt_comp (qt_diag hN hp hq hK D hD) (hlist L')))
    (fun v => by rw [hMLD]; simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]) ?_
  rw [hdetM, one_mul, mul_one]
end PI.TwistedEisensteinNonvanishing.W
