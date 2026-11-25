-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_transvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:42.215014+00:00
-- url     : https://prove2.me/submissions/059161cb-f733-4ce8-8f38-930196fd8a06

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_congr
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_em


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
theorem _root_.solution (t : TransvectionStruct ι E) :
    QT P (fun v => t.toMatrix *ᵥ v) ((qOf P : K) ^ vq P t.toMatrix.det) := by
  have hmv : ∀ v : ι → E, t.toMatrix *ᵥ v = em t.i t.j 1 t.c 0 v := by
    intro v
    funext k
    by_cases h : k = t.i
    · subst h
      simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
        Matrix.single_mulVec, em] <;> ring
    · simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_mulVec,
        Matrix.single_mulVec, em, h]
  exact qt_congr (qt_em hN hp hq hK t.i t.j one_ne_zero t.c 0 (Or.inl t.hij.symm)) hmv (by rw [t.det])
end PI.TwistedEisensteinNonvanishing.W
