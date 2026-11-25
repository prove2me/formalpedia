-- Prove2me | solution 1 for PI.Dv.ProjGramW.idxStd_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:28:11.911314+00:00
-- url     : https://prove2.me/submissions/cda6bebd-d763-486f-ae5c-d5bcb250e255

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_vAdd_mul
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_mul
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_one
import Theorems.Thm_PI_Dv_ProjGramW_idxStd_colOp
import Theorems.Thm_PI_Dv_ProjGramW_colOp_diag
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (D : Fin d → K)
    (hD : ∀ k, D k ≠ 0) : idxStd w (Matrix.diagonal D) = vAdd w (∏ k, D k) := by
  classical
  have key : ∀ s : Finset (Fin d),
      idxStd w (Matrix.diagonal fun k => if k ∈ s then D k else 1) = vAdd w (∏ k ∈ s, D k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty]
      rw [Matrix.diagonal_one, idxStd_one hI]
      simp [vAdd]
    | insert k s hk ih =>
      have e : (Matrix.diagonal fun m => if m ∈ insert k s then D m else 1) =
          (Matrix.diagonal fun m => if m ∈ s then D m else 1) *
            colOp k (fun i => if i = k then D k else 0) := by
        rw [colOp_diag, Matrix.diagonal_mul_diagonal]
        congr 1
        funext m
        by_cases hm : m = k
        · subst hm; simp [hk]
        · simp [hm]
      have hd1 : (Matrix.diagonal fun m => if m ∈ s then D m else 1).det ≠ 0 := by
        rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
        intro m _
        split_ifs
        · exact hD m
        · exact one_ne_zero
      have hd2 : (colOp k (fun i => if i = k then D k else 0)).det ≠ 0 := by
        rw [colOp_diag, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
        intro m _
        split_ifs
        · exact hD k
        · exact one_ne_zero
      have hps : ∏ m ∈ s, D m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => hD m
      rw [e, idxStd_mul hI w _ _ hd1 hd2, ih, idxStd_colOp hI w k _ (by simp [hD k]) hd2,
        Finset.prod_insert hk, vAdd_mul w (hD k) hps]
      simp only [if_true]
      ring
  have := key Finset.univ
  simpa using this
end PI.Dv.ProjGramW
