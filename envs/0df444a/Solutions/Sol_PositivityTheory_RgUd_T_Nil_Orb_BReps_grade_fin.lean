-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:26.253226+00:00
-- url     : https://prove2.me/submissions/a2a63852-cc1c-441b-ae25-61e92b2fa0cb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_GradeColMatMulVec
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_gradeColMat_mulVec
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_grade_mat_ext
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_grade_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Submodule
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {k : Type} [Field k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → ℤ)
    (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k)
    (hZ : ∀ z ∈ Z, ∀ j, z *ᵥ b j ∈ span k (b '' {j' | w j' = w j}))
    (hN : ∀ j, N *ᵥ b j ∈ span k (b '' {j' | w j' = w j + 1}))
    (hv : v ∈ span k (b '' {j | w j = 0}))
    (hA : ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
      ∀ j, w j < 0 → b.repr (a *ᵥ v) j = 0) :
    (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k :=
          (gradeBasisGL b).val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * (gradeBasisGL b)⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * N = (t : k) • (N * g) ∧ g *ᵥ v = v) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * N = N * a →
        ∃ u : Fin n → k, a *ᵥ v = (gradeBasisGL b).val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0 := by
  classical
  refine ⟨fun t => ?_, fun a ha haN => ?_⟩
  · intro g
    have hrow : ∀ j, gradeRowMat b *ᵥ b j = Pi.single j 1 := by
      intro j
      have h1 : gradeColMat b *ᵥ Pi.single j 1 = b j := by
        rw [gradeColMat_mulVec]
        simp [Pi.single_apply]
      rw [← h1, Matrix.mulVec_mulVec]
      show (b.toMatrix (Pi.basisFun k (Fin n)) * (Pi.basisFun k (Fin n)).toMatrix b) *ᵥ _ = _
      rw [Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.one_mulVec]
    have hgdef : g = gradeColMat b * diagonal (fun i => ((t ^ w i : kˣ) : k)) * gradeRowMat b := rfl
    clear_value g
    have hg : ∀ j, g *ᵥ b j = ((t ^ w j : kˣ) : k) • b j := by
      intro j
      rw [hgdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hrow, gradeColMat_mulVec]
      simp [Matrix.mulVec_diagonal, Pi.single_apply]
    refine ⟨fun a ha => ?_, ?_, ?_⟩
    · apply grade_mat_ext b
      intro j
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul]
      rw [grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j' | w j' = w j} _ (fun i hi => by rw [hi]) _ (hZ a ha j)]
    · apply grade_mat_ext b
      intro j
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hg, Matrix.mulVec_smul,
        grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j' | w j' = w j + 1} (((t ^ (w j + 1) : kˣ) : k))
          (fun i hi => by rw [hi]) _ (hN j), smul_smul, _root_.zpow_add_one, Units.val_mul, Units.val_zpow_eq_zpow_val,
        mul_comm]
    · rw [grade_eig b g (fun i => ((t ^ w i : kˣ) : k)) hg {j | w j = 0} 1 (fun i hi => by rw [hi]; simp) v hv, one_smul]
  · refine ⟨⇑(b.repr (a *ᵥ v)), ?_, fun i hi => hA a ha haN i hi⟩
    simp only [gradeBasisGL]
    rw [gradeColMat_mulVec, b.sum_repr]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
