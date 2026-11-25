-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_Rw__506400027688
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:38.123914+00:00
-- url     : https://prove2.me/submissions/b64b09b2-cbb0-4297-ba4c-fadbfc339727

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_JFxI_ckOn_RdV__1ba0d0d897b8
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxI
theorem _root_.solution {UU : Set (Mat k r)} {f : Mat k r → E} {N : ℕ} (h : CkOn (N : ℕ∞) UU f) (w : List (Mat k r))
    (hw : ∀ X ∈ w, inLie k r X) (m : ℕ) (hle : m + w.length ≤ N) : CkOn (m : ℕ∞) UU (Rw w f) := by
  have key : ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ m : ℕ, m + w.length ≤ N →
      CkOn (m : ℕ∞) UU (Rw w f) := by
    intro w
    induction w with
    | nil =>
      intro _ m hle
      intro g₀ hg
      obtain ⟨U, f', hU, hgU, hf', hff⟩ := h g₀ hg
      exact ⟨U, f', hU, hgU, hf'.of_le (by norm_cast <;> simpa using hle), hff⟩
    | cons X w ih =>
      intro hw m hle
      have hX : inLie k r X := hw X (by simp)
      have h1 := ih (fun Y hY => hw Y (by simp [hY])) (m + 1) (by simp at hle; omega)
      have h2 : CkOn ((m : ℕ∞) + 1) UU (Rw w f) := by exact_mod_cast h1
      exact ckOn_RdV' hX h2
  exact key w hw m hle
end Formalism.FourierDecayAlt.P.JFxI
