-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_image2_eq_67f8a4da0bc8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:55.157466+00:00
-- url     : https://prove2.me/submissions/a6cc9ba9-f9ff-4f22-a505-97296d2feaf7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (A : Subalgebra S Ω) (T : Set E) :
    Submodule.span S (Set.image2 (· • ·) (A : Set Ω) T) = (Submodule.span A T).restrictScalars S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, y, hy, rfl⟩
    exact Submodule.smul_mem (Submodule.span A T) (⟨a, ha⟩ : A) (Submodule.subset_span hy)
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨1, one_mem A, y, hy, one_smul Ω y⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul a w hw0 hw =>
      clear hw0
      induction hw using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a', ha', y, hy, rfl⟩ := hz
        exact Submodule.subset_span ⟨(a : Ω) * a', mul_mem a.2 ha', y, hy, mul_smul _ _ _⟩
      | zero => rw [smul_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
      | smul s u _ hu =>
        show (a : Ω) • (s • u) ∈ _
        rw [smul_comm]
        exact Submodule.smul_mem _ s hu
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
