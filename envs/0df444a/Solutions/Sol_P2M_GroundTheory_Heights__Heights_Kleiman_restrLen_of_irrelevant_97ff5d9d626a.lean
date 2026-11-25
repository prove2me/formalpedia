-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_restrLen_of_irrelevant_97ff5d9d626a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:14.821042+00:00
-- url     : https://prove2.me/submissions/f336b464-8850-403d-9baa-e7fb67ecc512

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCycleSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (pp : Ideal (Poly S N)) (hX : ∀ i, (X i : Poly S N) ∈ pp)
    (F : SubSystem S x Ω) : restrLen pp F = 0 := by
  have hle : F.secs ≤ (F.twist (idealSys x pp)).secs := by
    intro y hy
    simp only [SubSystem.secs, Submodule.mem_iInf, Submodule.restrictScalars_mem] at hy ⊢
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hX i, X_mem_monos hi, isHomogeneous_X S i,
        isHomogeneous_X S i, by rw [aeval_X, div_self hxi]⟩
    exact Submodule.subset_span ⟨1, h1, y, hy I, (one_smul Ω y).symm⟩
  have hs : Subsingleton (F.secs ⧸ ((F.twist (idealSys x pp)).secs).comap F.secs.subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    intro y _
    exact hle y.2
  unfold restrLen
  rw [Module.length_eq_zero_iff.mpr hs]
  rfl
end GroundTheory.Heights₂.Heights.Kleiman
