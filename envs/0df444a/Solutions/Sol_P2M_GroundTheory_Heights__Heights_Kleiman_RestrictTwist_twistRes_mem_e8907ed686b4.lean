-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_mem_e8907ed686b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:14.820692+00:00
-- url     : https://prove2.me/submissions/e2bbbc65-553f-44ae-9d67-c25cde555b6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_isFrac_46d7eee3b227
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_twistRes_eq_5dea7de76ecb

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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
theorem _root_.solution {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (c : ℤ) (I : Chart y) {q : Ω}
    (hq : q ∈ (twistSys S x c).sub (liftChart hxy I)) : twistRes S x y c q ∈ (twistSys S y c).sub I := by
  obtain ⟨t, ht⟩ := exists_isFrac hq
  rw [twistRes_eq hxy hle I ht]
  exact Submodule.subset_span ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
