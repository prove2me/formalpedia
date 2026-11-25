-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_frame_cover_ac01afdb2b09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:15.861202+00:00
-- url     : https://prove2.me/submissions/5878c8ca-0b95-472a-8579-237503e4c915

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E)
    (hloc : ∀ Q : Ideal A, Q.IsMaximal →
      ∃ h : Ω, ∃ hh : h ∈ A, (⟨h, hh⟩ : A) ∉ Q ∧ IsFrameAt A r M h) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ A) ∧ (∀ l, c l ∈ A) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, IsFrameAt A r M (f l) := by
  let H : Set A := {h | IsFrameAt A r M h}
  have htop : Ideal.span H = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h, hh, hQh, hfr⟩ := hloc Q hQ
    exact hQh (hle (Ideal.subset_span (show (⟨h, hh⟩ : A) ∈ H from hfr)))
  have h1 : (1 : A) ∈ Ideal.span H := by rw [htop]; exact Submodule.mem_top
  obtain ⟨k, c, g, hcg⟩ := Submodule.mem_span_set'.1 h1
  refine ⟨k, fun l => ((g l : A) : Ω), fun l => (c l : Ω), fun l => (g l : A).2, fun l => (c l).2,
    ?_, fun l => (g l).2⟩
  have := congrArg Subtype.val hcg
  simpa using this
end GroundTheory.Heights₂.Heights.Model
