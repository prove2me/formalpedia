-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:26.065435+00:00
-- url     : https://prove2.me/submissions/db888d40-bc23-42d7-945b-1358cfd024c3

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (u : Ideles K) :
    u ∈ rayUnits K ⊤ ∅ ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 := by
  constructor
  · intro h v
    exact (h.2 v).1
  · intro h
    refine ⟨fun w hw => absurd hw (Set.notMem_empty w), fun v => ⟨h v, 1, Submodule.mem_top, ?_⟩⟩
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (((1 : 𝓞 K)) : K)) = 1 := by simp
    rw [h1]
    refine (Valuation.map_sub _ _ _).trans ?_
    simp [h v]
end ReciprocityTheory.Neutral.Bridge.HCFR
