-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_closed_of_sat_fdb838e20b19
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:15.020056+00:00
-- url     : https://prove2.me/submissions/6cf30fc5-d852-491a-b49c-219b1ef59346

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable [IsAlgClosure E Ω]
attribute [instance] Test.grp Test.fin
omit [NumberField E] [IsAlgClosure E Ω]
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution (t : Test E Ω) (X : Set (G E Ω))
    (h : ∀ σ σ', t.φ σ = t.φ σ' → σ ∈ X → σ' ∈ X) : IsClosed X := by
  let _ : TopologicalSpace t.A' := ⊥
  have : DiscreteTopology t.A' := ⟨rfl⟩
  have hc : Continuous t.φ := by
    refine continuous_of_continuousAt_one t.φ ?_
    rw [ContinuousAt, map_one, nhds_discrete t.A', Filter.tendsto_pure]
    exact t.ho.mem_nhds (one_mem t.φ.ker)
  have : X = t.φ ⁻¹' (t.φ '' X) :=
    Set.Subset.antisymm (Set.subset_preimage_image _ _) fun σ' ⟨σ, hσ, e⟩ => h σ σ' e hσ
  rw [this]
  exact (isClosed_discrete _).preimage hc
end Formalism.BasicNotions.Examples₂.Tame
