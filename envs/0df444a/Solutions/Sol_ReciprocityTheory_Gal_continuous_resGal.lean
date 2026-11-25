-- Prove2me | solution 1 for ReciprocityTheory.Gal.continuous_resGal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:53.838452+00:00
-- url     : https://prove2.me/submissions/1133944f-3ac0-4fd6-8ee2-d668d6a0e104

import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_ReciprocityTheory_Hypotheses_Descent
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalEA
import Theorems.Thm_ReciprocityTheory_Gal_resGal_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Gal.resGal_apply

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp
variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution [Algebra.IsAlgebraic F Ω] : Continuous (resGal F L Ω) := by
  refine continuous_of_continuousAt_one (resGal F L Ω) ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  let S : Set Ω := Set.range (fun i => (b i : Ω))
  have hint : ∀ x ∈ S, IsIntegral L x := fun x _ =>
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  have : FiniteDimensional L (IntermediateField.adjoin L S) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin L S, this, fun σ hσ => hEs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, σ (b i : Ω) = b i := fun i =>
    hσ _ (IntermediateField.subset_adjoin L S ⟨i, rfl⟩)
  intro x hx
  have hx' : x = ((⟨x, hx⟩ : E) : Ω) := rfl
  rw [hx', ← b.sum_repr ⟨x, hx⟩]
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul]
  change resGal F L Ω σ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change σ (((b.repr ⟨x, hx⟩) i) • (b i : Ω)) = _
  rw [← algebraMap_smul L ((b.repr ⟨x, hx⟩) i) (b i : Ω), map_smul, hb]
end ReciprocityTheory.Gal
