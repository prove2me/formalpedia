-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P10.familiesOfMaps
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:57:26.319294+00:00
-- url     : https://prove2.me/submissions/a27dee15-fe1b-4c34-84ac-6ab02c053808
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P10_properAffineTransport
noncomputable section

open Set Filter MeasureTheory TopologicalSpace

open scoped Topology ENNReal BigOperators

universe u v w

open QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Dependency50.P25

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Frontier18.P10.paperBorel

section LocallyConvexResults

variable {E : Type u} [UniformSpace E] [AddCommGroup E] [Module ℝ E]
    [hgroup : IsUniformAddGroup E] [hsmul : ContinuousSMul ℝ E]
    [hlc : LocallyConvexSpace ℝ E] [hhaus : T2Space E]

include hgroup hsmul hlc hhaus

/-- Corollary 1, PDF p.6: the ambient locally convex space is represented
as a linear space of maps by an injective linear realization. Only sequential
continuity of evaluation at x0 and relatively compact evaluation preimages
are assumed. No compactness of each fiber is an input hypothesis. -/
theorem solution {X : Type v} {Y : Type w}
    [UniformSpace Y] [AddCommGroup Y] [Module ℝ Y] [IsUniformAddGroup Y]
    [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] [T2Space Y]
    (realize : E →ₗ[ℝ] (X → Y)) (hinj : Function.Injective realize)
    (F0 : Set E) (hF0 : GeneralBarycenterSpace F0) (hcF0 : Convex ℝ F0)
    (A : Set Y) (hA : GeneralBarycenterSpace A) (hcA : Convex ℝ A)
    (hmA : MuCompact A) (hvalues : ∀ f ∈ F0, ∀ x, realize f x ∈ A)
    (x0 : X)
    (hseq : ∀ (f : ℕ → F0) (f0 : F0), Tendsto f atTop (𝓝 f0) →
      Tendsto (fun n => realize (f n) x0) atTop (𝓝 (realize f0 x0)))
    (hrel : ∀ C : Set Y, C ⊆ A → IsCompact C →
      IsCompact (closure {f ∈ F0 | realize f x0 ∈ C})) :
    MuCompact F0 := by
  let : MetrizableSpace (closedConvexHull ℝ F0) := hF0.2.2.2.2
  let : MetrizableSpace F0 :=
    (Topology.IsEmbedding.inclusion (show F0 ⊆ closedConvexHull ℝ F0 from subset_closedConvexHull)).metrizableSpace
  have heval : Continuous (fun f : F0 => realize (f : E) x0) :=
    (show SeqContinuous (fun f : F0 => realize (f : E) x0) from hseq).continuous
  have hcont : ContinuousOn (fun f : E => realize f x0) F0 :=
    continuousOn_iff_continuous_domRestrict.mpr heval
  have haff : AffineOnSet F0 (fun f : E => realize f x0) := by
    intro f hf g hg a b ha hb hab
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  have hproper : ∀ C : Set Y, C ⊆ A → IsCompact C →
      IsCompact {f ∈ F0 | realize f x0 ∈ C} := by
    intro C hCA hC
    have hclosed : IsClosed {f ∈ F0 | realize f x0 ∈ C} :=
      hcont.preimage_isClosed_of_isClosed hF0.1 hC.isClosed
    exact (hrel C hCA hC).of_isClosed_subset hclosed subset_closure
  exact (properAffineTransport F0 A hF0 hA hcF0 hcA
    (fun f : E => realize f x0) hcont haff (fun f hf => hvalues f hf x0) hproper).1 hmA

end LocallyConvexResults



end
