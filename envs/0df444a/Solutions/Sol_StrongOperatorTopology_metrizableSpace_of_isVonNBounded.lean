-- Prove2me | solution 1 for StrongOperatorTopology.metrizableSpace_of_isVonNBounded
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:31:38.340607+00:00
-- url     : https://prove2.me/submissions/a8dddd82-6603-438e-99db-df01bcef8d79

import Mathlib

open Filter Topology
set_option autoImplicit false


theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (S : Set (H →Lₚₜ[ℂ] H)) (hS : Bornology.IsVonNBounded ℂ S) :
    TopologicalSpace.MetrizableSpace S := by
  -- each orbit `{T x | T ∈ S}` is bounded in `H`
  have hbounded (x : H) :
      Bornology.IsVonNBounded ℂ (Set.range fun T : S ↦ T.val x) := by
    let ev := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H x
    change Bornology.IsVonNBounded ℂ (Set.range (ev ∘ (Subtype.val : S → _)))
    rw [Set.range_comp, Subtype.range_coe]
    exact hS.image ev
  -- uniform boundedness principle: the family is equicontinuous
  have heq := (PolynormableSpace.banach_steinhaus
    (𝓕 := fun T : S ↦ (T.val : H →L[ℂ] H)) hbounded).equicontinuous
  -- restriction to a dense sequence
  let restrict (T : S) (n : ℕ) : H := T.val (TopologicalSpace.denseSeq H n)
  have hcont : Continuous restrict := continuous_pi fun n ↦
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) H
      (TopologicalSpace.denseSeq H n)).continuous.comp continuous_subtype_val
  have hind : Topology.IsInducing restrict := by
    rw [Topology.isInducing_iff_nhds]
    intro T
    refine le_antisymm (hcont.tendsto T).le_comap (tendsto_id'.mp ?_)
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
    intro x
    have hclosed := heq.isClosed_setOfPred_tendsto
      (l := comap restrict (𝓝 (restrict T))) (T.val : H →L[ℂ] H).continuous
    apply hclosed.closure_subset_iff.mpr ?_ (TopologicalSpace.denseRange_denseSeq H x)
    rintro _ ⟨n, rfl⟩
    exact tendsto_pi_nhds.mp (tendsto_comap (f := restrict) (x := 𝓝 (restrict T))) n
  let : TopologicalSpace.PseudoMetrizableSpace S := hind.pseudoMetrizableSpace
  infer_instance
