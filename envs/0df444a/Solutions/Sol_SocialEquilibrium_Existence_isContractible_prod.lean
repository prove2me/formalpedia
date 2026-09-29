-- Prove2me | solution 1 for SocialEquilibrium.Existence.isContractible_prod
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:25:09.68324+00:00
-- url     : https://prove2.me/submissions/add36bf4-d306-4344-a10a-e6086e5a0955

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsContractible

namespace SocialEquilibrium.Existence

open unitInterval

/-- Pairing of two deformations. -/
def aux_icp_pair {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {X : Set E} {Y : Set F} (H1 : C(I × X, X)) (H2 : C(I × Y, Y)) :
    C(I × ↥(X ×ˢ Y), ↥(X ×ˢ Y)) where
  toFun p := ⟨((H1 (p.1, ⟨p.2.1.1, p.2.2.1⟩)).1, (H2 (p.1, ⟨p.2.1.2, p.2.2.2⟩)).1),
    (H1 (p.1, ⟨p.2.1.1, p.2.2.1⟩)).2, (H2 (p.1, ⟨p.2.1.2, p.2.2.2⟩)).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply continuous_subtype_val.comp
      apply H1.continuous.comp
      apply Continuous.prodMk continuous_fst
      apply Continuous.subtype_mk
      exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    · apply continuous_subtype_val.comp
      apply H2.continuous.comp
      apply Continuous.prodMk continuous_fst
      apply Continuous.subtype_mk
      exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} (x₀ : X) (y₀ : Y)
    (hX : IsDeformableInto X x₀) (hY : IsDeformableInto Y y₀) :
    IsDeformableInto (X ×ˢ Y) ⟨(x₀.1, y₀.1), x₀.2, y₀.2⟩ := by
  obtain ⟨H1, h10, h11⟩ := hX
  obtain ⟨H2, h20, h21⟩ := hY
  refine ⟨aux_icp_pair H1 H2, ?_, ?_⟩
  · intro z
    apply Subtype.ext
    simp only [aux_icp_pair, ContinuousMap.coe_mk, h10, h20]
  · intro z
    apply Subtype.ext
    simp only [aux_icp_pair, ContinuousMap.coe_mk, h11, h21]
