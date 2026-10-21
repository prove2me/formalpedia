-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P04.convex_submodule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:24:43.071985+00:00
-- url     : https://prove2.me/submissions/b21f6341-74e0-4bbd-a885-fe10e5257b99

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04
open QAlgorithms.Papers.Independent.Claimed50.P04
noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section Modules

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem g58c_antisymm' {E : Type*} [AddCommGroup E] [Module ℝ E]
    (b : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (halt : ∀ v, b v v = 0) (v w : E) : b v w = - b w v := by
  have := halt (v + w)
  simp [halt v, halt w] at this
  exact eq_neg_of_add_eq_zero_left this

/-- Lemma 2.16, PDF p. 9: restriction to EVERY submodule preserves convex symplecticity. -/
theorem solution (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : SymplecticModule rho omega)
    (hc : StrictConvexType rho omega) (W : Submodule ℝ V) (hw : Stable rho W) :
    NondegenerateOn omega W ∧ ConvexOn rho omega W := by
  obtain ⟨⟨halt, _⟩, hpres⟩ := hs
  obtain ⟨x, hx⟩ := hc
  refine ⟨?_, ⟨x, fun v _ hv => hx v hv⟩⟩
  intro v hvW hv
  by_contra hne
  have h1 := hx v hne
  have h2 := hv (rho x v) (hw x v hvW)
  rw [g58c_antisymm' omega halt] at h1
  linarith

end Modules

end

