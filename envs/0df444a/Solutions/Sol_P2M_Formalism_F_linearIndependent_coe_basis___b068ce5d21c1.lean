-- Prove2me | solution 1 for P2M_Formalism_F_linearIndependent_coe_basis___b068ce5d21c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:07.717837+00:00
-- url     : https://prove2.me/submissions/d97e3854-5232-4a56-b7ea-abc5f3cd9c11

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_GramDetLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopeInequality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.F
universe u v
private theorem finrank_int_eq_finrank_real_span {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (Submodule.span ℝ (L : Set E)) := by

  have hsub : ∀ x ∈ L, x ∈ Submodule.span ℝ (L : Set E) := fun x hx => Submodule.subset_span hx
  let L₀ : Submodule ℤ (Submodule.span ℝ (L : Set E)) :=
    L.comap ((Submodule.span ℝ (L : Set E)).subtype.restrictScalars ℤ)
  let e : L₀ ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : Submodule.span ℝ (L : Set E)) : E), x.2⟩
      invFun := fun y => ⟨⟨y, hsub y y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L₀ := by
    refine DiscreteTopology.of_continuous_injective (f := e) ?_ e.injective
    exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  have himg : (Submodule.span ℝ (L : Set E)).subtype '' (L₀ : Set _) = (L : Set E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub x hx⟩, hx, rfl⟩
  haveI : IsZLattice ℝ L₀ := by
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (Submodule.span ℝ (L : Set E)).injective_subtype
    rw [Submodule.map_span, himg, Submodule.map_top, Submodule.range_subtype]
  rw [← e.finrank_eq, ZLattice.rank ℝ L₀]
end Formalism.F
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u v
namespace Formalism.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (b i : E)) := by
  classical
  have h1 : Submodule.span ℤ (Set.range (fun i => (b i : E))) = L := by
    have := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hspan : Submodule.span ℝ (Set.range (fun i => (b i : E))) =
      Submodule.span ℝ (L : Set E) := by
    have h2 := Submodule.span_span_of_tower ℤ ℝ (Set.range (fun i => (b i : E)))
    rw [h1] at h2
    exact h2.symm
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspan, ← finrank_int_eq_finrank_real_span L,
    Module.finrank_eq_card_basis b]
end Formalism.F
