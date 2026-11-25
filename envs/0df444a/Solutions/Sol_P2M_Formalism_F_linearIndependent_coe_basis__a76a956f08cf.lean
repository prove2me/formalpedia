-- Prove2me | solution 1 for P2M_Formalism_F_linearIndependent_coe_basis__a76a956f08cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:08.630796+00:00
-- url     : https://prove2.me/submissions/67953071-e515-420d-ba8e-058b7d9e0cd9

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd
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
universe u
private theorem finrank_int_eq_finrank_span_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] :
    Module.finrank ℤ L = Module.finrank ℝ (span ℝ (L : Set E)) := by

  let V := span ℝ (L : Set E)
  let L' : Submodule ℤ V := L.comap (V.subtype.restrictScalars ℤ)
  let φ : L' ≃ₗ[ℤ] L :=
    { toFun := fun x => ⟨((x : V) : E), x.2⟩
      invFun := fun y => ⟨⟨y, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : DiscreteTopology L' :=
    DiscreteTopology.of_continuous_injective
      (f := fun x : L' => (⟨((x : V) : E), x.2⟩ : L))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun a b h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  haveI : IsZLattice ℝ L' := ⟨Submodule.span_span_coe_preimage⟩
  exact φ.finrank_eq.symm.trans (ZLattice.rank ℝ L')
end Formalism.F
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u
namespace Formalism.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [hL : DiscreteTopology L] {ι : Type*} [Fintype ι]
    (e : Basis ι ℤ L) : LinearIndependent ℝ (fun i => (e i : E)) := by
  have hspanZ : span ℤ (Set.range fun i => (e i : E)) = L := by
    have : (Set.range fun i => (e i : E)) = L.subtype '' Set.range e := Set.range_comp _ _
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_subtype_top]
  have hspanR : span ℝ (Set.range fun i => (e i : E)) = span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (e i : E)), hspanZ]
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanR, ← finrank_int_eq_finrank_span_real L,
    Module.finrank_eq_card_basis e]
end Formalism.F
