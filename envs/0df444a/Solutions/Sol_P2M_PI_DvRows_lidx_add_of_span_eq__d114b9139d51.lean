-- Prove2me | solution 1 for P2M_PI_DvRows_lidx_add_of_span_eq__d114b9139d51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:29.536425+00:00
-- url     : https://prove2.me/submissions/c8d0909d-774c-47f0-a326-e838f896ea52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_P2M_PI_DvRows_le_locS_of_span_le__2805ff1ab53c
import Theorems.Thm_P2M_PI_DvRows_length_ne_top_of_le_locS__f6d46dbe9ad4
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_lidx_via
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.DvRows
theorem _root_.solution [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (p : Ideal R) [p.IsPrime]
    (A B C : Submodule R V) (hA : A.FG) (hB : B.FG) (hC : C.FG)
    (hAB : Submodule.span K (A : Set V) = Submodule.span K (B : Set V))
    (hBC : Submodule.span K (B : Set V) = Submodule.span K (C : Set V)) :
    lidx p A C = lidx p A B + lidx p B C := by
  have hD : ∀ X : Submodule R V, Submodule.span K (X : Set V) = Submodule.span K (A : Set V) →
      X ≤ locS (nonZeroDivisors R) (A ⊓ B ⊓ C) := by
    intro X hX
    rw [locBasic_locS_inf, locBasic_locS_inf]
    exact le_inf (le_inf (le_locS_of_span_le' (K := K) X A hX.le)
      (le_locS_of_span_le' (K := K) X B (hX.trans hAB).le))
      (le_locS_of_span_le' (K := K) X C (hX.trans (hAB.trans hBC)).le)
  have hAD := length_ne_top_of_le_locS' p A _ hA (hD A rfl)
  have hBD := length_ne_top_of_le_locS' p B _ hB (hD B hAB.symm)
  have hCD := length_ne_top_of_le_locS' p C _ hC (hD C (hAB.trans hBC).symm)
  rw [indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right
      hAD hCD,
    indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right
      hBD hCD]
  ring
end PI.DvRows
