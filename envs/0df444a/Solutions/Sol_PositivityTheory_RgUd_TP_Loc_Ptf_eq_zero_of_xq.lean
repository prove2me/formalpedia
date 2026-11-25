-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.eq_zero_of_xq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:38.460427+00:00
-- url     : https://prove2.me/submissions/9abb95cf-e0e4-48de-b095-ac306173fa20

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight
import Theorems.Thm_PositivityTheory_RgUd_TP_Loc_Ptf_sum_eI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Loc PositivityTheory.RgUd.TP.Loc.Ptf
open Classical
attribute [local instance] Ideal.Quotient.field
variable {k R V : Type*} [Field k] [CommRing R] [IsArtinianRing R] [IsReduced R] [Algebra k R]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V]
namespace PositivityTheory.RgUd.TP.Loc.Ptf
theorem _root_.solution (x : V →ₗ[R] V) (h : ∀ I : MaximalSpectrum R, xq I.asIdeal x = 0) : x = 0 := by
  ext v
  have hv : ∀ I : MaximalSpectrum R, x v ∈ I.asIdeal • (⊤ : Submodule R V) := fun I => by
    rw [← Submodule.Quotient.mk_eq_zero, ← xq_mk, h I, LinearMap.zero_apply]
  rw [LinearMap.zero_apply, ← one_smul R (x v), ← sum_eI, Finset.sum_smul]
  exact Finset.sum_eq_zero fun I _ => eI_smul_eq_zero I (hv I)
end PositivityTheory.RgUd.TP.Loc.Ptf
