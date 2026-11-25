-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.exists_equiv_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:10.886378+00:00
-- url     : https://prove2.me/submissions/c8155b1c-91b3-4a32-ab39-ad829d8d9234

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_exists_equiv_of_torsion
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_pidem_idem
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_mul_pidem_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
universe u
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
theorem _root_.solution {k A : Type*} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    [IsReduced A] (M M' : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M'] [FiniteDimensional k M]
    [FiniteDimensional k M']
    (h : ∀ e : A, IsIdempotentElem e → finrank k (piece M e) = finrank k (piece M' e)) :
    Nonempty (M ≃ₗ[A] M') := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have tor : ∀ (P : Type u) [AddCommGroup P] [Module A P] (I : MaximalSpectrum A),
      Module.IsTorsionBySet A (piece P (pidem A I)) I.asIdeal := by
    intro P _ _ I y a
    obtain ⟨y, m, rfl⟩ := y
    ext
    simp [smul_smul, mul_pidem_of_mem I a.2]
  have fd : ∀ (P : Type u) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
      [FiniteDimensional k P] (e : A), FiniteDimensional k (piece P e) := fun P _ _ _ _ _ e =>
    Module.Finite.of_injective ((piece P e).subtype.restrictScalars k) Subtype.val_injective
  have T : ∀ I : MaximalSpectrum A, Nonempty (piece M (pidem A I) ≃ₗ[A] piece M' (pidem A I)) := fun I =>
    haveI := fd M (pidem A I)
    haveI := fd M' (pidem A I)
    exists_equiv_of_torsion I.asIdeal _ _ (tor M I) (tor M' I) (h _ (pidem_idem I))
  exact ⟨(decomp M).trans ((LinearEquiv.piCongrRight fun I => (T I).some).trans (decomp M').symm)⟩
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
