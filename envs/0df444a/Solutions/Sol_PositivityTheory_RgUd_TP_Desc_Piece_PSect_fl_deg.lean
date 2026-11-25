-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:18.254512+00:00
-- url     : https://prove2.me/submissions/e8c31542-6bc9-4cd7-84db-78dc0a41b49b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_MemPw
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FieldGen
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_map_top_Pj
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_mem_Pj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {k E : Type*} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [CharP E p]
    (hroot : ∀ a : k, ∃ w : E, w ^ (p ^ c) = algebraMap k E a) :
    (Pj E p c).relfinrank ⊤ = finrank k (Tw k p c) := by
  set f := algebraMap k E with hf
  set Fr := iterateFrobenius E p c with hFr
  set K : Subfield E := f.fieldRange with hK
  set Kq : Subfield E := (Fr.comp f).fieldRange with hKq
  have hmapK : K.map Fr = Kq := RingHom.map_fieldRange _ _
  have hmapT : (⊤ : Subfield E).map Fr = Pj E p c := map_top_Pj p c
  have h3 : Kq.relfinrank (Pj E p c) = K.relfinrank ⊤ := by
    rw [← hmapK, ← hmapT, Subfield.relfinrank_map_map]
  have h4 : Kq ≤ K := by
    intro y hy
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.1 hy
    exact RingHom.mem_fieldRange.2 ⟨a ^ p ^ c, by rw [RingHom.comp_apply, hFr, iterateFrobenius_def, map_pow]⟩
  have h5 : K ≤ Pj E p c := by
    intro y hy
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.1 hy
    obtain ⟨w, hw⟩ := hroot a
    exact (mem_Pj p).2 ⟨w, hw⟩
  have hA := Subfield.relfinrank_mul_relfinrank h4 (le_top : K ≤ ⊤)
  have hB := Subfield.relfinrank_mul_relfinrank (h4.trans h5) (le_top : Pj E p c ≤ ⊤)
  have hKtop : K.relfinrank ⊤ = finrank k E := by
    have := IntermediateField.relfinrank_bot_left (⊤ : IntermediateField k E)
    rw [IntermediateField.finrank_top'] at this
    rw [← this, IntermediateField.relfinrank, IntermediateField.bot_toSubfield,
      IntermediateField.top_toSubfield]
  have hpos : 0 < K.relfinrank ⊤ := hKtop ▸ Module.finrank_pos
  have h9 : Kq.relfinrank K = finrank k (Tw k p c) := by
    rw [Subfield.relfinrank_eq_finrank_of_le h4]
    symm
    refine Algebra.finrank_eq_of_equiv_equiv (Fr.comp f).rangeRestrictFieldEquiv
      (f.rangeRestrictFieldEquiv.trans
        (RingEquiv.subfieldCongr (Subfield.extendScalars_toSubfield h4).symm)) ?_
    ext a
    show (((Fr.comp f).rangeRestrictFieldEquiv a : Kq) : E) = f (iterateFrobenius k p c a)
    rw [RingHom.rangeRestrictFieldEquiv_apply_coe, RingHom.comp_apply, hFr, iterateFrobenius_def,
      iterateFrobenius_def, map_pow]
  rw [h3] at hB
  rw [← h9]
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hB, ← hA, mul_comm]
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
