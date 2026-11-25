-- Prove2me | solution 1 for P2M_GlobalTheory_SatMinor_exists_minor_ne_zero__d04f3c26b9e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:10.259821+00:00
-- url     : https://prove2.me/submissions/bc23f4db-0b76-4464-bbce-fafae7eaec33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SatMinor
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.SatMinor
theorem _root_.solution {K : Type} [Field K] {κ J : Type} [Fintype κ] [DecidableEq κ] [Fintype J]
    (M : Matrix κ J K) (hM : LinearIndependent K M.row) :
    ∃ f : κ → J, Function.Injective f ∧ (M.submatrix id f).det ≠ 0 := by
  classical
  obtain ⟨ι, b, hb, hsp, hli⟩ := exists_linearIndependent' K M.col
  have : Finite ι := Finite.of_injective b hb
  let : Fintype ι := Fintype.ofFinite ι
  have hι : Fintype.card ι = Fintype.card κ := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix]
  let e : κ ≃ ι := (Fintype.equivOfCardEq hι).symm
  have h1 : LinearIndependent K (M.submatrix id (b ∘ e)).col := hli.comp e e.injective
  exact ⟨b ∘ e, hb.comp e.injective,
    ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 h1)).ne_zero⟩
end GlobalTheory.SatMinor
