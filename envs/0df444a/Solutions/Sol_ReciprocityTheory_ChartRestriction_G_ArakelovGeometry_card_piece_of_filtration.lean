-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_of_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:20.309956+00:00
-- url     : https://prove2.me/submissions/014a67e2-0b67-459e-be4b-d35ae5004828

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_piece_colon_exact
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_piece_top_ideal
import Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomogIdeal_sup_span_844f7f9a9bdb87ce


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι)
    (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)), IsMultiHomogIdeal (F 0) →
    F (Fin.last N) = ⊤ →
    (∀ j, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    ∀ a : K → ℕ, (∀ j, c j ≤ a) →
      Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j))
  | 0, F, f, c, q, _, hl, _, a, _ => by
    have : F 0 = ⊤ := hl
    rw [Finset.univ_eq_empty, Finset.prod_empty, this, card_piece_top_ideal]
  | N + 1, F, f, c, q, h0, hl, hs, a, ha => by
    obtain ⟨hf0, hF1, hq0⟩ := hs 0
    rw [Fin.castSucc_zero] at hF1 hq0
    have e1 := card_piece_colon_exact h0 hf0 hq0 (ha 0)
    rw [← hF1] at e1
    have h0' : IsMultiHomogIdeal (F (Fin.succ 0)) := by
      rw [hF1]
      exact isMultiHomogIdeal_sup_span h0 hf0
    have ih := solution N (fun i => F i.succ) (fun j => f j.succ) (fun j => c j.succ)
      (fun j => q j.succ) h0' (by simp only [Fin.succ_last]; exact hl)
      (fun j => by
        obtain ⟨x1, x2, x3⟩ := hs j.succ
        refine ⟨x1, ?_, ?_⟩
        · simp only [Fin.succ_castSucc] at x2 ⊢
          exact x2
        · simpa only [Fin.succ_castSucc] using x3) a (fun j => ha j.succ)
    rw [Fin.prod_univ_succ, e1]
    congr 1
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
