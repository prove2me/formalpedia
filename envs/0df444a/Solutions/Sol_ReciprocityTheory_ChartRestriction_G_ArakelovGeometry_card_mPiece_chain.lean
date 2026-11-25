-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:54:35.736335+00:00
-- url     : https://prove2.me/submissions/730c48b1-850e-4320-b970-b58365a82fd8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_LengthLocQuotEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomogIdeal_chain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_step


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
theorem _root_.solution (a : K → ℕ) : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι))
    (f : Fin N → MRing ι) (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)),
    IsMultiHomogIdeal (F 0) → F (Fin.last N) = ⊤ →
    (∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j k, c j k ≤ a k) →
    Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j))
  | 0, F, f, c, q, _, hlast, _, _ => by
    have : F 0 = ⊤ := hlast
    rw [this, card_mPiece_top, Fin.prod_univ_zero]
  | N + 1, F, f, c, q, h0, hlast, hj, ha => by
    have ih := solution a N (fun j => F j.succ) (fun j => f j.succ) (fun j => c j.succ)
      (fun j => q j.succ)
      (isMultiHomogIdeal_chain h0 (fun j => ⟨(hj j).1, (hj j).2.1⟩) 1)
      (by simpa [Fin.succ_last] using hlast)
      (fun j => by
        have h := hj j.succ
        rwa [← Fin.succ_castSucc] at h)
      (fun j => ha j.succ)
    obtain ⟨h1, h2, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h2 h3
    rw [card_mPiece_step h0 h1 h3 (ha 0), ← h2, Fin.prod_univ_succ, mul_comm]
    rw [ih]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
