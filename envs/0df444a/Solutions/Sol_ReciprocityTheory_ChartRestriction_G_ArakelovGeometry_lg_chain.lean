-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.lg_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:05.675266+00:00
-- url     : https://prove2.me/submissions/17b89565-e7ca-4365-9226-eab1ec2fd85c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_chain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_pos


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
theorem _root_.solution (a : K → ℕ) {N : ℕ} {F : Fin (N + 1) → Ideal (MRing ι)} {f : Fin N → MRing ι}
    {c : Fin N → K → ℕ} {q : Fin N → Ideal (MRing ι)} (h0 : IsMultiHomogIdeal (F 0))
    (hlast : F (Fin.last N) = ⊤)
    (hj : ∀ j : Fin N, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc)
    (ha : ∀ j k, c j k ≤ a k) {p : ℕ} (hp : 0 < p) (hpq : ∀ j, (p : MRing ι) ∈ q j) :
    lg (F 0) a = ∑ j, lg (q j) (a - c j) := by
  rw [lg, card_mPiece_chain a N F f c q h0 hlast hj ha, Nat.cast_prod, Real.log_prod]
  · rfl
  · intro j _
    exact_mod_cast (card_mPiece_pos _ _ hp (hpq j)).ne'
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
