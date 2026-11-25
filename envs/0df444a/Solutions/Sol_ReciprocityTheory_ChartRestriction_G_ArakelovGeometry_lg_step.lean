-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.lg_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:49:39.285807+00:00
-- url     : https://prove2.me/submissions/4d156f83-f063-48a4-81ea-e3ded875b484

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogIdealChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_pos
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
theorem _root_.solution {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) {q : Ideal (MRing ι)} (hq : ∀ g, g ∈ q ↔ g * f ∈ J) {a : K → ℕ}
    (hca : ∀ k, c k ≤ a k) {p : ℕ} (hp : 0 < p) (hpJ : (p : MRing ι) ∈ J) :
    lg J a = lg (J ⊔ Ideal.span {f}) a + lg q (a - c) := by
  have hpq : (p : MRing ι) ∈ q := (hq _).mpr (J.mul_mem_right _ hpJ)
  rw [lg, card_mPiece_step hJ hf hq hca, Nat.cast_mul, Real.log_mul, lg, lg]
  · exact_mod_cast (card_mPiece_pos _ a hp (Ideal.mem_sup_left hpJ)).ne'
  · exact_mod_cast (card_mPiece_pos _ _ hp hpq).ne'
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
