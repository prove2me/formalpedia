-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.existsUnique_branchH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:11.108987+00:00
-- url     : https://prove2.me/submissions/46bf38d9-03ed-4f14-b3d3-0d19f07fb850

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_parPrimes
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isBranch_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) (i : Fin n) (hi : i ∈ J) :
    ∃! C, IsBranchH (Z.support : Set W) (f i) y C := by
  obtain ⟨q, hq⟩ := exists_parPrimes U.2 hy f hrsp
  exact ⟨closure {U.2.fromSpec (q i)}, (isBranch_iff hq hZU hi _).2 rfl,
    fun C hC => (isBranch_iff hq hZU hi C).1 hC⟩
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
