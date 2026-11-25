-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_open_comps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:05:10.498511+00:00
-- url     : https://prove2.me/submissions/45f4c44e-f15f-4071-ab12-ab58816c8308

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_open_compsH


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [IsNoetherian W] {Z : W.IdealSheafData} (y : W) (U : W.affineOpens)
    (hy : y ∈ U.1) {n : ℕ} (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n))
    [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZU : Z.ideal U = Ideal.span {∏ i ∈ J, f i}) :
    ∃ O : W.Opens, y ∈ O ∧ O ≤ U.1 ∧ ∀ C ∈ comps (Z.support : Set W),
      C ∩ O = {z ∈ (O : Set W) | ∃ i ∈ J, IsBranch (Z.support : Set W) (f i) y C ∧
        z ∈ W.zeroLocus {f i}} := by
  exact exists_open_compsH y U hy f J hrsp hZU
end ReciprocityTheory.AnForm.R
