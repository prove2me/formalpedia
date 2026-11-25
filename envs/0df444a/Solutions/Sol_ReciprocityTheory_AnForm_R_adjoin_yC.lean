-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.adjoin_yC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:01.860215+00:00
-- url     : https://prove2.me/submissions/965fa63a-51f9-41ed-9341-ee8b303ef39b

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
import Theorems.Thm_ReciprocityTheory_AnForm_R_adjoin_reesChart_eq_top
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_exists_eval__chartCoord_95f51dd56702
import Theorems.Thm_ReciprocityTheory_AnForm_R_yC_yq
import Theorems.Thm_ReciprocityTheory_AnForm_R_yC_yt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) :
    @Algebra.adjoin ℂ (FinalTheorems.reesChart g i) _ _
      ((algebraMap _ (FinalTheorems.reesChart g i)).comp (constSec (toSpecC hP) (chartOpen hP p).1)).toAlgebra
      (Set.range (yC hP p g i)) = ⊤ :=
  adjoin_reesChart_eq_top _ (chartCoord hP p) (exists_eval₂_chartCoord hP p) g i (yC hP p g i)
    (fun q => ⟨_, yC_yq hP p g i q⟩) (fun k => ⟨_, yC_yt hP p g i k⟩)
end ReciprocityTheory.AnForm.R
