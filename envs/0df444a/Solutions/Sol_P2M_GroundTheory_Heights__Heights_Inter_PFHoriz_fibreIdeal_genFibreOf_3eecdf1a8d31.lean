-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_fibreIdeal_genFibreOf_3eecdf1a8d31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:43:27.756958+00:00
-- url     : https://prove2.me/submissions/7e03d25f-ac11-456a-b3e6-a0d50c34b6fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_exists_clear_d073348b32e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_ker_eq_map_4ad68b54e07b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_aeval_baseSubst_c36c478e057f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PFHoriz
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
variable {W : Ideal (MRing ι')} [W.IsPrime] (hW : imageZ v W = imageZ v P')
namespace GroundTheory.Heights₂.Heights.Inter.PFHoriz
theorem _root_.solution (hκv : IsBlockMap κ v) (G : GenFibre v P') :
    fibreIdeal κ (genFibreOf G W hW) = fibreOf κ G W := by
  letI := (genAlg G W hW).toAlgebra
  exact ker_eq_map (baseSubst κ G) (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩)
    (aeval (R := ℤ) (xW W)).toRingHom W (ker_aeval_xW W) (aeval_baseSubst hW hκv G)
    (fun g => let ⟨_, F, hb, e⟩ := exists_clear hκv G g; ⟨_, hb, F, e⟩)
end GroundTheory.Heights₂.Heights.Inter.PFHoriz
