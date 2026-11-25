-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFHoriz_aeval_baseSubst_c36c478e057f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:14:11.905185+00:00
-- url     : https://prove2.me/submissions/e6651990-ed84-44f4-88f7-8f196c03d948

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFHoriz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFHoriz

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
theorem _root_.solution (hκv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    letI := (genAlg G W hW).toAlgebra
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) (baseSubst κ G f) =
      aeval (R := ℤ) (xW W) f := by
  letI := (genAlg G W hW).toAlgebra
  have e : (aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => xW W ⟨q.1.1, q.2⟩) :
        MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] FractionRing (MRing ι' ⧸ W)).toRingHom.comp (baseSubst κ G) =
      (aeval (R := ℤ) (xW W)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun q => ?_)
    · rw [RingHom.comp_apply, baseSubst, eval₂Hom_C,
        eq_intCast (algebraMap ℤ (MRingOver G.Φ (fibreIdx ι' κ))) a, eq_intCast (C : ℤ →+* MRing ι') a,
        map_intCast, map_intCast]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rw [baseSubst, eval₂Hom_X']
      by_cases h : q.1 ∈ Set.range κ
      · have h' : q ∈ Set.range v := hκv.2.2.2 q h
        rw [dif_pos h, dif_pos h', aeval_C, RingHom.algebraMap_toAlgebra, genAlg_alt, h'.choose_spec]
        rfl
      · rw [dif_neg h, aeval_X]
  exact RingHom.congr_fun e f
end GroundTheory.Heights₂.Heights.Inter.PFHoriz
