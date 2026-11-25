-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_funField_hom_ext_8fb52f33d4ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:23.768253+00:00
-- url     : https://prove2.me/submissions/119e67e1-f09d-4051-8185-89b3daaea2ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
theorem _root_.solution {P : Ideal (MRing ι)} [P.IsPrime] {τ₁ τ₂ : funField P →+* ℂ}
    (h : ∀ (x : funField P) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ P →
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P v = toFrac P u → τ₁ x = τ₂ x) : τ₁ = τ₂ := by
  have hle : funField P ≤ (RingHom.eqLocus τ₁ τ₂).map (funField P).subtype := by
    refine Subring.closure_le.mpr ?_
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    exact ⟨⟨_, Subring.subset_closure ⟨u, v, a, hv, hu, hva, rfl⟩⟩,
      h _ u v a hu hva (not_mem_of_nonZeroDivisor hv) (IsLocalization.mk'_spec _ _ _), rfl⟩
  ext x
  obtain ⟨y, hy, hyx⟩ := hle x.2
  have : y = x := Subtype.ext hyx
  subst this
  exact hy
end GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
