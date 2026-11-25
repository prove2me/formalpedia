-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_RationalUnipotent_unipElem_inv_smul_c1eaf2eb5e18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:34:12.274714+00:00
-- url     : https://prove2.me/submissions/5cb8cea8-41bb-47b9-8065-0729cd09f9ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PRationalUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
theorem _root_.solution (h : HermitianForm F E W) {x₀ y : W} {c : E}
    (hx₀ : h.toSesq x₀ x₀ = 0) (hy : h.toSesq x₀ y = 0)
    (hc : c + conj F E c = -h.toSesq y y) (x : W) :
    (unipElem h hx₀ hy hc)⁻¹ • x = unipMap h x₀ (-y) (conj F E c) x := rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume.RationalUnipotent
