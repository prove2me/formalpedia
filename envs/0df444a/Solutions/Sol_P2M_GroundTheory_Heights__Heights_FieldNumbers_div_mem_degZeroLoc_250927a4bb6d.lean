-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:10:21.687148+00:00
-- url     : https://prove2.me/submissions/221effe2-803b-4924-b234-6a773e4f1676

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForwardLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F)))
    {b : K → ℕ} {f g : MRing ι F} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) (hgP : g ∉ P)
    (hg𝒲 : ∀ W ∈ 𝒲, g ∉ W) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ degZeroLoc P 𝒲 :=
  Algebra.subset_adjoin ⟨b, f, g, hf, hg, hgP, hg𝒲, rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers
