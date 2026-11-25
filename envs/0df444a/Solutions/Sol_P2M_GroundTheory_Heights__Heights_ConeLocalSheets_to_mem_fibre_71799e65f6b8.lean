-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_to_mem_fibre_71799e65f6b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:12.928861+00:00
-- url     : https://prove2.me/submissions/69d59a38-424d-402b-90cb-f349d173e37f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mem_zeroSet_chartIdeal_0963b45b1ca9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_tailMat_mulVec_c4c1d9585b97

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
open GroundTheory.Heights₂.Heights.ConeLocalSheets
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeLocalSheets
theorem _root_.solution {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : Unit) → PBlk n k) → ℂ} (hw : w ∈ fibre P Ψ y) :
    ∃ z ∈ ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y, segre (lift z) = w := by
  obtain ⟨z, hz, rfl, hΨ⟩ := hw
  have hl : lift (fun i => z ⟨(), i⟩) = z := by
    funext p
    obtain ⟨u, i⟩ := p
    rfl
  refine ⟨fun i => z ⟨(), i⟩, ⟨mem_zeroSet_chartIdeal.mpr ⟨?_, ?_⟩, ?_⟩, by rw [hl]⟩
  · rw [hl]
    exact hz.2
  · rw [hl, hΨ]
    rfl
  · funext i
    rw [tailMat_mulVec, hl, hΨ]
    rfl
end GroundTheory.Heights₂.Heights.ConeLocalSheets
