-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_exists_form_7820841f3e38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:00.722955+00:00
-- url     : https://prove2.me/submissions/636d693f-9f9c-4f8d-aa94-d765d38dcf98

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_xpow


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
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) (b : K → ℕ) :
    ∃ s : MRing ι, IsMultiHomog s b ∧ s ∉ P := by
  classical
  have hrel := hP.2.1.2.2
  have hpr : P.IsPrime := hP.2.1.1
  refine ⟨ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow (fun k => (hrel k).choose) b,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow _ _, fun h => ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow, Ideal.IsPrime.prod_mem_iff] at h
  obtain ⟨k, _, hk⟩ := h
  exact (hrel k).choose_spec (hpr.mem_of_pow_mem _ hk)
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
