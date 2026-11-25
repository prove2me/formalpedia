-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.BasePf.piece_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:57:33.57315+00:00
-- url     : https://prove2.me/submissions/2ec80fda-e19a-4f9a-914d-00fe144676c2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_BaseOrbits_PieceMem
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_rel_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf
variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]
open Classical
namespace PositivityTheory.RgUd.T.Nil.BasePf
theorem _root_.solution (K : Subgroup G) (S : Set W) (hKo : ∀ w ∈ S, IsOpen {w' | ∃ g ∈ K, g • w = w'})
    {F : Y × W → ℂ} (hF : F ∈ TF (Y × W)) (hFS : ∀ p : Y × W, p.2 ∉ S → F p = 0)
    (q : Quotient (rel K)) :
    (fun p : Y × W => F p * if Quotient.mk (rel K) p.2 = q then 1 else 0) ∈ TF (Y × W) := by
  refine ⟨?_, hF.2.mul_right⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  by_cases hp : p.2 ∈ S
  · have hO : {w' | ∃ g ∈ K, g • p.2 = w'} ∈ nhds p.2 := (hKo p.2 hp).mem_nhds ⟨1, K.one_mem, one_smul _ _⟩
    have h1 := ((IsLocallyConstant.iff_eventually_eq _).1 hF.1) p
    have h2 : ∀ᶠ x : Y × W in nhds p, x.2 ∈ {w' | ∃ g ∈ K, g • p.2 = w'} :=
      continuous_snd.continuousAt.preimage_mem_nhds hO
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨g, hg, hgx⟩ := hx2
    have : Quotient.mk (rel K) x.2 = Quotient.mk (rel K) p.2 := (rel_iff K _ _).2 ⟨g, hg, hgx⟩
    rw [hx1, this]
  · have h0 : F p = 0 := hFS p hp
    have h1 := ((IsLocallyConstant.iff_eventually_eq _).1 hF.1) p
    filter_upwards [h1] with x hx1
    rw [hx1, h0, zero_mul, zero_mul]
end PositivityTheory.RgUd.T.Nil.BasePf
