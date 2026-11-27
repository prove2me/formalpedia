-- Prove2me | solution 1 for PositivityTheory.ThKH.Locrep.Pm_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:45.313496+00:00
-- url     : https://prove2.me/submissions/22283701-f7d3-4776-bf04-5b581586cb43

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB
import Theorems.Thm_PositivityTheory_ThKH_Locrep_Pm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology GlobalTheory.WeilM
variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)
variable {ev ι}
variable [TopologicalSpace A] [IsTopologicalAddGroup A] [TopologicalSpace K] [IsTopologicalAddGroup K]
omit [IsTopologicalAddGroup K]
namespace PositivityTheory.ThKH.Locrep
theorem _root_.solution (h : ∀ y, ev (ι y) = y) (hev : Continuous ev) (hι : Continuous ι) {φ : K → ℂ} (hφ : φ ∈ SB K) (y : K)
    {g : A → ℂ} (hg : g ∈ SB A) : Pm ev ι φ y g ∈ SB A := by
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hput : Continuous fun x : A => put ev ι x y :=
    (continuous_id.sub (hι.comp hev)).add continuous_const
  have hfun : (Pm ev ι φ y g : A → ℂ) = fun x => φ (ev x) * g (put ev ι x y) :=
    funext (Pm_apply ev ι φ y g)
  show IsLocallyConstant (Pm ev ι φ y g) ∧ HasCompactSupport (Pm ev ι φ y g)
  rw [hfun]
  refine ⟨(hφ'.1.comp_continuous hev).mul (hg'.1.comp_continuous hput), ?_⟩
  have hc : Continuous fun p : A × K => p.1 + ι p.2 - ι y :=
    (continuous_fst.add (hι.comp continuous_snd)).sub continuous_const
  have hK : IsCompact ((fun p : A × K => p.1 + ι p.2 - ι y) '' (tsupport g ×ˢ tsupport φ)) :=
    (hg'.2.prod hφ'.2).image hc
  have hsub : Function.support (fun x => φ (ev x) * g (put ev ι x y)) ⊆
      (fun p : A × K => p.1 + ι p.2 - ι y) '' (tsupport g ×ˢ tsupport φ) := by
    intro x hx
    have hx' : φ (ev x) * g (put ev ι x y) ≠ 0 := hx
    have h1 : φ (ev x) ≠ 0 := left_ne_zero_of_mul hx'
    have h2 : g (put ev ι x y) ≠ 0 := right_ne_zero_of_mul hx'
    refine ⟨(put ev ι x y, ev x), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, ?_⟩
    simp only [put]
    abel
  exact IsCompact.of_isClosed_subset hK.closure isClosed_closure (closure_mono hsub)
end PositivityTheory.ThKH.Locrep
