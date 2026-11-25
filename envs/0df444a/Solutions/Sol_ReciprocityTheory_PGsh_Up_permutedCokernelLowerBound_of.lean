-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.permutedCokernelLowerBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:49:55.421321+00:00
-- url     : https://prove2.me/submissions/0d910e4a-3271-4d71-a0e3-12ea97d87657

import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundStatement
import Definitions.Def_ReciprocityTheory_DualLattices_MapSmulOneMulVec
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Theorems.Thm_ReciprocityTheory_PGsh_Up_span_mk_top
import Theorems.Thm_ReciprocityTheory_PGsh_Up_av_kill
import Theorems.Thm_ReciprocityTheory_PGsh_Up_vp_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hU6 : CokernelLengthComparisonStatement) (hEx : LenExStatement) (hKG : KilledGenStatement)
    (hIG : IdemGenStatement) : PermutedCokernelLowerBoundStatement := by
  unfold PermutedCokernelLowerBoundStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ hP1 hP2 hL1 hL2 w hw d hd cw hcw
  have hidem : H.ρL (e (π w)) * H.ρL (e (π w)) = H.ρL (e (π w)) := by
    rw [← map_mul, he, if_pos rfl]
  obtain ⟨y, hy⟩ := hIG R g d (H.ρL (e (π w))) hidem hd
  obtain ⟨cwb, hcwb⟩ := hEx C v R hS.integers g H.Ht (H.ρL (e (π w)))
    ((H.ρ (e w)).map (algebraMap ℤ_[p] R))
  have hkill := av_kill hS H (e (π w)) (e w) (hσ w)
  have hgen : ∃ y' : Fin d → htCoker H (e (π w)) (e w), Submodule.span R (Set.range y') = ⊤ :=
    ⟨fun k => Submodule.Quotient.mk (y k), span_mk_top _ y hy⟩
  have h1 := hKG C v R hS.integers (htCoker H (e (π w)) (e w)) cwb d cp hcwb hgen hkill
  have h2 := hU6 p g C v R O σ cp hS H m e π he hσ hP1 hP2 hL1 hL2 w hw cw cwb hcw hcwb
  rw [vp_rpow hS d]
  exact_mod_cast h1.trans h2
end ReciprocityTheory.PGsh.Up
