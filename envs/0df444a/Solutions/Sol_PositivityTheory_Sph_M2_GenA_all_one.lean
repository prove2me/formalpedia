-- Prove2me | solution 1 for PositivityTheory.Sph.M2.GenA.all_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:58.402077+00:00
-- url     : https://prove2.me/submissions/9dd4daa9-f80f-4dbb-b8b5-1ecdcc474f07

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_DgPerm
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_tv_one
import Theorems.Thm_PositivityTheory_Sph_M2_GenA_dg_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph PositivityTheory.Sph.M2 PositivityTheory.Sph.M2.GenA
open Matrix
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace PositivityTheory.Sph.M2.GenA
theorem _root_.solution (ψ : GL n K →* ℝ) (hpos : ∀ g, 0 < ψ g) {w : K} (h0 : w ≠ 0) (h1 : 1 + w ≠ 0)
    (hsc : ∀ u : Kˣ, ψ (dg fun _ => u) = 1) (g : GL n K) : ψ g = 1 := by
  have key : ∀ M : Matrix n n K, M.det ≠ 0 → ∀ g : GL n K, (g : Matrix n n K) = M → ψ g = 1 := by
    intro M hM
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∀ g : GL n K, (g : Matrix n n K) = M → ψ g = 1) M hM ?_ ?_ ?_
    · intro D hD g hg
      rw [det_diagonal] at hD
      have hD' : ∀ i, D i ≠ 0 := fun i => Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      have : g = dg fun i => Units.mk0 (D i) (hD' i) := Units.ext hg
      rw [this]
      exact dg_one ψ hpos hsc _
    · intro t g hg
      have : g = tv t.hij t.c := Units.ext hg
      rw [this]
      exact tv_one ψ hpos h0 h1 _ _
    · intro A B hA hB pA pB g hg
      have : g = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB := Units.ext hg
      rw [this, map_mul, pA _ rfl, pB _ rfl, one_mul]
  exact key _ (Matrix.GeneralLinearGroup.det_ne_zero g) g rfl
end PositivityTheory.Sph.M2.GenA
