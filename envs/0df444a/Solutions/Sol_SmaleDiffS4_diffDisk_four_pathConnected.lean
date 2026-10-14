-- Prove2me | solution 1 for SmaleDiffS4.diffDisk_four_pathConnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-12T04:25:42.901189+00:00
-- url     : https://prove2.me/submissions/46f89bcf-0d1d-4b99-bb86-070066412b74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic
import Theorems.Thm_SmaleDiffS4_diffDisk_four_smoothlyIsotopic_id
import Theorems.Thm_SmaleDiffS4_continuous_of_smoothIsotopy

set_option autoImplicit false

open SmaleDiffS4
open scoped ContDiff

namespace SmaleDiffS4.RedS4

lemma diffDisk_ext {n : ℕ} {f g : DiffDisk n} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (Diffeomorph.ext h)

lemma one_apply {n : ℕ} (x : E n) : (1 : DiffDisk n).1 x = x := rfl

/-- Every element of `Diff(D⁴ rel ∂)` is joined to the identity by a path. -/
lemma joined_one (f : DiffDisk 4) : Joined (1 : DiffDisk 4) f := by
  obtain ⟨F, hF, h0, h1, hg⟩ := diffDisk_four_smoothlyIsotopic_id f
  choose g hgF using fun t : Set.Icc (0 : ℝ) 1 => hg t t.2
  have hc : Continuous g := continuous_of_smoothIsotopy 4 F hF g hgF
  refine ⟨⟨⟨g, hc⟩, ?_, ?_⟩⟩
  · exact diffDisk_ext fun x => by
      rw [hgF, one_apply]
      exact h0 x
  · exact diffDisk_ext fun x => by
      rw [hgF]
      exact h1 x

end SmaleDiffS4.RedS4

theorem solution : PathConnectedSpace (DiffDisk 4) := by
  refine ⟨⟨1⟩, fun f g => ?_⟩
  exact (SmaleDiffS4.RedS4.joined_one f).symm.trans (SmaleDiffS4.RedS4.joined_one g)
