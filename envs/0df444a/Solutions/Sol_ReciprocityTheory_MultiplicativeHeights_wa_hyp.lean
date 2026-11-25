-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:34:23.857279+00:00
-- url     : https://prove2.me/submissions/b78c1f0a-7063-4d66-98b6-b6ba177feab2

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_symm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sub_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_smul_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sub_left
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_smul_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x : Fin r → K) (hxW : x ∈ W) (hx0 : x ≠ 0) (hxx : S.h x x = 0) :
    ∃ y ∈ W, S.h x y = 1 ∧ S.h y y = 0 := by
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W, S.h x w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 (hnd x hxW hc)
  obtain ⟨u, hu⟩ : ∃ u, u = (S.h x w)⁻¹ • w := ⟨_, rfl⟩
  have huW : u ∈ W := hu ▸ W.smul_mem _ hwW
  have hxu : S.h x u = 1 := by rw [hu, wa_smul_right, inv_mul_cancel₀ hw]
  have hux : S.h u x = 1 := by rw [wa_symm S x u, hxu, map_one]
  have hcuu : S.c (S.h u u) = S.h u u := (wa_symm S u u).symm
  obtain ⟨t, ht⟩ : ∃ t, t = S.h u u / 2 := ⟨_, rfl⟩
  have hct : S.c t = t := by rw [ht, map_div₀, hcuu, map_ofNat]
  refine ⟨u - t • x, W.sub_mem huW (W.smul_mem _ hxW), ?_, ?_⟩
  · rw [wa_sub_right, hxu, wa_smul_right, hxx, mul_zero, sub_zero]
  · simp only [wa_sub_left, wa_sub_right, wa_smul_left, wa_smul_right, hux, hxu, hxx, hct]
    rw [ht]
    ring
end ReciprocityTheory.MultiplicativeHeights
