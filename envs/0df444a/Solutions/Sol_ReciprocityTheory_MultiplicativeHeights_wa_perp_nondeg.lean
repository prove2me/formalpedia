-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.wa_perp_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:06:03.980426+00:00
-- url     : https://prove2.me/submissions/3fe803ae-c969-4a7a-bd9d-045757da1406

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegAA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_symm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_sub_right
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_wa_smul_right

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
    (x y : Fin r → K) (hxW : x ∈ W) (hyW : y ∈ W) (hxx : S.h x x = 0) (hxy : S.h x y = 1)
    (hyy : S.h y y = 0) :
    ∀ z ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y),
      (∀ w ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y), S.h z w = 0) → z = 0 := by
  intro z hz hzo
  obtain ⟨⟨hzW, hzx⟩, hzy⟩ := hz
  have hzx : S.h x z = 0 := hzx
  have hzy : S.h y z = 0 := hzy
  apply hnd z hzW
  intro w hwW
  have hyx : S.h y x = 1 := by rw [wa_symm S x y, hxy, map_one]
  have hw' : w - S.h y w • x - S.h x w • y ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y) := by
    refine ⟨⟨W.sub_mem (W.sub_mem hwW (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_⟩, ?_⟩
    · show S.h x _ = 0
      simp only [wa_sub_right, wa_smul_right, hxx, hxy]
      ring
    · show S.h y _ = 0
      simp only [wa_sub_right, wa_smul_right, hyx, hyy]
      ring
  have h1 := hzo _ hw'
  have hzx' : S.h z x = 0 := by rw [wa_symm S x z, hzx, map_zero]
  have hzy' : S.h z y = 0 := by rw [wa_symm S y z, hzy, map_zero]
  simp only [wa_sub_right, wa_smul_right, hzx', hzy', mul_zero, sub_zero] at h1
  exact h1
end ReciprocityTheory.MultiplicativeHeights
