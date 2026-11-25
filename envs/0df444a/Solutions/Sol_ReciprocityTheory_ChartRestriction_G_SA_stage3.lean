-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.stage3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:22.298494+00:00
-- url     : https://prove2.me/submissions/5a758c0c-e210-42a3-95dd-a2d3e097e8cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_ef_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_apply_half
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_neg_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_reach_eich_e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1) {s : ℕ} {a : Fin s → ι → K}
  (hae : ∀ j, hf σ J (a j) e = 0) (haf : ∀ j, hf σ J (a j) f = 0)
  (hfix : ∀ x, σ x = x → x ≠ 0 → IsUnit x) {i2 : K} (h2i : 2 * i2 = 1) {δ : K} (hδ : IsUnit δ)
  (hσδ : σ δ = -δ) [IsReduced K]
include hσ hJ he hff hef hae haf hfix h2i hδ hσδ
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {b : ι → K} (hb : ∀ j, hf σ J b (a j) = 0) (hβ : IsUnit (hf σ J b e)) :
    ∃ b', Reach σ J e f a b b' ∧ b' = hf σ J b' f • e + hf σ J b' e • f ∧ IsUnit (hf σ J b' e) := by
  have hi2 := apply_half hσ hJ he hff hef hae haf hfix h2i hδ hσδ
  obtain ⟨hwe, hwf⟩ := decomp hσ hJ he hff hef b
  set α := hf σ J b f
  set β := hf σ J b e
  set w := b - α • e - β • f with hw
  have hea : ∀ j, hf σ J e (a j) = 0 := fun j => by rw [← hf_symm hσ hJ, hae, map_zero]
  have hfa : ∀ j, hf σ J f (a j) = 0 := fun j => by rw [← hf_symm hσ hJ, haf, map_zero]
  have hwa : ∀ j, hf σ J w (a j) = 0 := fun j => by
    rw [hw, hf_sub_left, hf_sub_left, hf_smul_left, hf_smul_left, hb, hea, hfa]; ring
  obtain ⟨βi, hβi⟩ := hβ.exists_right_inv
  set u := (-βi) • w
  set c := -(hf σ J u u * i2)
  have hc : c + σ c + hf σ J u u = 0 := by
    have : σ (hf σ J u u) = hf σ J u u := hf_symm hσ hJ u u
    simp only [c, map_neg, map_mul, this, hi2]
    linear_combination (-hf σ J u u) * h2i
  have r := reach_eich_e hσ hJ he hff hef hae haf (u := u) (c := c)
    (by simp [u, hf_smul_left, hf_neg_left, hwe]) (by simp [u, hf_smul_left, hf_neg_left, hwf]) hc
    (fun j => by simp [u, hf_smul_left, hf_neg_left, hwa]) b
  have hb' : eich σ J e u c *ᵥ b = (α - hf σ J b u + c * β) • e + β • f := by
    rw [eich_mulVec]
    ext i
    simp only [u, hw, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(b i - α * e i - β * f i)) * hβi
  rw [hb'] at r
  have hval := hf_ef_left hσ hJ he hff hef (e := e) (f := f) (α - hf σ J b u + c * β) β
  exact ⟨_, r, by rw [hval.1, hval.2], by rw [hval.1]; exact hβ⟩
end ReciprocityTheory.ChartRestriction.G.SA
