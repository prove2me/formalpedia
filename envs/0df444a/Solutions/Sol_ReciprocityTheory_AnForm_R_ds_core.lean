-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ds_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:19.83104+00:00
-- url     : https://prove2.me/submissions/420bbeb5-e25a-41be-970b-c705491533ac

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_local
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_dsJ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (hV : ∀ x : W, ∃ c, x ∈ V c)
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {U : W.affineOpens} (s a : Γ(W, U))
    (ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen s → W.presheaf.germ U.1 z hz a ∈ dsK V g z) :
    ∃ m : ℕ, s ^ m * a ∈ dsJ V g U := by
  classical
  have hc : ∀ z : U.1, ∃ t : Γ(W, U), ∃ c, W.basicOpen t ≤ V c ∧ (z : W) ∈ W.basicOpen t := by
    intro z
    obtain ⟨c, hc⟩ := hV z
    obtain ⟨t, ht, hzt⟩ := U.2.exists_basicOpen_le ⟨(z : W), hc⟩ z.2
    exact ⟨t, c, ht, hzt⟩
  choose t c ht hzt using hc
  have hm : ∀ z : U.1, ∃ m : ℕ, ∀ y (hy : y ∈ W.basicOpen (t z)),
      W.presheaf.germ U.1 y (W.basicOpen_le (t z) hy) (s ^ m * a) ∈ dsK V g y :=
    fun z => ds_local hg s a ha (c z) (t z) (ht z)
  choose m hm using hm
  obtain ⟨F, hF⟩ := U.2.isCompact.elim_finite_subcover
    (fun z : U.1 => (W.basicOpen (t z) : Set W))
    (fun z => (W.basicOpen (t z)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hzt ⟨y, hy⟩⟩)
  refine ⟨∑ z ∈ F, m z, mem_dsJ.2 fun y hy => ?_⟩
  obtain ⟨z, hzF, hyz⟩ := Set.mem_iUnion₂.1 (hF hy)
  have hle : m z ≤ ∑ z ∈ F, m z := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzF
  have h1 := hm z y hyz
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]
  exact Ideal.mul_mem_left _ _ h1
end ReciprocityTheory.AnForm.R
