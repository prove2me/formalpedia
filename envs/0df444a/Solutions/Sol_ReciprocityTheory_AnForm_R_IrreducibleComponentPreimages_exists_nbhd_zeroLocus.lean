-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_nbhd_zeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:49:59.638274+00:00
-- url     : https://prove2.me/submissions/19fedfda-0cf2-4434-a2b8-9be89863fec4

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution {U V : W.Opens} {x : W} (hxU : x ∈ U) (hxV : x ∈ V) (s : Γ(W, U))
    (s' : Γ(W, V)) (u : W.presheaf.stalk x) (hu : IsUnit u)
    (heq : W.presheaf.germ V x hxV s' = W.presheaf.germ U x hxU s * u) :
    ∃ O : W.Opens, x ∈ O ∧ ∀ z ∈ O, (z ∈ W.zeroLocus {s} ↔ z ∈ W.zeroLocus {s'}) := by
  obtain ⟨U₁, hx1, t, ht⟩ := W.presheaf.germ_exist u
  have hxt : x ∈ W.basicOpen t := (Scheme.mem_basicOpen _ _ x hx1).2 (by rw [ht]; exact hu)
  have e1 : W.presheaf.germ (U ⊓ U₁) x ⟨hxU, hx1⟩
      (W.presheaf.map (homOfLE inf_le_left).op s * W.presheaf.map (homOfLE inf_le_right).op t) =
      W.presheaf.germ U x hxU s * u := by
    rw [map_mul]
    first
    | (erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht])
    | (simp only [TopCat.Presheaf.germ_res_apply, ht])
    | (simp only [Scheme.germ_res_apply, ht])
  obtain ⟨O₀, hxO₀, i₁, i₂, hO₀⟩ := W.presheaf.germ_eq x hxV (show x ∈ U ⊓ U₁ from ⟨hxU, hx1⟩) s' _ (heq.trans e1.symm)
  refine ⟨O₀ ⊓ W.basicOpen t, ⟨hxO₀, hxt⟩, fun z hz => ?_⟩
  have hzV : z ∈ V := i₁.le hz.1
  have hzU : z ∈ U := (i₂.le hz.1).1
  have hz1 : z ∈ U₁ := (i₂.le hz.1).2
  have hg : W.presheaf.germ V z hzV s' =
      W.presheaf.germ U z hzU s * W.presheaf.germ U₁ z hz1 t := by
    have h1 := congrArg (W.presheaf.germ O₀ z hz.1) hO₀
    first
    | (erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, map_mul,
        TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h1; exact h1)
    | (simp only [TopCat.Presheaf.germ_res_apply, map_mul] at h1; exact h1)
    | (simp only [Scheme.germ_res_apply, map_mul] at h1; exact h1)
  have hunit : IsUnit (W.presheaf.germ U₁ z hz1 t) := (Scheme.mem_basicOpen _ _ z hz1).1 hz.2
  simp only [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe]
  rw [Scheme.mem_basicOpen _ _ z hzU, Scheme.mem_basicOpen _ _ z hzV, hg, IsUnit.mul_iff]
  exact not_congr ⟨fun h => ⟨h, hunit⟩, fun h => h.1⟩
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
