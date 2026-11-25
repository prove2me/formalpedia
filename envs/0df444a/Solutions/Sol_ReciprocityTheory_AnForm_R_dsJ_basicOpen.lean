-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.dsJ_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:25.382542+00:00
-- url     : https://prove2.me/submissions/cc066d35-0b29-4252-ab8b-7ce4a23df1af

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_core
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
    (U : W.affineOpens) (f : Γ(W, U)) :
    (dsJ V g U).map (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom =
      dsJ V g (W.affineBasicOpen f) := by
  apply le_antisymm
  · refine Ideal.map_le_of_le_comap fun b hb => ?_
    change (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom b ∈ dsJ V g (W.affineBasicOpen f)
    refine mem_dsJ.2 fun y hy => ?_
    have h1 := (mem_dsJ.1 hb) y (W.basicOpen_le f hy)
    have e : W.presheaf.germ (W.affineBasicOpen f).1 y hy
        ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom b) =
        W.presheaf.germ U.1 y (W.basicOpen_le f hy) b :=
      TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) y hy b
    rw [e]
    exact h1
  · intro b hb
    letI := (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom.toAlgebra
    haveI := U.2.isLocalization_basicOpen f
    obtain ⟨⟨a, s'⟩, hab⟩ := IsLocalization.surj (Submonoid.powers f) b
    obtain ⟨n, hn⟩ := s'.2
    simp only [RingHom.algebraMap_toAlgebra, ← hn] at hab
    have ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen f →
        W.presheaf.germ U.1 z hz a ∈ dsK V g z := by
      intro z hz hzf
      have h1 := (mem_dsJ.1 hb) z hzf
      have e1 : W.presheaf.germ (W.basicOpen f) z hzf
          ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom a) = W.presheaf.germ U.1 z hz a :=
        TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) z hzf a
      have e2 : W.presheaf.germ (W.basicOpen f) z hzf
          ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ n)) =
            W.presheaf.germ U.1 z hz (f ^ n) :=
        TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) z hzf (f ^ n)
      rw [← e1, ← hab, map_mul, e2]
      exact Ideal.mul_mem_right _ _ h1
    obtain ⟨m, hm⟩ := ds_core hV hg f a ha
    have hx : (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) ∈
        (dsJ V g U).map (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom :=
      Ideal.mem_map_of_mem _ hm
    have hu : IsUnit ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ (m + n))) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit f).pow _
    have heq : b * (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ (m + n)) =
        (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) := by
      rw [map_mul, ← hab, pow_add, map_mul]
      ring
    obtain ⟨v, hv⟩ := hu
    have hb' : b = (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) * ↑v⁻¹ := by
      rw [← heq, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [hb']
    exact Ideal.mul_mem_right _ _ hx
end ReciprocityTheory.AnForm.R
