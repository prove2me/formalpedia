-- Prove2me | solution 1 for P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___eq_top_iff_ideal_eq_top_b681c76d4d78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:50:54.555919+00:00
-- url     : https://prove2.me/submissions/645bc1dc-0621-44bb-8c30-2fc64bd278ff

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution {Y : Scheme.{u}} (I : Y.IdealSheafData) {V : Y.Opens}
    (hV : IsAffineOpen V) : I.comap V.ι = ⊤ ↔ I.ideal ⟨V, hV⟩ = ⊤ := by
  have hVaff : IsAffine V.toScheme := hV
  have htop : ∀ U : V.toScheme.affineOpens, (⊤ : V.toScheme.IdealSheafData).ideal U = ⊤ := by
    intro U
    simp
  have e : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := by simp
  have himg : V.ι ''ᵁ (⊤ : V.toScheme.Opens) = V := by simp
  have hiso : ∀ U : Y.Opens, U = V.ι ''ᵁ (⊤ : V.toScheme.Opens) →
      ∀ e' : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ U,
        IsIso (V.ι.appLE U (⊤ : V.toScheme.Opens) e') := by
    rintro U rfl e'
    rw [← Scheme.Hom.appIso_hom' V.ι (⊤ : V.toScheme.Opens)]
    infer_instance
  obtain ⟨φ, hφ, hmap⟩ : ∃ φ : Γ(Y, V) ⟶ Γ(V.toScheme, ⊤), IsIso φ ∧
      (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
        = (I.ideal ⟨V, hV⟩).map φ.hom :=
    ⟨V.ι.appLE V (⊤ : V.toScheme.Opens) e, hiso V himg.symm e,
      comap_ideal_eq_map_appLE I V.ι ⟨V, hV⟩ ⟨⊤, isAffineOpen_top V.toScheme⟩ e⟩
  have hcomp : (CommRingCat.Hom.hom (CategoryTheory.inv φ)).comp (CommRingCat.Hom.hom φ)
      = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, IsIso.hom_inv_id, CommRingCat.hom_id]
  constructor
  · intro h
    rw [h, htop] at hmap
    have h3 : ((I.ideal ⟨V, hV⟩).map φ.hom).map (CategoryTheory.inv φ).hom
        = I.ideal ⟨V, hV⟩ := by
      rw [Ideal.map_map, hcomp, Ideal.map_id]
    rw [← hmap, Ideal.map_top] at h3
    exact h3.symm
  · intro h
    have h2 : (I.comap V.ι).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩
        = (⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩ := by
      rw [hmap, h, Ideal.map_top, htop]
    exact (equivOfIsAffine (X := V.toScheme)).injective h2
end AlgebraicGeometry.Scheme.IdealSheafData
