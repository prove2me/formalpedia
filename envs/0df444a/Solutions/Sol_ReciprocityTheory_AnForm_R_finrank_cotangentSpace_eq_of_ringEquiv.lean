-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.finrank_cotangentSpace_eq_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:17:03.929525+00:00
-- url     : https://prove2.me/submissions/7e7dc3a4-a0aa-4f44-be35-8cfd67932ac4

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
noncomputable section
variable {σ : Type} [Fintype σ]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (f : A ≃+* B) :
    Module.finrank (ResidueField A) (CotangentSpace A) =
      Module.finrank (ResidueField B) (CotangentSpace B) := by
  classical
  let g : A →ₐ[ℤ] B := f.toRingHom.toIntAlgHom
  let g' : B →ₐ[ℤ] A := f.symm.toRingHom.toIntAlgHom
  have hmax : ∀ x : A, f x ∈ maximalIdeal B ↔ x ∈ maximalIdeal A := by
    intro x
    simp only [mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff f x)
  have hA : maximalIdeal A ≤ (maximalIdeal B).comap g := fun x hx => (hmax x).2 hx
  have hB : maximalIdeal B ≤ (maximalIdeal A).comap g' := fun y hy => by
    show f.symm y ∈ maximalIdeal A
    rw [← hmax, f.apply_symm_apply]
    exact hy
  let j₁ := Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) g hA
  let j₂ := Ideal.mapCotangent (maximalIdeal B) (maximalIdeal A) g' hB
  let j : CotangentSpace A ≃+ CotangentSpace B :=
    { toFun := j₁
      invFun := j₂
      left_inv := fun m => by
        obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective m
        simp only [j₁, j₂, Ideal.mapCotangent_toCotangent]
        congr 1
        exact Subtype.ext (f.symm_apply_apply (x : A))
      right_inv := fun m => by
        obtain ⟨y, rfl⟩ := (maximalIdeal B).toCotangent_surjective m
        simp only [j₁, j₂, Ideal.mapCotangent_toCotangent]
        congr 1
        exact Subtype.ext (f.apply_symm_apply (y : B))
      map_add' := j₁.map_add }
  let i : ResidueField A ≃+* ResidueField B := ResidueField.mapEquiv f
  have hc : ∀ (r : ResidueField A) (m : CotangentSpace A), j (r • m) = i r • j m := by
    intro r m
    obtain ⟨a, rfl⟩ := residue_surjective r
    obtain ⟨x, rfl⟩ := (maximalIdeal A).toCotangent_surjective m
    have e1 : (residue A a : ResidueField A) • ((maximalIdeal A).toCotangent x : CotangentSpace A) =
        (maximalIdeal A).toCotangent (a • x) := by
      rw [map_smul]
      exact algebraMap_smul (ResidueField A) a _
    have e3 : (residue B (f a) : ResidueField B) •
        ((maximalIdeal B).toCotangent ⟨g x, hA x.2⟩ : CotangentSpace B) =
        (maximalIdeal B).toCotangent (f a • ⟨g x, hA x.2⟩) := by
      rw [map_smul]
      exact algebraMap_smul (ResidueField B) (f a) _
    have e2 : i (residue A a) = residue B (f a) := by
      first
        | rfl
        | exact IsLocalRing.ResidueField.map_residue (f : A →+* B) a
        | simp [i]
    have hj : ∀ m, j m = j₁ m := fun _ => rfl
    rw [hj, hj, e1, e2, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, e3]
    congr 1
    apply Subtype.ext
    show f (a * (x : A)) = f a * f x
    exact map_mul f a x
  have h2 := congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv (⇑i) j i.bijective hc)
  rw [Cardinal.toNat_lift, Cardinal.toNat_lift] at h2
  exact h2
end ReciprocityTheory.AnForm.R
