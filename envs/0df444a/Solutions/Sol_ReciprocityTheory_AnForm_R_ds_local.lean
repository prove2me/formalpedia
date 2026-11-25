-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ds_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:26.948319+00:00
-- url     : https://prove2.me/submissions/7dd26608-400e-41e1-87bb-45d2b291fddc

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Theorems.Thm_ReciprocityTheory_AnForm_R_dsK_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
section LocGen
variable {W : Scheme.{u}} {ι' : Type*} (V : ι' → W.Opens) (g : ∀ c, Γ(W, V c))
variable {V g}
variable (V g)
variable {V g}
end LocGen
section LocGen
variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}
private lemma exists_pow_mul_mem_span_of_germ_mem {X : Scheme.{u}} {O : X.Opens} (hO : IsAffineOpen O)
    (s a h : Γ(X, O))
    (hloc : ∀ (x : X) (hx : x ∈ O), IsUnit (X.presheaf.germ O x hx s) →
      X.presheaf.germ O x hx a ∈ Ideal.span {X.presheaf.germ O x hx h}) :
    ∃ m : ℕ, s ^ m * a ∈ Ideal.span {h} := by
  let Q : Ideal Γ(X, O) := Submodule.comap (LinearMap.mulRight Γ(X, O) a) (Ideal.span {h})
  have hQ : ∀ r, r ∈ Q ↔ r * a ∈ Ideal.span {h} := fun r => by
    simp only [Q, Submodule.mem_comap, LinearMap.mulRight_apply]
  suffices hs : s ∈ Q.radical by
    obtain ⟨m, hm⟩ := hs
    exact ⟨m, (hQ _).mp hm⟩
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro p ⟨hQp, hp⟩
  by_contra hsp
  obtain ⟨x, hx⟩ : ∃ x : O, hO.primeIdealOf x = ⟨p, hp⟩ := by
    first
    | (refine ⟨hO.isoSpec.inv (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)), ?_⟩
       exact congrArg (fun f : Spec Γ(X, O) ⟶ Spec Γ(X, O) => f (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)))
         hO.isoSpec.inv_hom_id)
    | (refine ⟨hO.isoSpec.inv.base (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)), ?_⟩
       simp [IsAffineOpen.primeIdealOf, ← Scheme.Hom.comp_apply]
       done)
    | (refine ⟨hO.isoSpec.inv (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)), ?_⟩
       show hO.isoSpec.hom (hO.isoSpec.inv _) = _
       rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
       try rfl
       done)
    | (refine ⟨hO.isoSpec.inv (⟨p, hp⟩ : PrimeSpectrum Γ(X, O)), ?_⟩
       simp only [IsAffineOpen.primeIdealOf]
       rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
       try rfl
       try simp
       done)
  have hL := hO.isLocalization_stalk x
  have hxp : (hO.primeIdealOf x).asIdeal = p := by rw [hx]
  have hsu : IsUnit (X.presheaf.germ O x x.2 s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) (hO.primeIdealOf x).asIdeal
      s).mpr (by show s ∉ (hO.primeIdealOf x).asIdeal; rw [hxp]; exact hsp)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hloc x x.2 hsu)
  obtain ⟨⟨b, u⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hO.primeIdealOf x).asIdeal.primeCompl y
  have hy' : IsLocalization.mk' (X.presheaf.stalk x) b u *
      algebraMap Γ(X, O) (X.presheaf.stalk x) h = algebraMap Γ(X, O) (X.presheaf.stalk x) a := hy
  have e : algebraMap Γ(X, O) (X.presheaf.stalk x) (↑u * a) =
      algebraMap Γ(X, O) (X.presheaf.stalk x) (b * h) := by
    rw [map_mul, map_mul, ← IsLocalization.mk'_spec (X.presheaf.stalk x) b u]
    linear_combination -(algebraMap Γ(X, O) (X.presheaf.stalk x) ↑u) * hy'
  obtain ⟨v, hv⟩ := IsLocalization.exists_of_eq (M := (hO.primeIdealOf x).asIdeal.primeCompl) e
  have hvu : (v : Γ(X, O)) * (u : Γ(X, O)) ∈ Q := by
    rw [hQ]; exact Ideal.mem_span_singleton'.mpr ⟨(v : Γ(X, O)) * b, by linear_combination -hv⟩
  have hvu' : (v : Γ(X, O)) * (u : Γ(X, O)) ∉ p := by
    rw [← hxp]; exact (hO.primeIdealOf x).asIdeal.primeCompl.mul_mem v.2 u.2
  exact hvu' (hQp hvu)
end LocGen
end
end ReciprocityTheory.AnForm.R
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {U : W.affineOpens} (s a : Γ(W, U))
    (ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen s → W.presheaf.germ U.1 z hz a ∈ dsK V g z)
    (c : ι') (t : Γ(W, U)) (htc : W.basicOpen t ≤ V c) :
    ∃ m : ℕ, ∀ z (hz : z ∈ W.basicOpen t),
      W.presheaf.germ U.1 z (W.basicOpen_le t hz) (s ^ m * a) ∈ dsK V g z := by
  have hOU : W.basicOpen t ≤ U.1 := W.basicOpen_le t
  have hO : IsAffineOpen (W.basicOpen t) := U.2.basicOpen t
  let ρ := W.presheaf.map (homOfLE hOU).op
  let g' : Γ(W, W.basicOpen t) := W.presheaf.map (homOfLE htc).op (g c)
  have gU : ∀ z (hz : z ∈ W.basicOpen t) (f : Γ(W, U)),
      W.presheaf.germ (W.basicOpen t) z hz (ρ f) = W.presheaf.germ U.1 z (hOU hz) f :=
    fun z hz f => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gV : ∀ z (hz : z ∈ W.basicOpen t),
      W.presheaf.germ (W.basicOpen t) z hz g' = W.presheaf.germ (V c) z (htc hz) (g c) :=
    fun z hz => TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hK : ∀ z (hz : z ∈ W.basicOpen t),
      dsK V g z = Ideal.span {W.presheaf.germ (W.basicOpen t) z hz g'} := by
    intro z hz; rw [gV z hz]; exact dsK_eq hg c (htc hz)
  obtain ⟨m, hm⟩ := exists_pow_mul_mem_span_of_germ_mem hO (ρ s) (ρ a) g' (by
    intro z hz hu
    rw [← hK z hz, gU z hz]
    apply ha z (hOU hz)
    have hu' : IsUnit (W.presheaf.germ U.1 z (hOU hz) s) := by rw [← gU z hz]; exact hu
    first
    | exact (Scheme.mem_basicOpen W s z (hOU hz)).mpr hu'
    | exact (W.mem_basicOpen s z (hOU hz)).mpr hu'
    | simpa [Scheme.mem_basicOpen] using hu')
  refine ⟨m, fun z hz => ?_⟩
  rw [hK z hz, ← gU z hz]
  first
  | rw [map_mul, map_pow]
  | simp only [map_mul, map_pow]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hm
  rw [← hy, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
end ReciprocityTheory.AnForm.R
