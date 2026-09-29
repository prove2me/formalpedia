-- Prove2me | solution 1 for Rep.nonempty_splitting_of_isZero_H1_ihom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/7feb8f48-d972-5367-8dfe-ac9fc4dc1ec3

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_splitting_of_isZero_H1_ihom

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

set_option maxHeartbeats 3200000

theorem solution {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) [Module.Free k X.X₃]
    (h : CategoryTheory.Limits.IsZero (groupCohomology ((ihom X.X₃).obj X.X₁) 1)) :
    Nonempty X.Splitting := by
  classical
  have zelt : ∀ {M : ModuleCat.{u} k}, CategoryTheory.Limits.IsZero M → ∀ x : M, x = 0 := fun hM x => by
    simpa using congrArg (fun ψ => ψ.hom x) (hM.eq_of_src (𝟙 _) 0)
  have hfinj := Rep.seam_f_injective hX
  have hgsurj := Rep.seam_g_surjective hX
  have hfρ : ∀ (g : G) (x : X.X₁), X.f.hom (X.X₁.ρ g x) = X.X₂.ρ g (X.f.hom x) := fun g x => Rep.hom_comm_apply X.f g x
  have hgρ : ∀ (g : G) (y : X.X₂), X.g.hom (X.X₂.ρ g y) = X.X₃.ρ g (X.g.hom y) := fun g y => Rep.hom_comm_apply X.g g y
  have ρinv₃ : ∀ (g : G) (z : X.X₃), X.X₃.ρ g (X.X₃.ρ g⁻¹ z) = z := fun g z => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

  let b := Module.Free.chooseBasis k X.X₃
  let s₀ : X.X₃ →ₗ[k] X.X₂ := b.constr k fun i => Classical.choose (hgsurj (b i))
  have hs₀ : ∀ z, X.g.hom (s₀ z) = z := by
    have : X.g.hom.toLinearMap ∘ₗ s₀ = LinearMap.id := b.ext fun i => by
      rw [LinearMap.comp_apply, Module.Basis.constr_basis, LinearMap.id_apply]
      exact Classical.choose_spec (hgsurj (b i))
    exact fun z => LinearMap.congr_fun this z

  let d : G → (X.X₃ →ₗ[k] X.X₂) := fun g => X.X₂.ρ g ∘ₗ s₀ ∘ₗ X.X₃.ρ g⁻¹ - s₀
  have hd : ∀ g z, d g z = X.X₂.ρ g (s₀ (X.X₃.ρ g⁻¹ z)) - s₀ z := fun g z => rfl
  have hgd : ∀ g z, X.g.hom (d g z) = 0 := fun g z => by
    rw [hd, map_sub, hgρ, hs₀, hs₀, ρinv₃, sub_self]
  have hdmem : ∀ g z, d g z ∈ LinearMap.range X.f.hom.toLinearMap := fun g z => by
    rw [Rep.seam_range_eq_ker hX, LinearMap.mem_ker]
    exact hgd g z
  let c : G → (X.X₃ →ₗ[k] X.X₁) := fun g =>
    (LinearEquiv.ofInjective X.f.hom.toLinearMap hfinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (d g) (hdmem g)
  have hfc : ∀ g z, X.f.hom (c g z) = d g z := fun g z =>
    congrArg Subtype.val ((LinearEquiv.ofInjective X.f.hom.toLinearMap hfinj).apply_symm_apply ⟨d g z, hdmem g z⟩)

  let A : Rep.{u} k G := (ihom X.X₃).obj X.X₁
  let toA : (X.X₃ →ₗ[k] X.X₁) → A := fun t => t
  let ofA : A → (X.X₃ →ₗ[k] X.X₁) := fun t => t
  have hAρ : ∀ (g : G) (t : A), ofA (A.ρ g t) = X.X₁.ρ g ∘ₗ ofA t ∘ₗ X.X₃.ρ g⁻¹ := fun g t =>
    Rep.ihom_obj_ρ_apply g (ofA t)
  have hAρz : ∀ (g : G) (t : A) (z : X.X₃), ofA (A.ρ g t) z = X.X₁.ρ g (ofA t (X.X₃.ρ g⁻¹ z)) := fun g t z =>
    LinearMap.congr_fun (hAρ g t) z
  let c' : G → A := fun g => toA (c g)

  have hc : c' ∈ groupCohomology.cocycles₁ A := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g g'
    change toA (c (g * g')) = toA (ofA (A.ρ g (c' g')) + c g)
    congr 1
    apply LinearMap.ext
    intro z
    apply hfinj
    rw [LinearMap.add_apply, map_add, hAρz, hfρ]
    change X.f.hom (c (g * g') z) = X.X₂.ρ g (X.f.hom (c g' (X.X₃.ρ g⁻¹ z))) + X.f.hom (c g z)
    rw [hfc, hfc, hfc, hd, hd, hd, map_sub, mul_inv_rev, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply]
    abel

  have hcob : (c' : G → A) ∈ groupCohomology.coboundaries₁ A :=
    (groupCohomology.H1π_eq_zero_iff (⟨c', hc⟩ : groupCohomology.cocycles₁ A)).1 (zelt h _)
  obtain ⟨t, ht⟩ := hcob
  have ht' : ∀ g z, X.X₁.ρ g (ofA t (X.X₃.ρ g⁻¹ z)) - ofA t z = c g z := fun g z => by
    have h1 : A.ρ g t - t = c' g := by
      have := congrFun ht g
      rwa [groupCohomology.d₀₁_hom_apply] at this
    have h2 : ofA (A.ρ g t) - ofA t = c g := h1
    rw [← hAρz, ← h2, LinearMap.sub_apply]

  let s : X.X₃ →ₗ[k] X.X₂ := s₀ - X.f.hom.toLinearMap ∘ₗ ofA t
  have hs : ∀ z, s z = s₀ z - X.f.hom (ofA t z) := fun z => rfl
  have hsg : ∀ z, X.g.hom (s z) = z := fun z => by
    rw [hs, map_sub, hs₀]
    have hm : X.f.hom (ofA t z) ∈ LinearMap.ker X.g.hom.toLinearMap := by
      rw [← Rep.seam_range_eq_ker hX]; exact ⟨ofA t z, rfl⟩
    rw [LinearMap.mem_ker] at hm
    change X.g.hom (X.f.hom (ofA t z)) = 0 at hm
    rw [hm, sub_zero]
  have hsequiv : ∀ g : G, s ∘ₗ X.X₃.ρ g = X.X₂.ρ g ∘ₗ s := by
    intro g
    apply LinearMap.ext
    intro z
    change s (X.X₃.ρ g z) = X.X₂.ρ g (s z)
    have key : ∀ w, X.X₂.ρ g (s (X.X₃.ρ g⁻¹ w)) = s w := fun w => by
      rw [hs, hs, map_sub, ← hfρ]
      have e1 : X.X₂.ρ g (s₀ (X.X₃.ρ g⁻¹ w)) = s₀ w + d g w := by rw [hd]; abel
      have e2 : X.f.hom (X.X₁.ρ g (ofA t (X.X₃.ρ g⁻¹ w))) = X.f.hom (c g w) + X.f.hom (ofA t w) := by
        rw [← map_add, ← ht' g w]; congr 1; abel
      rw [e1, e2, hfc]
      abel
    have := key (X.X₃.ρ g z)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

  let σ : X.X₃ ⟶ X.X₂ := Rep.ofHom ⟨s, hsequiv⟩
  have hσ : σ ≫ X.g = 𝟙 X.X₃ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => hsg z))
  exact ⟨ShortComplex.Splitting.ofExactOfSection X hX.exact σ hσ hX.mono_f⟩

end S_Rep_nonempty_splitting_of_isZero_H1_ihom
end P2MW
export P2MW.S_Rep_nonempty_splitting_of_isZero_H1_ihom (solution)
