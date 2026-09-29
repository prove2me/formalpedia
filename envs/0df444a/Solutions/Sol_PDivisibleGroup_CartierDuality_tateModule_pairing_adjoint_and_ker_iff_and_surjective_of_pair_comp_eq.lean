-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fdc7e0c3-5074-59af-821d-f767a0c80c78

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_CartierDuality
import Theorems.Thm_PDivisibleGroup_CartierDuality_bijective_tateModule_pairing_of_isAlgClosed
import Theorems.Thm_PDivisibleGroup_nonempty_basis_tateModule_points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

namespace LinearMap p2m_export "LinearMap" "range sub_apply id codRestrict_apply module codRestrict zero_apply flip mk id_apply ext comp flip_apply ker comp_apply mem_range_self" end LinearMap
p2m_open_scoped "LinearMap" in
theorem LinearMap.surjective_of_forall_pair_eq_of_injective_of_saturated_c3b
    {S : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
    {V W V' W' U : Type*} [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W]
    [AddCommGroup V'] [Module S V'] [AddCommGroup W'] [Module S W'] [AddCommGroup U] [Module S U]
    [Module.Finite S V]
    (B : V →ₗ[S] W →ₗ[S] U) (BE : V' →ₗ[S] W' →ₗ[S] U)
    (hB : Function.Surjective B.flip) (hBE : Function.Injective BE.flip)
    (Tφ : V' →ₗ[S] V) (Tψ : W →ₗ[S] W')
    (hadj : ∀ x y, B (Tφ x) y = BE x (Tψ y))
    (hinj : Function.Injective Tφ)
    (hsat : ∀ (r : S) (z : V), r ≠ 0 → r • z ∈ LinearMap.range Tφ → z ∈ LinearMap.range Tφ) :
    Function.Surjective Tψ := by
  classical

  haveI : Module.Finite S (V ⧸ LinearMap.range Tφ) := Module.Finite.quotient S _
  haveI : Module.IsTorsionFree S (V ⧸ LinearMap.range Tφ) := by
    refine ⟨fun r hr a b hab => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    induction a using Submodule.Quotient.induction_on with | _ a => ?_
    induction b using Submodule.Quotient.induction_on with | _ b => ?_
    have hab' : r • Submodule.Quotient.mk (p := LinearMap.range Tφ) a =
        r • Submodule.Quotient.mk (p := LinearMap.range Tφ) b := hab
    rw [← sub_eq_zero, ← smul_sub, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at hab'
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    exact hsat r (a - b) hr0 hab'
  haveI : Module.Free S (V ⧸ LinearMap.range Tφ) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Projective S (V ⧸ LinearMap.range Tφ) := Module.Projective.of_free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range Tφ).mkQ
    (LinearMap.id : (V ⧸ LinearMap.range Tφ) →ₗ[S] (V ⧸ LinearMap.range Tφ)) (Submodule.mkQ_surjective _)

  have hπ : ∀ v : V, ((LinearMap.id : V →ₗ[S] V) - s ∘ₗ (LinearMap.range Tφ).mkQ) v ∈ LinearMap.range Tφ := fun v => by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub,
      LinearMap.comp_apply, ← LinearMap.comp_apply (f := (LinearMap.range Tφ).mkQ) (g := s), hs,
      LinearMap.id_apply, LinearMap.id_apply, sub_self]
  let π : V →ₗ[S] LinearMap.range Tφ := LinearMap.codRestrict (LinearMap.range Tφ) _ hπ
  let e : V' ≃ₗ[S] LinearMap.range Tφ := LinearEquiv.ofInjective Tφ hinj
  have hπφ : ∀ x : V', π (Tφ x) = e x := fun x => by
    apply Subtype.ext
    rw [LinearMap.codRestrict_apply, LinearEquiv.ofInjective_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self Tφ x), map_zero,
      LinearMap.id_apply, sub_zero]
  intro z

  let g : V →ₗ[S] U := (BE.flip z) ∘ₗ (e.symm : LinearMap.range Tφ →ₗ[S] V') ∘ₗ π
  have hg : ∀ x : V', g (Tφ x) = BE x z := fun x => by
    show BE.flip z (e.symm (π (Tφ x))) = BE x z
    rw [hπφ, LinearEquiv.symm_apply_apply, LinearMap.flip_apply]
  obtain ⟨y, hy⟩ := hB g
  refine ⟨y, hBE ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.flip_apply, LinearMap.flip_apply, ← hadj, ← hg, ← hy, LinearMap.flip_apply]

p2m_open_scoped "LinearMap" in
theorem LinearMap.transpose_eq_zero_iff_c3b
    {S : Type*} [CommRing S]
    {V W V' W' U : Type*} [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W]
    [AddCommGroup V'] [Module S V'] [AddCommGroup W'] [Module S W'] [AddCommGroup U] [Module S U]
    (B : V →ₗ[S] W →ₗ[S] U) (BE : V' →ₗ[S] W' →ₗ[S] U) (hBE : Function.Injective BE.flip)
    (Tφ : V' →ₗ[S] V) (Tψ : W →ₗ[S] W')
    (hadj : ∀ x y, B (Tφ x) y = BE x (Tψ y)) (y : W) :
    Tψ y = 0 ↔ ∀ x : V', B (Tφ x) y = 0 := by
  constructor
  · intro hy x
    rw [hadj, hy, map_zero]
  · intro h
    apply hBE
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.flip_apply, ← hadj, h, map_zero, LinearMap.zero_apply]

namespace PDivisibleGroup p2m_export "PDivisibleGroup" "Point Point.toAlgHom Point.ofAlgHom pointInclLE exists_pointInclLE_eq_of_pow_eq_one Points pointsMkAdd pointsMkAdd_pointInclLE Points.exists_mkAdd pointsMkAdd_eq_pointsMkAdd_iff level mk CartierDuality CartierDuality.bijective_tateModule_pairing_of_isAlgClosed nonempty_basis_tateModule_points" end PDivisibleGroup
p2m_open_scoped "PDivisibleGroup" in
theorem PDivisibleGroup.exists_pointsMkAdd_eq_tateModule_apply_c3b
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)
    (L : Type) [CommRing L] [Algebra R L] (x : TateModule p (G.Points L)) (v : ℕ) :
    ∃ g : G.Point L v, G.pointsMkAdd L v (Additive.ofMul g) = (x : ℕ → G.Points L) v := by
  obtain ⟨w, g0, hg0⟩ := PDivisibleGroup.Points.exists_mkAdd G ((x : ℕ → G.Points L) v)
  have hg1 : G.pointsMkAdd L (max v w) (Additive.ofMul (G.pointInclLE L (le_max_right v w) g0)) =
      (x : ℕ → G.Points L) v := by
    rw [G.pointsMkAdd_pointInclLE, hg0]
  have hpow : G.pointInclLE L (le_max_right v w) g0 ^ (p ^ v) = 1 := by
    have ht := TateModule.torsion x v
    rw [natCast_zsmul] at ht
    have h1 : G.pointsMkAdd L (max v w) (Additive.ofMul (G.pointInclLE L (le_max_right v w) g0 ^ (p ^ v))) =
        G.pointsMkAdd L (max v w) (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, hg1, ofMul_one, map_zero, ht]
    exact (G.pointsMkAdd_eq_pointsMkAdd_iff _ _).1 h1
  obtain ⟨g, hg⟩ := G.exists_pointInclLE_eq_of_pow_eq_one (le_max_left v w) _ hpow
  exact ⟨g, by rw [← hg1, ← hg, G.pointsMkAdd_pointInclLE]⟩

theorem solution
    {R : Type} [CommRing R] {p h h' : ℕ} [Fact p.Prime]
    {A A' : PDivisibleGroup R p h} (D : A.CartierDuality A')
    {Γ Γ' : PDivisibleGroup R p h'} (E : Γ.CartierDuality Γ')
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L]
    (B : TateModule p (A.Points L) →ₗ[ℤ_[p]] TateModule p (A'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hB : (∀ (x : TateModule p (A.Points L)) (y : TateModule p (A'.Points L)) (v : ℕ)
        (f : A.Point L v) (g : A'.Point L v),
        A.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → A.Points L) v →
        A'.pointsMkAdd L v (Additive.ofMul g) = (y : ℕ → A'.Points L) v →
        ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f g))
    (BE : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (Γ'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ))
    (hBE : (∀ (x : TateModule p (Γ.Points L)) (y : TateModule p (Γ'.Points L)) (v : ℕ)
        (f : Γ.Point L v) (g : Γ'.Point L v),
        Γ.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → Γ.Points L) v →
        Γ'.pointsMkAdd L v (Additive.ofMul g) = (y : ℕ → Γ'.Points L) v →
        ((Additive.toMul ((BE x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = E.pair L v f g))
    (φ : ∀ v : ℕ, A.level v →ₐc[R] Γ.level v) (ψ : ∀ v : ℕ, Γ'.level v →ₐc[R] A'.level v)
    (hadj : ∀ (v : ℕ) (x : Γ.Point L v) (y : A'.Point L v),
      D.pair L v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp
          (φ v : A.level v →ₐ[R] Γ.level v))) y =
        E.pair L v x (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp
          (ψ v : Γ'.level v →ₐ[R] A'.level v))))
    (Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (A.Points L))
    (hTφ : ∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (A.Points L)) : ℕ → A.Points L) n =
          A.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : A.level w →ₐ[R] Γ.level w)))))
    (Tψ : TateModule p (A'.Points L) →ₗ[ℤ_[p]] TateModule p (Γ'.Points L))
    (hTψ : ∀ (y : TateModule p (A'.Points L)) (n w : ℕ) (g : A'.Point L w),
        A'.pointsMkAdd L w (Additive.ofMul g) = (y : ℕ → A'.Points L) n →
        ((Tψ y : TateModule p (Γ'.Points L)) : ℕ → Γ'.Points L) n =
          Γ'.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (ψ w : Γ'.level w →ₐ[R] A'.level w))))) :
    (∀ (x : TateModule p (Γ.Points L)) (y : TateModule p (A'.Points L)), B (Tφ x) y = BE x (Tψ y)) ∧
    (∀ y : TateModule p (A'.Points L), Tψ y = 0 ↔ ∀ x : TateModule p (Γ.Points L), B (Tφ x) y = 0) ∧
    ((Function.Injective Tφ ∧
        ∀ (r : ℤ_[p]) (z : TateModule p (A.Points L)), r ≠ 0 → r • z ∈ LinearMap.range Tφ →
          z ∈ LinearMap.range Tφ) →
      Function.Surjective Tψ) := by
  classical

  have hBbij := PDivisibleGroup.CartierDuality.bijective_tateModule_pairing_of_isAlgClosed D L B hB
  have hBEbij := PDivisibleGroup.CartierDuality.bijective_tateModule_pairing_of_isAlgClosed E L BE hBE

  have hi : ∀ (x : TateModule p (Γ.Points L)) (y : TateModule p (A'.Points L)), B (Tφ x) y = BE x (Tψ y) := by
    intro x y
    refine Subtype.ext (funext fun v => ?_)
    obtain ⟨gx, hgx⟩ := PDivisibleGroup.exists_pointsMkAdd_eq_tateModule_apply_c3b Γ L x v
    obtain ⟨gy, hgy⟩ := PDivisibleGroup.exists_pointsMkAdd_eq_tateModule_apply_c3b A' L y v
    have h1 := hTφ x v v gx hgx
    have h2 := hTψ y v v gy hgy
    have h3 := hB (Tφ x) y v (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom gx).comp
      (φ v : A.level v →ₐ[R] Γ.level v))) gy h1.symm hgy
    have h4 := hBE x (Tψ y) v gx (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom gy).comp
      (ψ v : Γ'.level v →ₐ[R] A'.level v))) hgx h2.symm
    have h5 := hadj v gx gy
    apply Additive.toMul.injective
    apply Units.ext
    rw [h3, h4, h5]
  refine ⟨hi, ?_, ?_⟩
  ·
    intro y
    exact LinearMap.transpose_eq_zero_iff_c3b B BE hBEbij.1.injective Tφ Tψ hi y
  ·
    rintro ⟨hinj, hsat⟩
    obtain ⟨b⟩ := PDivisibleGroup.nonempty_basis_tateModule_points A L
    haveI : Module.Finite ℤ_[p] (TateModule p (A.Points L)) := Module.Finite.of_basis b
    exact LinearMap.surjective_of_forall_pair_eq_of_injective_of_saturated_c3b B BE hBbij.1.surjective
      hBEbij.1.injective Tφ Tψ hi hinj hsat

end S_PDivisibleGroup_CartierDuality_tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_tateModule_pairing_adjoint_and_ker_iff_and_surjective_of_pair_comp_eq (solution)
