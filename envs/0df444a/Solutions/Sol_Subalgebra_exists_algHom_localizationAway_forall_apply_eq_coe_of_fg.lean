-- Prove2me | solution 1 for Subalgebra.exists_algHom_localizationAway_forall_apply_eq_coe_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/646bcc11-afad-5fd0-9d70-a1e9c730a0b7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg

set_option autoImplicit false

universe u

namespace H2bBridge

open IsLocalization

variable {R : Type u} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]

noncomputable def awayToAtPrime (r : R) (hr : r ∉ 𝔭) :
    Localization.Away r →ₐ[R] Localization.AtPrime 𝔭 :=
  IsLocalization.liftAlgHom (M := Submonoid.powers r) (S := Localization.Away r)
    (f := Algebra.ofId R (Localization.AtPrime 𝔭)) (fun y => by
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      rw [Algebra.ofId_apply, ← hk, map_pow]
      exact IsUnit.pow _ (IsLocalization.map_units (Localization.AtPrime 𝔭) (⟨r, hr⟩ : 𝔭.primeCompl)))

noncomputable def awayToAway (u r : R) (h : u ∣ r) :
    Localization.Away u →ₐ[R] Localization.Away r :=
  IsLocalization.liftAlgHom (M := Submonoid.powers u) (S := Localization.Away u)
    (f := Algebra.ofId R (Localization.Away r)) (fun y => by
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      rw [Algebra.ofId_apply, ← hk, map_pow]
      exact IsUnit.pow _ ((IsLocalization.Away.algebraMap_isUnit_iff r).mpr ⟨1, by simpa using h⟩))

end H2bBridge

open IsLocalization H2bBridge in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (T : Subalgebra R (Localization.AtPrime 𝔭)) (hT : T.FG) :
    ∃ (r : R) (_ : r ∉ 𝔭) (ψ : ↥T →ₐ[R] Localization.Away r),
      ∀ (π : Localization.Away r →ₐ[R] Localization.AtPrime 𝔭) (x : ↥T),
        π (ψ x) = (x : Localization.AtPrime 𝔭) := by
  classical

  have hft : Algebra.FiniteType R ↥T := (Subalgebra.fg_iff_finiteType T).mp hT
  have hfp : Algebra.FinitePresentation R ↥T := Algebra.FinitePresentation.of_finiteType.mp hft
  obtain ⟨n, F, hF, hker⟩ := hfp.out
  obtain ⟨G, hG⟩ := hker

  have hsurj : ∀ i : Fin n, ∃ x : R × 𝔭.primeCompl,
      ((F (MvPolynomial.X i) : ↥T) : Localization.AtPrime 𝔭) * algebraMap R _ (x.2 : R) = algebraMap R _ x.1 :=
    fun i => IsLocalization.surj 𝔭.primeCompl _
  choose au hau using hsurj

  let u : 𝔭.primeCompl := ∏ i, (au i).2
  let c : Fin n → 𝔭.primeCompl := fun i => ∏ j ∈ Finset.univ.erase i, (au j).2
  have huc : ∀ i, ((au i).2 : R) * (c i : R) = (u : R) := by
    intro i
    rw [← Submonoid.coe_mul]
    congr 1
    exact Finset.mul_prod_erase Finset.univ (fun j => (au j).2) (Finset.mem_univ i)

  let w : Fin n → Localization.Away (u : R) := fun i =>
    IsLocalization.mk' (Localization.Away (u : R)) ((au i).1 * (c i : R))
      (⟨(u : R), Submonoid.mem_powers _⟩ : Submonoid.powers (u : R))
  have hw : ∀ i, w i * algebraMap R _ (u : R) = algebraMap R _ ((au i).1 * (c i : R)) := fun i =>
    IsLocalization.mk'_spec (Localization.Away (u : R)) _ _
  let φ : MvPolynomial (Fin n) R →ₐ[R] Localization.Away (u : R) := MvPolynomial.aeval w
  have hφX : ∀ i, φ (MvPolynomial.X i) = w i := fun i => MvPolynomial.aeval_X w i
  let π : Localization.Away (u : R) →ₐ[R] Localization.AtPrime 𝔭 := awayToAtPrime 𝔭 (u : R) u.2
  have huS : IsUnit (algebraMap R (Localization.AtPrime 𝔭) (u : R)) := IsLocalization.map_units _ u

  have h1 : ∀ i, π (w i) = ((F (MvPolynomial.X i) : ↥T) : Localization.AtPrime 𝔭) := by
    intro i
    have hl : π (w i) * algebraMap R (Localization.AtPrime 𝔭) (u : R) =
        algebraMap R (Localization.AtPrime 𝔭) ((au i).1 * (c i : R)) := by
      rw [← AlgHom.commutes π (u : R), ← map_mul, hw, AlgHom.commutes]
    have hr' : ((F (MvPolynomial.X i) : ↥T) : Localization.AtPrime 𝔭) * algebraMap R (Localization.AtPrime 𝔭) (u : R) =
        algebraMap R (Localization.AtPrime 𝔭) ((au i).1 * (c i : R)) := by
      rw [← huc i, map_mul, ← mul_assoc, hau i, ← map_mul]
    exact huS.mul_left_inj.mp (hl.trans hr'.symm)
  have h1' : π.comp φ = T.val.comp F := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hφX, h1 i]
    rfl

  have hkill : ∀ g ∈ G, ∃ m : 𝔭.primeCompl, ∃ b : R, ∃ k : ℕ,
      φ g * algebraMap R _ ((u : R) ^ k) = algebraMap R _ b ∧ (m : R) * b = 0 := by
    intro g hg
    obtain ⟨⟨b, ⟨y, k, hk⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (u : R)) (φ g)
    simp only at hb
    have hg0 : F g = 0 := by
      have : g ∈ RingHom.ker F.toRingHom := by rw [← hG]; exact Ideal.subset_span hg
      exact this
    have hπφ : π (φ g) = 0 := by
      have := congrArg (fun h => h g) (congrArg DFunLike.coe h1')
      simp only [AlgHom.coe_comp, Function.comp_apply, hg0, map_zero] at this
      exact this
    have hb0 : algebraMap R (Localization.AtPrime 𝔭) b = 0 := by
      have := congrArg π hb
      rw [map_mul, AlgHom.commutes, AlgHom.commutes, hπφ, zero_mul] at this
      exact this.symm
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl _ b).mp hb0
    exact ⟨m, b, k, by subst hk; simpa using hb, hm⟩
  choose vg bg kg hvg using hkill
  let v : 𝔭.primeCompl := ∏ g : ↥G, vg g.1 g.2
  let r : R := (u : R) * (v : R)
  have hr : r ∉ 𝔭 := (u * v).2
  have hur : (u : R) ∣ r := ⟨v, rfl⟩
  have hvr : ∀ g (hg : g ∈ G), (vg g hg : R) ∣ r := by
    intro g hg
    refine Dvd.dvd.mul_left ?_ _
    have : vg g hg ∣ v := Finset.dvd_prod_of_mem (fun g' : ↥G => vg g'.1 g'.2) (Finset.mem_univ ⟨g, hg⟩)
    obtain ⟨z, hz⟩ := this
    exact ⟨z, by rw [hz, Submonoid.coe_mul]⟩
  let ρ : Localization.Away (u : R) →ₐ[R] Localization.Away r := awayToAway (u : R) r hur

  have h3 : ∀ g ∈ G, ρ (φ g) = 0 := by
    intro g hg
    obtain ⟨hb, hm⟩ := hvg g hg
    have hvunit : IsUnit (algebraMap R (Localization.Away r) (vg g hg : R)) :=
      (IsLocalization.Away.algebraMap_isUnit_iff r).mpr ⟨1, by rw [pow_one]; exact hvr g hg⟩
    have huunit : IsUnit (algebraMap R (Localization.Away r) ((u : R) ^ kg g hg)) := by
      rw [map_pow]
      exact IsUnit.pow _ ((IsLocalization.Away.algebraMap_isUnit_iff r).mpr ⟨1, by rw [pow_one]; exact hur⟩)
    have hb0 : algebraMap R (Localization.Away r) (bg g hg) = 0 := by
      rw [← hvunit.mul_right_eq_zero, ← map_mul, hm, map_zero]
    rw [← huunit.mul_left_eq_zero, ← AlgHom.commutes ρ, ← map_mul, hb, AlgHom.commutes, hb0]
  have hle : ∀ a ∈ RingHom.ker F.toRingHom, (ρ.comp φ) a = 0 := by
    intro a ha
    rw [← hG] at ha
    refine Submodule.span_induction (p := fun a _ => (ρ.comp φ) a = 0) ?_ ?_ ?_ ?_ ha
    · intro g hg; exact h3 g hg
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]

  let ψ : ↥T →ₐ[R] Localization.Away r :=
    (Ideal.Quotient.liftₐ (RingHom.ker F.toRingHom) (ρ.comp φ) hle).comp
      (Ideal.quotientKerAlgEquivOfSurjective hF).symm.toAlgHom
  have hψ : ∀ p, ψ (F p) = ρ (φ p) := by
    intro p
    change Ideal.Quotient.liftₐ (RingHom.ker F.toRingHom) (ρ.comp φ) hle
      ((Ideal.quotientKerAlgEquivOfSurjective hF).symm (F p)) = _
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    rfl
  refine ⟨r, hr, ψ, ?_⟩
  intro π' x
  obtain ⟨p, rfl⟩ := hF x
  haveI : Subsingleton (Localization.Away (u : R) →ₐ[R] Localization.AtPrime 𝔭) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (u : R))
  have hππ : π'.comp ρ = π := Subsingleton.elim _ _
  rw [hψ, ← AlgHom.comp_apply, hππ]
  have := congrArg (fun h => h p) (congrArg DFunLike.coe h1')
  simpa using this

end S_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg
end P2MW
export P2MW.S_Subalgebra_exists_algHom_localizationAway_forall_apply_eq_coe_of_fg (solution)
