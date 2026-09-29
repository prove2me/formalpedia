-- Prove2me | solution 1 for WeierstrassCurve.not_forall_apOfModel_eq_two_of_modRepIsIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/45908d24-fdc6-57d3-b01d-8a132baad43d

import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_NumberField_exists_isFrobenius_lift_arithFrobAt
import Theorems.Thm_NumberField_exists_valuationSubring_eq_localization
import Theorems.Thm_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem
import Theorems.Thm_WeierstrassCurve_galoisTrace_frobenius_eq_apOfModel
import Theorems.Thm_WeierstrassCurve_det_galoisRep_frobenius_eq_prime
import Theorems.Thm_WeierstrassCurve_finrank_torsionBy_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_isOpen_torsionBy_fixingSubgroup
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_rootOfUnity_eq_pow_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_not_forall_apOfModel_eq_two_of_modRepIsIrreducible
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "FrobeniusEndo.linePencil_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"
set_option autoImplicit false

open scoped NumberField

namespace TraceTwoObstruction

section Core

variable {p : ℕ} [hp : Fact p.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

private theorem toMatrix_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι (ZMod p) V)
    (e : Module.End (ZMod p) V) (n : ℕ) :
    LinearMap.toMatrix b b (e ^ n) = (LinearMap.toMatrix b b e) ^ n := by
  induction n with
  | zero => simp [LinearMap.toMatrix_one]
  | succ n ih => rw [pow_succ, pow_succ, LinearMap.toMatrix_mul, ih]

private theorem pow_eq_one_of_trace_eq_two_of_det_eq_one (h2 : Module.finrank (ZMod p) V = 2)
    (e : Module.End (ZMod p) V) (htr : LinearMap.trace (ZMod p) V e = 2) (hdet : LinearMap.det e = 1) :
    e ^ p = 1 := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.finite_of_finrank_eq_succ h2
  let b : Module.Basis (Fin 2) (ZMod p) V := Module.finBasisOfFinrankEq (ZMod p) V h2
  set M : Matrix (Fin 2) (Fin 2) (ZMod p) := LinearMap.toMatrix b b e with hM
  have htrM : M.trace = 2 := by
    rw [LinearMap.trace_eq_matrix_trace (ZMod p) b e] at htr
    exact htr
  have hdetM : M.det = 1 := by rw [hM, LinearMap.det_toMatrix]; exact hdet
  have hCH : M ^ 2 = (2 : ZMod p) • M - (1 : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [Matrix.sq_eq_trace_smul_sub_det_smul_one, htrM, hdetM]
  have hnil : (M - 1) ^ 2 = 0 := by
    have h : (M - 1) ^ 2 = M ^ 2 - M - M + 1 := by
      rw [sq, sub_mul, mul_sub, mul_sub, one_mul, mul_one, mul_one, sq]
      abel
    rw [h, hCH, two_smul, one_smul]
    abel
  have hMp : M ^ p = 1 := by
    have h1 : (M - 1) ^ p = M ^ p - 1 ^ p := sub_pow_char_of_commute _ (Commute.one_right M)
    have h0 : (M - 1) ^ p = 0 := by
      obtain ⟨m, hm⟩ : ∃ m, p = 2 + m := ⟨p - 2, by have := hp.out.two_le; omega⟩
      have hsplit : (M - 1) ^ p = (M - 1) ^ 2 * (M - 1) ^ m := by rw [← pow_add, ← hm]
      rw [hsplit, hnil, zero_mul]
    rw [h0, one_pow, eq_comm, sub_eq_zero] at h1
    exact h1
  apply (LinearMap.toMatrix b b).injective
  rw [toMatrix_pow, LinearMap.toMatrix_one]
  exact hMp

private theorem core_false {G : Type*} [Group G] (ρ : G →* Module.End (ZMod p) V)
    (h2 : Module.finrank (ZMod p) V = 2)
    (hirr : ∀ N : Submodule (ZMod p) V, (∀ g : G, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤)
    (H : Subgroup G) [hN : H.Normal] (hab : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ H)
    (hH : ∀ h ∈ H, ρ h ^ p = 1)
    (hp2 : p ≠ 2) (t : G) (ht : t ^ 2 ∈ H) (hdet : LinearMap.det (ρ t) = -1) : False := by
  classical
  haveI : Module.Finite (ZMod p) V := Module.finite_of_finrank_eq_succ h2
  haveI : Finite V := Module.finite_of_finite (ZMod p)

  have hneg : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2' : ((2 : ℕ) : ZMod p) = 0 := by
      have h2'' : (2 : ZMod p) = 0 := by linear_combination -h
      exact_mod_cast h2''
    have := (ZMod.natCast_eq_zero_iff 2 p).mp h2'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

  let ρH : H →* (Module.End (ZMod p) V)ˣ := (ρ.comp H.subtype).toHomUnits
  let P : Subgroup (Module.End (ZMod p) V)ˣ := ρH.range
  have hP : IsPGroup p P := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨h, hh⟩, rfl⟩ := hx
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    apply Units.ext
    simp only [P, ρH, SubgroupClass.coe_pow, OneMemClass.coe_one, Units.val_pow_eq_pow_val, Units.val_one,
      MonoidHom.coe_toHomUnits, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact hH h hh
  letI : MulAction P V :=
    { smul := fun x v => ((x : (Module.End (ZMod p) V)ˣ) : Module.End (ZMod p) V) v
      one_smul := fun v => rfl
      mul_smul := fun x y v => rfl }
  have hzero : (0 : V) ∈ MulAction.fixedPoints P V := fun x => map_zero _
  have hcard : p ∣ Nat.card V := by
    have hV : Nat.card V = p ^ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, h2]
    rw [hV]
    exact dvd_pow_self p two_ne_zero
  obtain ⟨v, hv, hv0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hcard hzero

  let Vfix : Submodule (ZMod p) V :=
    { carrier := {w | ∀ h ∈ H, ρ h w = w}
      add_mem' := fun {a b} ha hb h hh => by rw [map_add, ha h hh, hb h hh]
      zero_mem' := fun h _ => map_zero _
      smul_mem' := fun c {a} ha h hh => by rw [map_smul, ha h hh] }
  have hVfix_stable : ∀ g : G, ∀ x ∈ Vfix, ρ g x ∈ Vfix := by
    intro g x hx h hh
    have hconj : g⁻¹ * h * g ∈ H := by
      have := hN.conj_mem h hh g⁻¹
      simpa using this
    have e1 : h * g = g * (g⁻¹ * h * g) := by group
    calc ρ h (ρ g x) = ρ (h * g) x := by rw [map_mul]; rfl
      _ = ρ g (ρ (g⁻¹ * h * g) x) := by rw [e1, map_mul]; rfl
      _ = ρ g x := by rw [hx _ hconj]
  have hv_fix : v ∈ Vfix := by
    intro h hh
    have := hv ⟨ρH ⟨h, hh⟩, ⟨⟨h, hh⟩, rfl⟩⟩
    exact this
  have hVfix_top : Vfix = ⊤ := by
    rcases hirr Vfix hVfix_stable with hbot | htop
    · exfalso
      apply hv0
      have : v ∈ (⊥ : Submodule (ZMod p) V) := hbot ▸ hv_fix
      exact (Submodule.mem_bot _).mp this |>.symm
    · exact htop
  have hHtriv : ∀ h ∈ H, ρ h = 1 := by
    intro h hh
    ext w
    have hw : w ∈ Vfix := hVfix_top ▸ Submodule.mem_top
    exact hw h hh

  set m : Module.End (ZMod p) V := ρ t with hm
  have hm2 : m * m = 1 := by
    rw [hm, ← map_mul, ← sq]
    exact hHtriv _ ht
  have hcomm : ∀ g : G, ρ g * m = m * ρ g := by
    intro g
    have e1 : g * t = (g * t * g⁻¹ * t⁻¹) * (t * g) := by group
    have := congrArg ρ e1
    rw [map_mul, map_mul, hHtriv _ (hab g t), one_mul, map_mul] at this
    simpa [hm] using this
  let N₁ : Submodule (ZMod p) V := LinearMap.ker (m - 1)
  have hN₁_stable : ∀ g : G, ∀ x ∈ N₁, ρ g x ∈ N₁ := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h1 : m (ρ g x) = ρ g (m x) := by
      have := congrArg (fun f : Module.End (ZMod p) V => f x) (hcomm g)
      simpa using this.symm
    rw [LinearMap.sub_apply, Module.End.one_apply, h1]
    have hx' : m x = x := by
      have := hx
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      exact this
    rw [hx', sub_self]
  have hdet1 : LinearMap.det m = 1 := by
    rcases hirr N₁ hN₁_stable with hbot | htop
    ·
      have hinj : Function.Injective ⇑(m - 1) := LinearMap.ker_eq_bot.mp hbot
      have hprod : (m - 1) * (m + 1) = 0 := by
        have hexp : (m - 1) * (m + 1) = m * m - 1 := by noncomm_ring
        rw [hexp, hm2, sub_self]
      have hm_neg : m = -1 := by
        ext w
        have hw : (m - 1) ((m + 1) w) = (m - 1) 0 := by
          rw [map_zero]
          exact congrArg (fun f : Module.End (ZMod p) V => f w) hprod
        have := hinj hw
        rw [LinearMap.add_apply, Module.End.one_apply] at this
        rw [LinearMap.neg_apply, Module.End.one_apply]
        exact eq_neg_of_add_eq_zero_left this
      rw [hm_neg, show (-1 : Module.End (ZMod p) V) = (-1 : ZMod p) • (1 : Module.End (ZMod p) V) by simp,
        LinearMap.det_smul, h2, map_one]
      ring
    · have hm_one : m = 1 := by
        ext w
        have hw : w ∈ N₁ := htop ▸ Submodule.mem_top
        rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
        simpa using hw
      rw [hm_one, map_one]
  exact hneg (hdet.symm.trans hdet1)

end Core

section Galois

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

local notation "Kbar" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

private theorem exists_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) : ∃ μ : Kbar, IsPrimitiveRoot μ n := by
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (n : Kbar) := ⟨by exact_mod_cast hn⟩
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Kbar)
    (Polynomial.degree_cyclotomic_pos n Kbar (Nat.pos_of_ne_zero hn)).ne'
  exact ⟨μ, (Polynomial.isRoot_cyclotomic_iff).mp hμ⟩

private theorem pow_eq_pow_iff {μ : Kbar} {n : ℕ} (hμ : IsPrimitiveRoot μ n) (hn : n ≠ 0) (a b : ℕ) :
    μ ^ a = μ ^ b ↔ a ≡ b [MOD n] := by
  have hfin : IsOfFinOrder μ := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hμ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hμ.eq_orderOf]

private theorem pow_eq_one_of_forall_frobenius {M : Type*} [Monoid M] (ρ : Gal →* M) (p : ℕ)
    (E : IntermediateField ℚ Kbar) [FiniteDimensional ℚ E] [Normal ℚ E]
    (H : Subgroup Gal) (hHn : H.Normal)
    (hfixE : ∀ x : Gal, AlgEquiv.restrictNormalHom E x = 1 → ρ x = 1 ∧ x ∈ H)
    (hagree : ∀ x y : Gal, AlgEquiv.restrictNormalHom E x = AlgEquiv.restrictNormalHom E y → ρ x = ρ y)
    (X : Finset ℕ)
    (hfrobH : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ X → ∀ (A : ValuationSubring Kbar), A.LiesOverPrime ℓ →
      ∀ τ : Gal, A.IsFrobeniusAt τ ℓ → τ ∈ H → ρ τ ^ p = 1) :
    ∀ h ∈ H, ρ h ^ p = 1 := by
  classical
  haveI hEnf : NumberField E := ⟨⟩
  haveI hEgal : IsGalois ℚ E := ⟨⟩
  intro σ hσ
  set σ' : E ≃ₐ[ℚ] E := AlgEquiv.restrictNormalHom E σ with hσ'
  obtain ⟨ℓ, hℓX, hreal⟩ := FrobeniusDensity.statement E σ' X
  obtain ⟨hℓ, hQall⟩ := hreal
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  obtain ⟨Q, -, hQprime, hQcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (FrobeniusDensity.ratPrimeIdeal ℓ) (⊥ : Ideal (𝓞 E))
    (by
      rw [Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 E)) (algebraMap ℤ (𝓞 E)).injective_int]
      exact bot_le)
  haveI := hQprime
  haveI hQover : Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ) := ⟨hQcomap.symm⟩
  haveI hQfin : Finite (𝓞 E ⧸ Q) :=
    FrobeniusDensity.finite_quotient_of_ne_bot (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  obtain ⟨k, hk, hconj⟩ := hQall Q hQprime hQover hQfin

  obtain ⟨Qt, hQtmax, τ, hQtQ, hτres, hstab, hfrob⟩ := NumberField.exists_isFrobenius_lift_arithFrobAt E ℓ hℓ Q
  haveI := hQtmax
  obtain ⟨A, hA⟩ := NumberField.exists_valuationSubring_eq_localization Qt
  have hℓQ : ((ℓ : ℕ) : 𝓞 E) ∈ Q := by
    have h1 : ((ℓ : ℕ) : ℤ) ∈ FrobeniusDensity.ratPrimeIdeal ℓ := Ideal.mem_span_singleton_self _
    rw [hQover.over, Ideal.under, Ideal.mem_comap, map_natCast] at h1
    exact h1
  have hℓQt : ((ℓ : ℕ) : 𝓞 Kbar) ∈ Qt := by
    rw [hQtQ.over, Ideal.under, Ideal.mem_comap, map_natCast] at hℓQ
    exact hℓQ
  obtain ⟨hAℓ, hAfrob⟩ := ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem Qt ℓ hℓ hℓQt τ hstab hfrob A hA

  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥E) Kbar c
  have hτres' : AlgEquiv.restrictNormalHom E τ = arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q := hτres
  have hrest : AlgEquiv.restrictNormalHom E (g * σ ^ k * g⁻¹) = AlgEquiv.restrictNormalHom E τ := by
    rw [hτres', ← hc, map_mul, map_mul, map_inv, map_pow, hg, hσ']

  have hconjH : g * σ ^ k * g⁻¹ ∈ H := hHn.conj_mem _ (H.pow_mem hσ k) g
  have hτH : τ ∈ H := by
    have h1 : AlgEquiv.restrictNormalHom E ((g * σ ^ k * g⁻¹)⁻¹ * τ) = 1 := by
      rw [map_mul, map_inv, hrest, inv_mul_cancel]
    have h2' := (hfixE _ h1).2
    have : τ = (g * σ ^ k * g⁻¹) * ((g * σ ^ k * g⁻¹)⁻¹ * τ) := by group
    rw [this]
    exact H.mul_mem hconjH h2'

  have hτp : ρ τ ^ p = 1 := hfrobH ℓ hℓ hℓX A hAℓ τ hAfrob hτH
  have hρconj : ρ (g * σ ^ k * g⁻¹) = ρ τ := hagree _ _ hrest
  have hkp : ρ σ ^ (k * p) = 1 := by
    have h1 : ρ (g * σ ^ (k * p) * g⁻¹) = 1 := by
      rw [pow_mul, ← conj_pow, map_pow, hρconj, hτp]
    have h3 : σ ^ (k * p) = g⁻¹ * (g * σ ^ (k * p) * g⁻¹) * g := by group
    rw [← map_pow, h3, map_mul, map_mul, h1, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have hord : ρ σ ^ orderOf σ' = 1 := by
    rw [← map_pow]
    have h1 : AlgEquiv.restrictNormalHom E (σ ^ orderOf σ') = AlgEquiv.restrictNormalHom E (1 : Gal) := by
      rw [map_pow, map_one, ← hσ', pow_orderOf_eq_one]
    rw [hagree _ _ h1, map_one]
  have hgcd : ρ σ ^ Nat.gcd p (orderOf σ') = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hkp, hord⟩
    rwa [Nat.Coprime.gcd_mul_left_cancel p hk] at this
  obtain ⟨d, hd⟩ : Nat.gcd p (orderOf σ') ∣ p := Nat.gcd_dvd_left _ _
  have hsplit : ρ σ ^ p = (ρ σ ^ Nat.gcd p (orderOf σ')) ^ d := by rw [← pow_mul, ← hd]
  rw [hsplit, hgcd, one_pow]

private theorem frobenius_pow_eq_one (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (h2 : Module.finrank (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄Kbar).Point (p : ℤ)) = 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hgood : W.IsGoodPrimeFor ℓ)
    (hap : ((W.apOfModel ℓ : ℤ) : ZMod p) = 2) (hℓ1 : ℓ ≡ 1 [MOD p])
    (A : ValuationSubring Kbar) (hA : A.LiesOverPrime ℓ) (τ : Gal) (hτ : A.IsFrobeniusAt τ ℓ) :
    galoisRepModuleEnd (K := Kbar) ℚ (W.map (Int.castRingHom ℚ)) p τ ^ p = 1 := by
  have hpp : p.Prime := Fact.out
  have htr : LinearMap.trace (ZMod p) _ (galoisRepModuleEnd (K := Kbar) ℚ (W.map (Int.castRingHom ℚ)) p τ) = 2 := by
    rw [← galoisTrace_def, WeierstrassCurve.galoisTrace_frobenius_eq_apOfModel W p ℓ hpp hℓ hℓp hgood A hA τ hτ]
    exact hap
  have hdet : LinearMap.det (galoisRepModuleEnd (K := Kbar) ℚ (W.map (Int.castRingHom ℚ)) p τ) = 1 := by
    rw [WeierstrassCurve.det_galoisRep_frobenius_eq_prime W p ℓ hpp hℓ hℓp hgood A hA τ hτ]
    have := (ZMod.natCast_eq_natCast_iff ℓ 1 p).mpr hℓ1
    simpa using this
  exact pow_eq_one_of_trace_eq_two_of_det_eq_one h2 _ htr hdet

private theorem main
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (S₀ : Set ℕ) (hS₀fin : S₀.Finite) :
    ¬ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ℓ ≡ 1 [MOD p * N'] → W.IsGoodPrimeFor ℓ →
      ((W.apOfModel ℓ : ℤ) : ZMod p) = 2 := by
  intro hall
  classical
  have hpp : p.Prime := Fact.out
  haveI hnormal : Normal ℚ Kbar := inferInstance
  haveI hKalg : Algebra.IsAlgebraic ℚ Kbar := inferInstance

  set ρ := galoisRepModuleEnd (K := Kbar) ℚ (W.map (Int.castRingHom ℚ)) p with hρ
  haveI hell : (W.map (Int.castRingHom ℚ)).IsElliptic := by
    refine ⟨?_⟩
    rw [WeierstrassCurve.map_Δ, eq_intCast]
    exact isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hΔ)
  have h2 : Module.finrank (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄Kbar).Point (p : ℤ)) = 2 :=
    WeierstrassCurve.finrank_torsionBy_of_isAlgClosed (K := Kbar) (W.map (Int.castRingHom ℚ)) (p := p)
      (by exact_mod_cast hpp.ne_zero)
  have hirr' : ∀ N : Submodule (ZMod p)
      (Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄Kbar).Point (p : ℤ)),
      (∀ g : Gal, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤ := by
    obtain ⟨-, hirr2⟩ := hirr
    intro N hN
    exact hirr2 N (fun σ x hx => hN σ x hx)

  have hopen : IsOpen {σ : Gal | ∀ x : Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄Kbar).Point (p : ℤ), σ • x = x} :=
    WeierstrassCurve.isOpen_torsionBy_fixingSubgroup W p hΔ hpp.pos

  have hn0 : p * N' ≠ 0 := mul_ne_zero hpp.ne_zero (NeZero.ne N')
  haveI : NeZero (p * N') := ⟨hn0⟩
  have hn1 : 1 < p * N' := by
    have := hpp.two_le
    have := Nat.pos_of_ne_zero (NeZero.ne N')
    nlinarith
  haveI : Fact (1 < p * N') := ⟨hn1⟩
  obtain ⟨μ, hμ⟩ := exists_isPrimitiveRoot (p * N') hn0
  set χ : Gal →* (ZMod (p * N'))ˣ := IsPrimitiveRoot.autToPow ℚ hμ with hχ
  set H : Subgroup Gal := χ.ker with hH
  haveI hHn : H.Normal := χ.normal_ker
  have hab : ∀ a b : Gal, a * b * a⁻¹ * b⁻¹ ∈ H := by
    intro a b
    rw [hH, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (χ a) (χ b)]
    group
  have hH_fix : ∀ h ∈ H, h μ = μ := by
    intro h hh
    have hspec : μ ^ ((χ h : (ZMod (p * N'))ˣ) : ZMod (p * N')).val = h μ :=
      IsPrimitiveRoot.autToPow_spec ℚ hμ h
    rw [hH, MonoidHom.mem_ker] at hh
    rw [← hspec, hh, Units.val_one, ZMod.val_one, pow_one]
  have hfix_H : ∀ g : Gal, g μ = μ → g ∈ H := by
    intro g hg
    have hspec : μ ^ ((χ g : (ZMod (p * N'))ˣ) : ZMod (p * N')).val = g μ :=
      IsPrimitiveRoot.autToPow_spec ℚ hμ g
    rw [hg] at hspec
    have hval : ((χ g : (ZMod (p * N'))ˣ) : ZMod (p * N')).val = 1 :=
      hμ.pow_inj (ZMod.val_lt _) hn1 (by rw [hspec, pow_one])
    rw [hH, MonoidHom.mem_ker]
    apply Units.ext
    apply ZMod.val_injective
    rw [hval, Units.val_one, ZMod.val_one]

  have hμint : IsIntegral ℚ μ := Algebra.IsIntegral.isIntegral μ
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {μ}) :=
    IntermediateField.adjoin.finiteDimensional hμint
  have hopenμ : IsOpen ((IntermediateField.adjoin ℚ {μ}).fixingSubgroup : Set Gal) :=
    IntermediateField.fixingSubgroup_isOpen _

  obtain ⟨E, hEfin, hEnormal, hEsub⟩ := (krullTopology_mem_nhds_one_iff_of_normal ℚ Kbar _).mp
    ((hopen.inter hopenμ).mem_nhds ⟨fun x => one_smul _ x, Subgroup.one_mem _⟩)
  haveI := hEfin
  haveI := hEnormal
  haveI hEnf : NumberField E := ⟨⟩
  haveI hEn : Normal ℚ E := hEnormal
  haveI hEgal : IsGalois ℚ E := ⟨⟩

  have hfixE : ∀ x : Gal, AlgEquiv.restrictNormalHom E x = 1 → ρ x = 1 ∧ x ∈ H := by
    intro x hx
    have hxE : x ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h1 : (x.restrictNormal E) ⟨y, hy⟩ = ⟨y, hy⟩ := by
        have h := congrArg (fun e : E ≃ₐ[ℚ] E => e ⟨y, hy⟩) hx
        exact h
      have h2 := AlgEquiv.restrictNormal_commutes x E ⟨y, hy⟩
      rw [h1] at h2
      simpa using h2.symm
    obtain ⟨hx1, hx2⟩ := hEsub hxE
    refine ⟨?_, ?_⟩
    · exact LinearMap.ext fun v => hx1 v
    · apply hfix_H
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hx2 μ
        (IntermediateField.mem_adjoin_simple_self ℚ μ)
      exact this
  have hagree : ∀ x y : Gal, AlgEquiv.restrictNormalHom E x = AlgEquiv.restrictNormalHom E y → ρ x = ρ y := by
    intro x y hxy
    have h1 : AlgEquiv.restrictNormalHom E (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2' := (hfixE _ h1).1
    have h3 : y = x * (x⁻¹ * y) := by group
    rw [h3, map_mul, h2', mul_one]

  set X : Finset ℕ := hS₀fin.toFinset ∪ W.Δ.natAbs.primeFactors ∪ (p * N').primeFactors with hX
  have hX_S₀ : ∀ ℓ, ℓ ∉ X → ℓ ∉ S₀ := fun ℓ hℓ hmem =>
    hℓ (by rw [hX]; exact Finset.mem_union_left _ (Finset.mem_union_left _ (hS₀fin.mem_toFinset.mpr hmem)))
  have hX_good : ∀ ℓ, ℓ.Prime → ℓ ∉ X → W.IsGoodPrimeFor ℓ := by
    intro ℓ hℓ hℓX hdvd
    apply hℓX
    rw [hX]
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    exact Nat.mem_primeFactors.mpr ⟨hℓ, Int.natCast_dvd.mp hdvd, Int.natAbs_ne_zero.mpr hΔ⟩
  have hX_ndvd : ∀ ℓ, ℓ.Prime → ℓ ∉ X → ¬ ℓ ∣ p * N' := by
    intro ℓ hℓ hℓX hdvd
    apply hℓX
    rw [hX]
    exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hℓ, hdvd, hn0⟩)
  have hX_ne_p : ∀ ℓ, ℓ.Prime → ℓ ∉ X → ℓ ≠ p := by
    intro ℓ hℓ hℓX hℓp
    exact hX_ndvd ℓ hℓ hℓX (hℓp ▸ dvd_mul_right p N')

  have hfrob_unipotent : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ X → ∀ (A : ValuationSubring Kbar), A.LiesOverPrime ℓ →
      ∀ τ : Gal, A.IsFrobeniusAt τ ℓ → τ ∈ H → ρ τ ^ p = 1 := by
    intro ℓ hℓ hℓX A hA τ hτ hτH
    have hτμ : τ μ = μ ^ ℓ :=
      ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow_of_not_dvd hℓ A hA hτ (hX_ndvd ℓ hℓ hℓX) μ
        hμ.pow_eq_one
    have hℓ1 : ℓ ≡ 1 [MOD p * N'] := by
      have : μ ^ ℓ = μ ^ 1 := by rw [pow_one, ← hτμ, hH_fix τ hτH]
      exact (pow_eq_pow_iff hμ hn0 ℓ 1).mp this
    have hgood := hX_good ℓ hℓ hℓX
    exact frobenius_pow_eq_one p W h2 ℓ hℓ (hX_ne_p ℓ hℓ hℓX) hgood (hall ℓ hℓ (hX_S₀ ℓ hℓX) hℓ1 hgood)
      (Nat.ModEq.of_mul_right N' hℓ1) A hA τ hτ

  have hHunip : ∀ h ∈ H, ρ h ^ p = 1 :=
    pow_eq_one_of_forall_frobenius ρ p E H hHn hfixE hagree X hfrob_unipotent

  have hunit : IsUnit (-1 : ZMod (p * N')) := isUnit_one.neg
  obtain ⟨ℓ₁, ⟨⟨hℓ₁, hℓ₁mod⟩, hℓ₁X⟩⟩ :=
    ((Nat.infinite_setOf_prime_and_eq_mod hunit).diff X.finite_toSet).nonempty
  have hℓ₁X' : ℓ₁ ∉ X := by simpa using hℓ₁X
  obtain ⟨A₁, τ₁, hA₁, hτ₁⟩ := ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨ℓ₁, hℓ₁⟩

  have hτ₁μ : τ₁ μ = μ ^ ℓ₁ :=
    ValuationSubring.IsFrobeniusAt.apply_rootOfUnity_eq_pow_of_not_dvd hℓ₁ A₁ hA₁ hτ₁ (hX_ndvd ℓ₁ hℓ₁ hℓ₁X') μ
      hμ.pow_eq_one
  have hsq : τ₁ ^ 2 ∈ H := by
    apply hfix_H
    have hmod : ℓ₁ * ℓ₁ ≡ 1 [MOD p * N'] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hℓ₁mod, Nat.cast_one]
      ring
    rw [sq, AlgEquiv.mul_apply, hτ₁μ, map_pow, hτ₁μ, ← pow_mul]
    exact ((pow_eq_pow_iff hμ hn0 (ℓ₁ * ℓ₁) 1).mpr hmod).trans (pow_one μ)

  have hdet₁ : LinearMap.det (ρ τ₁) = -1 := by
    rw [hρ, WeierstrassCurve.det_galoisRep_frobenius_eq_prime W p ℓ₁ hpp hℓ₁ (hX_ne_p ℓ₁ hℓ₁ hℓ₁X')
      (hX_good ℓ₁ hℓ₁ hℓ₁X') A₁ hA₁ τ₁ hτ₁]
    have := congrArg (ZMod.castHom (dvd_mul_right p N') (ZMod p)) hℓ₁mod
    simpa using this
  exact core_false ρ h2 hirr' H hab hHunip hp2 τ₁ hsq hdet₁

end Galois

end TraceTwoObstruction

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (N' : ℕ) [NeZero N'] (S₀ : Set ℕ) (hS₀fin : S₀.Finite) :
    ¬ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ℓ ≡ 1 [MOD p * N'] → W.IsGoodPrimeFor ℓ →
      ((W.apOfModel ℓ : ℤ) : ZMod p) = 2 :=
  TraceTwoObstruction.main p hp2 W hΔ hirr N' S₀ hS₀fin

end S_WeierstrassCurve_not_forall_apOfModel_eq_two_of_modRepIsIrreducible
end P2MW
export P2MW.S_WeierstrassCurve_not_forall_apOfModel_eq_two_of_modRepIsIrreducible (solution)
