-- Prove2me | solution 1 for ResidualGaloisRep.nonempty_localFlatClassesAd_linearEquiv_of_dualTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a15505ca-4ac8-5bf6-a87e-823691ab4d9a

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_CartierDual_exists_equiv_algHom_padicAlgCl_monoidHom_units
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

namespace AdDualCore

section Chars
variable {P : Type} [CommMonoid P] {L : Type} [Field L] {p : ℕ} [Fact p.Prime]
  (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ p) (hP : ∀ f : P, f ^ p = 1)

include hζ hP in
lemma apply_mem_zpowers (ψ : P →* Lˣ) (f : P) : ψ f ∈ Subgroup.zpowers ζ := by
  rw [hζ.zpowers_eq, mem_rootsOfUnity, ← map_pow, hP, map_one]

noncomputable def dlogChar (ψ : P →* Lˣ) : Additive P →+ ZMod p :=
  hζ.zmodEquivZPowers.symm.toAddMonoidHom.comp
    (MonoidHom.toAdditive (ψ.codRestrict (Subgroup.zpowers ζ) (apply_mem_zpowers ζ hζ hP ψ)))

noncomputable def expChar (lam : Additive P →+ ZMod p) : P →* Lˣ :=
  (Subgroup.zpowers ζ).subtype.comp
    (MonoidHom.toAdditive.symm (hζ.zmodEquivZPowers.toAddMonoidHom.comp lam))

lemma zmodEquivZPowers_dlogChar (ψ : P →* Lˣ) (x : Additive P) :
    hζ.zmodEquivZPowers (dlogChar ζ hζ hP ψ x) =
      Additive.ofMul ⟨ψ x.toMul, apply_mem_zpowers ζ hζ hP ψ x.toMul⟩ := by
  simp [dlogChar]

lemma expChar_apply (lam : Additive P →+ ZMod p) (f : P) :
    (expChar ζ hζ lam f : Lˣ) = ((hζ.zmodEquivZPowers (lam (Additive.ofMul f))).toMul : Subgroup.zpowers ζ) := by
  simp [expChar]

lemma dlogChar_expChar (lam : Additive P →+ ZMod p) :
    dlogChar ζ hζ hP (expChar ζ hζ lam) = lam := by
  refine AddMonoidHom.ext fun x => ?_
  apply hζ.zmodEquivZPowers.injective
  rw [zmodEquivZPowers_dlogChar]
  apply Additive.toMul.injective
  ext
  simp only [toMul_ofMul]
  exact congrArg Units.val (expChar_apply ζ hζ lam x.toMul)

lemma expChar_dlogChar (ψ : P →* Lˣ) : expChar ζ hζ (dlogChar ζ hζ hP ψ) = ψ := by
  ext f
  rw [expChar_apply, zmodEquivZPowers_dlogChar]
  rfl

noncomputable def charEquiv : (P →* Lˣ) ≃ (Additive P →+ ZMod p) where
  toFun := dlogChar ζ hζ hP
  invFun := expChar ζ hζ
  left_inv := expChar_dlogChar ζ hζ hP
  right_inv := dlogChar_expChar ζ hζ hP

lemma coe_pow_val_dlogChar (ψ : P →* Lˣ) (f : P) :
    (ζ : L) ^ (dlogChar ζ hζ hP ψ (Additive.ofMul f)).val = ((ψ f : Lˣ) : L) := by
  have h := zmodEquivZPowers_dlogChar ζ hζ hP ψ (Additive.ofMul f)
  rw [← ZMod.natCast_zmod_val (dlogChar ζ hζ hP ψ (Additive.ofMul f)),
    IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat] at h
  have h' := congrArg (fun x => (((Additive.toMul x : Subgroup.zpowers ζ) : Lˣ) : L)) h
  simpa using h'

lemma dlogChar_mul (ψ₁ ψ₂ : P →* Lˣ) :
    dlogChar ζ hζ hP (ψ₁ * ψ₂) = dlogChar ζ hζ hP ψ₁ + dlogChar ζ hζ hP ψ₂ := by
  refine AddMonoidHom.ext fun x => ?_
  apply hζ.zmodEquivZPowers.injective
  rw [AddMonoidHom.add_apply, map_add, zmodEquivZPowers_dlogChar, zmodEquivZPowers_dlogChar,
    zmodEquivZPowers_dlogChar]
  rfl

lemma dlogChar_eq_mul_of_apply_eq {K : Type} [Field K] [Algebra K L] (σ : L ≃ₐ[K] L) (a : ℕ)
    (hσ : σ (ζ : L) = (ζ : L) ^ a) (ψ ψ' : P →* Lˣ) (f f' : P)
    (h : ((ψ' f' : Lˣ) : L) = σ ((ψ f : Lˣ) : L)) :
    dlogChar ζ hζ hP ψ' (Additive.ofMul f') = (a : ZMod p) * dlogChar ζ hζ hP ψ (Additive.ofMul f) := by
  set n := dlogChar ζ hζ hP ψ (Additive.ofMul f) with hn
  set n' := dlogChar ζ hζ hP ψ' (Additive.ofMul f') with hn'
  have e1 : ((ψ f : Lˣ) : L) = (ζ : L) ^ n.val := (coe_pow_val_dlogChar ζ hζ hP ψ f).symm
  have e2 : ((ψ' f' : Lˣ) : L) = (ζ : L) ^ n'.val := (coe_pow_val_dlogChar ζ hζ hP ψ' f').symm
  have hζ' : IsPrimitiveRoot (ζ : L) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have key' : (ζ : L) ^ n'.val = (ζ : L) ^ (a * n.val) := by
    rw [← e2, h, e1, map_pow, hσ, ← pow_mul]
  have key : ζ ^ n'.val = ζ ^ (a * n.val) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, key']
  rw [pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at key
  rw [← ZMod.natCast_zmod_val n', ← ZMod.natCast_zmod_val n, ← Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr key

end Chars
end AdDualCore

namespace AdDualCore
section Trace
set_option linter.unusedSectionVars false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
  (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M]

noncomputable def trPush : Module.Dual k M →+ (M →+ ZMod p) :=
  letI := ZMod.algebra k p
  { toFun := fun f => (Algebra.trace (ZMod p) k).toAddMonoidHom.comp f.toAddMonoidHom
    map_zero' := by ext; simp
    map_add' := by intro f g; ext; simp }

lemma trPush_apply (f : Module.Dual k M) (m : M) :
    letI := ZMod.algebra k p
    trPush p k M f m = Algebra.trace (ZMod p) k (f m) := rfl

lemma trPush_injective : Function.Injective (trPush p k M) := by
  letI := ZMod.algebra k p
  haveI : FiniteDimensional (ZMod p) k := inferInstance
  haveI : Algebra.IsSeparable (ZMod p) k := inferInstance
  intro f g hfg
  rw [← sub_eq_zero]
  ext m
  have hnd := traceForm_nondegenerate (ZMod p) k
  rw [LinearMap.zero_apply]
  refine hnd.1 _ fun a => ?_
  rw [Algebra.traceForm_apply]
  have := congrArg (fun φ : M →+ ZMod p => φ (a • m)) hfg
  simp only [trPush_apply, map_smul, smul_eq_mul] at this
  rw [LinearMap.sub_apply, sub_mul, map_sub, sub_eq_zero, mul_comm]
  simpa [mul_comm] using this

lemma trPush_surjective : Function.Surjective (trPush p k M) := by
  letI := ZMod.algebra k p
  haveI : FiniteDimensional (ZMod p) k := inferInstance
  haveI : Algebra.IsSeparable (ZMod p) k := inferInstance
  intro lam
  set b := Module.finBasis k M
  have hnd := traceForm_nondegenerate (ZMod p) k

  let φ : Fin (Module.finrank k M) → Module.Dual (ZMod p) k :=
    fun i => AddMonoidHom.toZModLinearMap p (lam.comp ((LinearMap.lsmul k M).flip (b i)).toAddMonoidHom)
  let c : Fin (Module.finrank k M) → k := fun i => ((Algebra.traceForm (ZMod p) k).toDual hnd).symm (φ i)
  have hc : ∀ i (a : k), Algebra.trace (ZMod p) k (a * c i) = lam (a • b i) := by
    intro i a
    have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) (f := φ i) a

    rw [Algebra.traceForm_apply] at this
    rw [mul_comm]
    simp [φ] at this
    exact this
  refine ⟨b.constr k c, ?_⟩
  ext m
  rw [trPush_apply]
  conv_lhs => rw [← b.sum_repr m]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [show lam m = lam (∑ i, b.repr m i • b i) by rw [b.sum_repr]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b.constr_basis]
  exact hc i _

noncomputable def trEquiv : Module.Dual k M ≃ (M →+ ZMod p) :=
  Equiv.ofBijective (trPush p k M) ⟨trPush_injective p k M, trPush_surjective p k M⟩

lemma trEquiv_apply (f : Module.Dual k M) : trEquiv p k M f = trPush p k M f := rfl

lemma trPush_comp (f : Module.Dual k M) (A : M →ₗ[k] M) :
    trPush p k M (f ∘ₗ A) = (trPush p k M f).comp A.toAddMonoidHom := rfl

lemma trPush_castHom_smul (x : ZMod p) (f : Module.Dual k M) :
    trPush p k M ((ZMod.castHom (dvd_refl p) k x) • f) = x • trPush p k M f := by
  letI := ZMod.algebra k p
  ext m
  simp only [trPush_apply, LinearMap.smul_apply, AddMonoidHom.smul_apply]
  have : (ZMod.castHom (dvd_refl p) k x) • f m = x • f m := by
    rw [Algebra.smul_def]; rfl
  rw [this, map_smul, smul_eq_mul]

end Trace
end AdDualCore

namespace AdDualCore
section Transpose
variable {k : Type} [Field k] {ρ₁ ρ₂ : ResidualGaloisRep k} (θ : ρ₂.V ≃ₗ[k] Module.Dual k ρ₁.V)

noncomputable def Tθ : Module.End k ρ₁.V →ₗ[k] Module.End k ρ₂.V where
  toFun φ := -(θ.symm.toLinearMap ∘ₗ φ.dualMap ∘ₗ θ.toLinearMap)
  map_add' φ ψ := by
    ext w
    simp only [LinearMap.dualMap_apply', LinearMap.comp_add, map_add, neg_add, LinearMap.neg_apply,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.add_apply]
  map_smul' a φ := by
    ext w
    simp only [LinearMap.dualMap_apply', LinearMap.comp_smul, map_smul, RingHom.id_apply,
      LinearMap.neg_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.smul_apply, smul_neg]

@[scoped simp] lemma Tθ_apply (φ : Module.End k ρ₁.V) (w : ρ₂.V) :
    Tθ θ φ w = -θ.symm ((θ w) ∘ₗ φ) := rfl

end Transpose

section Model
variable {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
  (ρ₁ ρ₂ : ResidualGaloisRep k) (θ : ρ₂.V ≃ₗ[k] Module.Dual k ρ₁.V)

def precompEquiv {P M : Type} [CommMonoid P] [AddCommGroup M] (e : P ≃ M)
    (he : ∀ f g, e (f * g) = e f + e g) : (Additive P →+ ZMod p) ≃ (M →+ ZMod p) where
  toFun lam :=
    { toFun := fun x => lam (Additive.ofMul (e.symm x))
      map_zero' := by
        have h1 : e 1 = 0 := by
          have := he 1 1; rw [one_mul] at this
          exact left_eq_add.mp this
        rw [← h1, Equiv.symm_apply_apply]; exact lam.map_zero
      map_add' := fun x y => by
        obtain ⟨f, rfl⟩ := e.surjective x; obtain ⟨g, rfl⟩ := e.surjective y
        rw [← he, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
          ofMul_mul, map_add] }
  invFun mu :=
    { toFun := fun x => mu (e x.toMul)
      map_zero' := by
        have h1 : e 1 = 0 := by
          have := he 1 1; rw [one_mul] at this
          exact left_eq_add.mp this
        show mu (e 1) = 0; rw [h1, map_zero]
      map_add' := fun x y => by show mu (e (x.toMul * y.toMul)) = _; rw [he, map_add] }
  left_inv lam := by ext x; simp
  right_inv mu := by ext x; simp

end Model
end AdDualCore
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore"

namespace AdDualCore
section Core
variable {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]

def ofAut (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : primeLocalGaloisGroup (pPrime p) := τ

noncomputable def twist {H : Type} [CommRing H] [HopfAlgebra ℤ_[p] H]
    (σ : primeLocalGaloisGroup (pPrime p)) (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) :
    WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) :=
  WithConv.toConv (((ResidualGaloisRep.localAut p σ).toAlgHom.restrictScalars ℤ_[p]).comp f.ofConv)

lemma trEquiv_symm_add (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M]
    (x y : M →+ ZMod p) :
    (trEquiv p k M).symm (x + y) = (trEquiv p k M).symm x + (trEquiv p k M).symm y := by
  apply (trEquiv p k M).injective
  rw [Equiv.apply_symm_apply, trEquiv_apply, map_add, ← trEquiv_apply, ← trEquiv_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem isLocallyFlatCocycleAd_of_dual (ρ₁ ρ₂ : ResidualGaloisRep k)
    (θ : ρ₂.V ≃ₗ[k] Module.Dual k ρ₁.V)
    (hθ : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρ₂.V),
      θ (ρ₂.ρ g w) =
        (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((θ w) ∘ₗ (ρ₁.ρ g⁻¹)))
    (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρ₁.adRep)))
    (c' : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρ₂.adRep)))
    (hc' : ∀ σ, c'.val σ = Tθ θ (c.val σ))
    (hc : ρ₁.IsLocallyFlatCocycleAd p c) : ρ₂.IsLocallyFlatCocycleAd p c' := by
  obtain ⟨H, iCR, iHA, hfin, hfl, hco, e, hadd, hgal⟩ := hc
  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing

  have hact : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (x : ρ₁.V × ρ₁.V),
      ρ₁.dualLiftModuleActAd p c σ x =
        (ρ₁.ρ (primeLocalToGlobal (pPrime p) σ) x.1,
          (c.val σ) (ρ₁.ρ (primeLocalToGlobal (pPrime p) σ) x.1) +
            ρ₁.ρ (primeLocalToGlobal (pPrime p) σ) x.2) := fun σ x => rfl
  have hact' : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (x : ρ₂.V × ρ₂.V),
      ρ₂.dualLiftModuleActAd p c' σ x =
        (ρ₂.ρ (primeLocalToGlobal (pPrime p) σ) x.1,
          (c'.val σ) (ρ₂.ρ (primeLocalToGlobal (pPrime p) σ) x.1) +
            ρ₂.ρ (primeLocalToGlobal (pPrime p) σ) x.2) := fun σ x => rfl

  have he1 : e 1 = 0 := by
    have h := hadd 1 1
    rw [one_mul] at h
    have h' : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hpow : ∀ (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) (n : ℕ), e (f ^ n) = n • e f := by
    intro f n
    induction n with
    | zero => simp [he1]
    | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]
  have hkill : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), f ^ p = 1 := by
    intro f
    apply e.injective
    rw [hpow, he1, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]

  obtain ⟨d, hdmul, hdgal⟩ := CartierDual.exists_equiv_algHom_padicAlgCl_monoidHom_units p H
  obtain ⟨ζ, hζ, hζgal⟩ :=
    ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal p p

  let E1 := charEquiv ζ hζ hkill
  let E2 := precompEquiv p e hadd
  let E3 := (trEquiv p k (ρ₁.V × ρ₁.V)).symm
  let E4 := (Module.dualProdDualEquivDual k ρ₁.V ρ₁.V).symm.toEquiv
  let E5 : Module.Dual k ρ₁.V × Module.Dual k ρ₁.V ≃ ρ₂.V × ρ₂.V :=
    (Equiv.prodComm _ _).trans (Equiv.prodCongr θ.symm.toEquiv θ.symm.toEquiv)
  let Fof : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p) → Module.Dual k (ρ₁.V × ρ₁.V) :=
    fun φ => E3 (E2 (E1 (d φ)))
  let e' : WithConv (CartierDual ℤ_[p] H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρ₂.V × ρ₂.V :=
    d.trans (E1.trans (E2.trans (E3.trans (E4.trans E5))))
  have he'_apply : ∀ φ, e' φ = (θ.symm ((Fof φ) ∘ₗ LinearMap.inr k ρ₁.V ρ₁.V),
      θ.symm ((Fof φ) ∘ₗ LinearMap.inl k ρ₁.V ρ₁.V)) := fun φ => rfl

  have hstar : ∀ φ (x : ρ₁.V × ρ₁.V),
      trPush p k (ρ₁.V × ρ₁.V) (Fof φ) x = dlogChar ζ hζ hkill (d φ) (Additive.ofMul (e.symm x)) := by
    intro φ x
    have : trPush p k (ρ₁.V × ρ₁.V) (Fof φ) = E2 (E1 (d φ)) := by
      show trEquiv p k (ρ₁.V × ρ₁.V) ((trEquiv p k (ρ₁.V × ρ₁.V)).symm (E2 (E1 (d φ)))) = _
      exact Equiv.apply_symm_apply _ _
    rw [this]
    rfl

  have hE2add : ∀ x y, E2 (x + y) = E2 x + E2 y := fun x y => by ext; rfl
  have hFof_mul : ∀ φ ψ, Fof (φ * ψ) = Fof φ + Fof ψ := by
    intro φ ψ
    show E3 (E2 (E1 (d (φ * ψ)))) = E3 (E2 (E1 (d φ))) + E3 (E2 (E1 (d ψ)))
    rw [hdmul, show E1 (d φ * d ψ) = E1 (d φ) + E1 (d ψ) from dlogChar_mul ζ hζ hkill _ _, hE2add]
    exact trEquiv_symm_add p (ρ₁.V × ρ₁.V) _ _
  have he'add : ∀ φ ψ, e' (φ * ψ) = e' φ + e' ψ := by
    intro φ ψ
    rw [he'_apply, he'_apply, he'_apply, hFof_mul, LinearMap.add_comp, LinearMap.add_comp, map_add,
      map_add, Prod.mk_add_mk]

  have hsplit : ∀ (G : Module.Dual k (ρ₁.V × ρ₁.V)) (x₁ x₂ : ρ₁.V),
      G (x₁, x₂) = (G ∘ₗ LinearMap.inl k ρ₁.V ρ₁.V) x₁ + (G ∘ₗ LinearMap.inr k ρ₁.V ρ₁.V) x₂ := by
    intro G x₁ x₂
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, ← map_add,
      Prod.mk_add_mk, add_zero, zero_add]
  refine ⟨CartierDual ℤ_[p] H, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    e', he'add, ?_⟩

  intro σ φ φ' hφ'
  set g := primeLocalToGlobal (pPrime p) σ with hg
  set ρσ : Module.End k ρ₁.V := ρ₁.ρ g with hρσ
  set s : k := ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p) with hs
  have hinv : ∀ v, ρσ (ρ₁.ρ g⁻¹ v) = v := by
    intro v
    rw [hρσ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

  let A : ρ₁.V × ρ₁.V →ₗ[k] ρ₁.V × ρ₁.V :=
    (ρσ ∘ₗ LinearMap.fst k ρ₁.V ρ₁.V).prod
      ((c.val σ ∘ₗ ρσ) ∘ₗ LinearMap.fst k ρ₁.V ρ₁.V + ρσ ∘ₗ LinearMap.snd k ρ₁.V ρ₁.V)
  have hA : ∀ x, A x = ρ₁.dualLiftModuleActAd p c σ x := fun x => rfl

  have hσζ : (ResidualGaloisRep.localAut p σ) ((ζ : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((ζ : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ ((cycloChar p g : (ZMod p)ˣ) : ZMod p).val := by
    have h0 := congrArg Units.val (hζgal (ResidualGaloisRep.localAut p σ))
    rw [Units.val_pow_eq_pow_val] at h0
    exact h0

  have hF' : Fof φ' ∘ₗ A = s • Fof φ := by
    apply trPush_injective p k
    ext x
    rw [trPush_comp, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, hstar, hs,
      trPush_castHom_smul, AddMonoidHom.smul_apply, hstar, smul_eq_mul]
    set f := e.symm x with hf
    have hx : e.symm (A x) = twist p σ f := by
      rw [Equiv.symm_apply_eq, hA, hgal σ f (twist p σ f) (fun h => rfl), hf, Equiv.apply_symm_apply]
    rw [hx, ← ZMod.natCast_zmod_val ((cycloChar p g : (ZMod p)ˣ) : ZMod p)]
    exact dlogChar_eq_mul_of_apply_eq ζ hζ hkill (ResidualGaloisRep.localAut p σ) _ hσζ (d φ) (d φ') f
      (twist p σ f) (hdgal (ResidualGaloisRep.localAut p σ) φ φ' hφ' f (twist p σ f) (fun x => rfl))

  have hβ : ∀ w, (Fof φ' ∘ₗ LinearMap.inr k ρ₁.V ρ₁.V) (ρσ w) =
      s • (Fof φ ∘ₗ LinearMap.inr k ρ₁.V ρ₁.V) w := by
    intro w
    have h1 := LinearMap.congr_fun hF' (0, w)
    rw [LinearMap.comp_apply, LinearMap.smul_apply, hA, hact] at h1
    simp only [map_zero, zero_add] at h1
    simpa [LinearMap.comp_apply] using h1
  have hα : ∀ v, (Fof φ' ∘ₗ LinearMap.inl k ρ₁.V ρ₁.V) (ρσ v) +
      (Fof φ' ∘ₗ LinearMap.inr k ρ₁.V ρ₁.V) ((c.val σ) (ρσ v)) =
      s • (Fof φ ∘ₗ LinearMap.inl k ρ₁.V ρ₁.V) v := by
    intro v
    have h1 := LinearMap.congr_fun hF' (v, 0)
    rw [LinearMap.comp_apply, LinearMap.smul_apply, hA, hact] at h1
    simp only [map_zero, add_zero] at h1
    rw [hsplit] at h1
    simpa [LinearMap.comp_apply] using h1

  rw [he'_apply, he'_apply, hact']
  have coord1 : θ.symm (Fof φ' ∘ₗ LinearMap.inr k ρ₁.V ρ₁.V) =
      ρ₂.ρ g (θ.symm (Fof φ ∘ₗ LinearMap.inr k ρ₁.V ρ₁.V)) := by
    apply θ.injective
    rw [LinearEquiv.apply_symm_apply, hθ, LinearEquiv.apply_symm_apply]
    ext v
    have h := hβ (ρ₁.ρ g⁻¹ v)
    rw [hinv] at h
    simp only [LinearMap.smul_apply, LinearMap.comp_apply] at h ⊢
    exact h
  refine Prod.ext coord1 ?_
  show θ.symm (Fof φ' ∘ₗ LinearMap.inl k ρ₁.V ρ₁.V) =
    (c'.val σ) (ρ₂.ρ g (θ.symm (Fof φ ∘ₗ LinearMap.inr k ρ₁.V ρ₁.V))) +
      ρ₂.ρ g (θ.symm (Fof φ ∘ₗ LinearMap.inl k ρ₁.V ρ₁.V))
  rw [← coord1, hc', Tθ_apply, LinearEquiv.apply_symm_apply]
  apply θ.injective
  rw [LinearEquiv.apply_symm_apply, map_add, map_neg, LinearEquiv.apply_symm_apply, hθ,
    LinearEquiv.apply_symm_apply]
  ext v
  have h2 := hα (ρ₁.ρ g⁻¹ v)
  rw [hinv] at h2
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.smul_apply] at h2 ⊢
  linear_combination h2

end Core
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore"
end AdDualCore
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore"

namespace AdDualH1f

noncomputable section

section Chi

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

def χk (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : k :=
  ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)

theorem χk_def (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    χk (k := k) p g = ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p) := rfl

theorem χk_mul (g h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    χk (k := k) p (g * h) = χk p g * χk p h := by
  rw [χk_def, χk_def, χk_def, map_mul, Units.val_mul, map_mul]

theorem χk_one : χk (k := k) p 1 = 1 := by
  rw [χk_def, map_one, Units.val_one, map_one]

theorem χk_mul_inv (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    χk (k := k) p g * χk p g⁻¹ = 1 := by
  rw [← χk_mul, mul_inv_cancel, χk_one]

theorem χk_inv_mul (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    χk (k := k) p g⁻¹ * χk p g = 1 := by
  rw [← χk_mul, inv_mul_cancel, χk_one]

end Chi
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore"

section Transpose

variable {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

def Tlin (η : W ≃ₗ[K] Module.Dual K V) : Module.End K V →ₗ[K] Module.End K W :=
  -((η.symm.conj : Module.End K (Module.Dual K V) ≃ₗ[K] Module.End K W).toLinearMap ∘ₗ
      Module.Dual.transpose (R := K))

@[scoped simp] theorem Tlin_apply (η : W ≃ₗ[K] Module.Dual K V) (φ : Module.End K V) (w : W) :
    Tlin η φ w = -η.symm ((η w) ∘ₗ φ) := by
  simp [Tlin, LinearEquiv.conj_apply, Module.Dual.transpose_apply]

theorem apply_Tlin (η : W ≃ₗ[K] Module.Dual K V) (φ : Module.End K V) (w : W) :
    η (Tlin η φ w) = -((η w) ∘ₗ φ) := by
  rw [Tlin_apply, map_neg, LinearEquiv.apply_symm_apply]

theorem apply_Tlin_apply (η : W ≃ₗ[K] Module.Dual K V) (φ : Module.End K V) (w : W) (v : V) :
    η (Tlin η φ w) v = -(η w (φ v)) := by
  rw [apply_Tlin]
  rfl

variable [FiniteDimensional K V]

def η₂ (η : W ≃ₗ[K] Module.Dual K V) : V ≃ₗ[K] Module.Dual K W :=
  (Module.evalEquiv K V).trans η.dualMap

@[scoped simp] theorem η₂_apply (η : W ≃ₗ[K] Module.Dual K V) (v : V) (w : W) : η₂ η v w = η w v := rfl

theorem Tlin_η₂_Tlin (η : W ≃ₗ[K] Module.Dual K V) (φ : Module.End K V) :
    Tlin (η₂ η) (Tlin η φ) = φ := by
  apply LinearMap.ext
  intro v
  apply (η₂ η).injective
  apply LinearMap.ext
  intro w
  rw [apply_Tlin_apply, η₂_apply, apply_Tlin_apply, neg_neg, η₂_apply]

theorem Tlin_Tlin_η₂ (η : W ≃ₗ[K] Module.Dual K V) (ψ : Module.End K W) :
    Tlin η (Tlin (η₂ η) ψ) = ψ := by
  apply LinearMap.ext
  intro w
  apply η.injective
  apply LinearMap.ext
  intro v
  rw [apply_Tlin_apply, ← η₂_apply η (Tlin (η₂ η) ψ v) w, apply_Tlin_apply, neg_neg, η₂_apply]

def T (η : W ≃ₗ[K] Module.Dual K V) : Module.End K V ≃ₗ[K] Module.End K W :=
  { Tlin η with
    invFun := Tlin (η₂ η)
    left_inv := Tlin_η₂_Tlin η
    right_inv := Tlin_Tlin_η₂ η }

@[scoped simp] theorem T_apply (η : W ≃ₗ[K] Module.Dual K V) (φ : Module.End K V) :
    T η φ = Tlin η φ := rfl

@[scoped simp] theorem T_symm_apply (η : W ≃ₗ[K] Module.Dual K V) (ψ : Module.End K W) :
    (T η).symm ψ = Tlin (η₂ η) ψ := rfl

omit [FiniteDimensional K V] in

theorem Tlin_conj {G : Type*} [Group G] (ρ : G →* Module.End K V) (ρ' : G →* Module.End K W)
    (η : W ≃ₗ[K] Module.Dual K V) (χ : G → K)
    (hη : ∀ (g : G) (w : W), η (ρ' g w) = χ g • ((η w) ∘ₗ (ρ g⁻¹)))
    (hχ : ∀ g : G, χ g * χ g⁻¹ = 1) (g : G) (φ : Module.End K V) :
    Tlin η (ρ g * φ * ρ g⁻¹) = ρ' g * Tlin η φ * ρ' g⁻¹ := by
  apply LinearMap.ext
  intro w
  apply η.injective
  apply LinearMap.ext
  intro v
  rw [apply_Tlin_apply]
  simp only [Module.End.mul_apply, hη, LinearMap.smul_apply, LinearMap.comp_apply,
    apply_Tlin_apply, inv_inv, smul_eq_mul, mul_neg, ← mul_assoc, hχ, one_mul]

end Transpose
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore"

section Galois

open CategoryTheory groupCohomology

variable {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

abbrev Gp : Type := primeLocalGaloisGroup (pPrime p)

abbrev AdL (ρbar : ResidualGaloisRep k) : Rep k (Gp p) :=
  Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep)

variable (ρ₁ ρ₂ : ResidualGaloisRep k) (θ : ρ₂.V ≃ₗ[k] Module.Dual k ρ₁.V)

def IsDualTwist : Prop :=
  ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρ₂.V),
    θ (ρ₂.ρ g w) = (χk p g : k) • ((θ w) ∘ₗ (ρ₁.ρ g⁻¹))

variable {p ρ₁ ρ₂ θ}

omit [CharP k p] in
theorem AdL_ρ_apply (ρbar : ResidualGaloisRep k) (g : Gp p) (φ : Module.End k ρbar.V) :
    (AdL p ρbar).ρ g φ = ρbar.ρ (primeLocalToGlobal (pPrime p) g) * φ *
      ρbar.ρ (primeLocalToGlobal (pPrime p) g)⁻¹ := rfl

theorem Tlin_AdL (hθ : IsDualTwist p ρ₁ ρ₂ θ) (g : Gp p) (φ : Module.End k ρ₁.V) :
    Tlin θ ((AdL p ρ₁).ρ g φ) = (AdL p ρ₂).ρ g (Tlin θ φ) := by
  rw [AdL_ρ_apply, AdL_ρ_apply]
  exact Tlin_conj ρ₁.ρ ρ₂.ρ θ (χk p) hθ (χk_mul_inv p) _ φ

def TEquiv (hθ : IsDualTwist p ρ₁ ρ₂ θ) : ((AdL p ρ₁).ρ).Equiv ((AdL p ρ₂).ρ) :=
  Representation.Equiv.mk (T θ) (fun g => LinearMap.ext fun φ => Tlin_AdL hθ g φ)

@[scoped simp] theorem TEquiv_apply (hθ : IsDualTwist p ρ₁ ρ₂ θ) (φ : Module.End k ρ₁.V) :
    TEquiv hθ φ = Tlin θ φ := rfl

def adIso (hθ : IsDualTwist p ρ₁ ρ₂ θ) : AdL p ρ₁ ≅ AdL p ρ₂ := Rep.mkIso (TEquiv hθ)

def Tcoc (hθ : IsDualTwist p ρ₁ ρ₂ θ) : cocycles₁ (AdL p ρ₁) →ₗ[k] cocycles₁ (AdL p ρ₂) where
  toFun c := ⟨fun g => Tlin θ (c.val g), by
    rw [mem_cocycles₁_iff]
    intro g h
    rw [(mem_cocycles₁_iff (A := AdL p ρ₁) c.val).mp c.2 g h, map_add, Tlin_AdL hθ]⟩
  map_add' a b := by
    apply cocycles₁_ext
    intro g
    change Tlin θ (a.val g + b.val g) = Tlin θ (a.val g) + Tlin θ (b.val g)
    rw [map_add]
  map_smul' r a := by
    apply cocycles₁_ext
    intro g
    change Tlin θ (r • a.val g) = r • Tlin θ (a.val g)
    rw [map_smul]

@[scoped simp] theorem Tcoc_val (hθ : IsDualTwist p ρ₁ ρ₂ θ) (c : cocycles₁ (AdL p ρ₁)) (g : Gp p) :
    (Tcoc hθ c).val g = Tlin θ (c.val g) := rfl

theorem mapCocycles₁_adIso_hom (hθ : IsDualTwist p ρ₁ ρ₂ θ) (c : cocycles₁ (AdL p ρ₁)) :
    (mapCocycles₁ (MonoidHom.id (Gp p)) (adIso hθ).hom).hom c = Tcoc hθ c := by
  apply cocycles₁_ext
  intro g
  rfl

def ΦL (hθ : IsDualTwist p ρ₁ ρ₂ θ) : H1 (AdL p ρ₁) ≃ₗ[k] H1 (AdL p ρ₂) :=
  ((groupCohomology.functor k (Gp p) 1).mapIso (adIso hθ)).toLinearEquiv

theorem ΦL_H1π (hθ : IsDualTwist p ρ₁ ρ₂ θ) (c : cocycles₁ (AdL p ρ₁)) :
    ΦL hθ ((H1π (AdL p ρ₁)).hom c) = (H1π (AdL p ρ₂)).hom (Tcoc hθ c) := by
  change ((groupCohomology.functor k (Gp p) 1).mapIso (adIso hθ)).hom.hom
    ((H1π (AdL p ρ₁)).hom c) = _
  rw [Functor.mapIso_hom, groupCohomology.functor_map, ← mapCocycles₁_adIso_hom hθ c]
  exact H1π_comp_map_apply (A := AdL p ρ₁) (B := AdL p ρ₂) (MonoidHom.id (Gp p)) (adIso hθ).hom c

theorem Tθ_eq_Tlin (θ' : ρ₂.V ≃ₗ[k] Module.Dual k ρ₁.V) : AdDualCore.Tθ θ' = Tlin θ' :=
  LinearMap.ext fun φ => LinearMap.ext fun w => by rw [AdDualCore.Tθ_apply, Tlin_apply]

theorem Tcoc_val_eq_Tθ (hθ : IsDualTwist p ρ₁ ρ₂ θ) (c : cocycles₁ (AdL p ρ₁)) (g : Gp p) :
    (Tcoc hθ c).val g = AdDualCore.Tθ θ (c.val g) := by
  rw [Tcoc_val, Tθ_eq_Tlin]

theorem isDualTwist_η₂ (hθ : IsDualTwist p ρ₁ ρ₂ θ) : IsDualTwist p ρ₂ ρ₁ (η₂ θ) := by
  intro g v
  apply LinearMap.ext
  intro w
  rw [η₂_apply, LinearMap.smul_apply, LinearMap.comp_apply, η₂_apply, hθ g⁻¹ w, inv_inv,
    LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    χk_mul_inv, one_mul]

theorem Tcoc_η₂_Tcoc (hθ : IsDualTwist p ρ₁ ρ₂ θ) (c : cocycles₁ (AdL p ρ₁)) :
    Tcoc (isDualTwist_η₂ hθ) (Tcoc hθ c) = c := by
  apply cocycles₁_ext
  intro g
  exact Tlin_η₂_Tlin θ (c.val g)

theorem Tcoc_Tcoc_η₂ (hθ : IsDualTwist p ρ₁ ρ₂ θ) (c' : cocycles₁ (AdL p ρ₂)) :
    Tcoc hθ (Tcoc (isDualTwist_η₂ hθ) c') = c' := by
  apply cocycles₁_ext
  intro g
  exact Tlin_Tlin_η₂ θ (c'.val g)

end Galois
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore"

section Main

open CategoryTheory groupCohomology

theorem main_of_core {k : Type} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (core : ∀ (ρ₁ ρ₂ : ResidualGaloisRep k) (θ : ρ₂.V ≃ₗ[k] Module.Dual k ρ₁.V),
      (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρ₂.V),
        θ (ρ₂.ρ g w) =
          (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((θ w) ∘ₗ (ρ₁.ρ g⁻¹))) →
      ∀ (c : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρ₁.adRep)))
        (c' : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρ₂.adRep))),
        (∀ σ : primeLocalGaloisGroup (pPrime p), c'.val σ = AdDualCore.Tθ θ (c.val σ)) →
        ρ₁.IsLocallyFlatCocycleAd p c → ρ₂.IsLocallyFlatCocycleAd p c')
    (ρbar ρbar' : ResidualGaloisRep k) (η : ρbar'.V ≃ₗ[k] Module.Dual k ρbar.V)
    (hη : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρbar'.V),
      η (ρbar'.ρ g w) =
        (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((η w) ∘ₗ (ρbar.ρ g⁻¹))) :
    Nonempty ((ρbar.localFlatClassesAd p) ≃ₗ[k] (ρbar'.localFlatClassesAd p)) := by
  have hθ : IsDualTwist p ρbar ρbar' η := hη
  refine ⟨LinearEquiv.ofSubmodules (ΦL hθ) _ _ ?_⟩
  rw [ResidualGaloisRep.localFlatClassesAd, ResidualGaloisRep.localFlatClassesAd, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨Tcoc hθ c, core _ _ η hη c _ (Tcoc_val_eq_Tθ hθ c) hc, ΦL_H1π hθ c⟩
  · rintro ⟨c', hc', rfl⟩
    refine ⟨(H1π _).hom (Tcoc (isDualTwist_η₂ hθ) c'),
      ⟨_, core _ _ (η₂ η) (isDualTwist_η₂ hθ) c' _ (Tcoc_val_eq_Tθ (isDualTwist_η₂ hθ) c') hc',
        rfl⟩, ?_⟩
    change ΦL hθ ((H1π _).hom (Tcoc (isDualTwist_η₂ hθ) c')) = _
    rw [ΦL_H1π, Tcoc_Tcoc_η₂]

end Main
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore"

end
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore"

end AdDualH1f
p2m_reactivate "P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualCore P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist.AdDualH1f"

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (ρbar' : ResidualGaloisRep k) (η : ρbar'.V ≃ₗ[k] Module.Dual k ρbar.V)
    (hη : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρbar'.V),
      η (ρbar'.ρ g w) =
        (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((η w) ∘ₗ (ρbar.ρ g⁻¹))) :
    Nonempty ((ρbar.localFlatClassesAd p) ≃ₗ[k] (ρbar'.localFlatClassesAd p)) := by
  have _ := hp2
  have _ := hker
  exact AdDualH1f.main_of_core p (AdDualCore.isLocallyFlatCocycleAd_of_dual p) ρbar ρbar' η hη

end S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist
end P2MW
export P2MW.S_ResidualGaloisRep_nonempty_localFlatClassesAd_linearEquiv_of_dualTwist (solution)
