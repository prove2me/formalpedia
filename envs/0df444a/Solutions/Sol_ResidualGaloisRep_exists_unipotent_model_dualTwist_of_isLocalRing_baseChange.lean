-- Prove2me | solution 1 for ResidualGaloisRep.exists_unipotent_model_dualTwist_of_isLocalRing_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/072c0974-bd03-5520-a5e3-cc0ea8e3538e

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
import Theorems.Thm_CartierDual_nonempty_ringEquiv_baseChange
import Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
import Theorems.Thm_ExtCitation_exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal
import Theorems.Thm_IsPrimitiveRoot_existsUnique_eq_pow_val
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_unipotent_model_dualTwist_of_isLocalRing_baseChange

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

open scoped TensorProduct

namespace E90DM

theorem exists_linearEquiv_dual_trace (F K V : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V] [FiniteDimensional K V] :
    ∃ T : Module.Dual K V ≃ₗ[F] (V →ₗ[F] F), ∀ μ v, T μ v = Algebra.trace F K (μ v) := by
  classical
  haveI : FiniteDimensional F V := Module.Finite.trans K V
  let T₀ : Module.Dual K V →ₗ[F] (V →ₗ[F] F) :=
    { toFun := fun μ => (Algebra.trace F K).comp (μ.restrictScalars F)
      map_add' := fun μ ν => by ext v; simp
      map_smul' := fun c μ => by ext v; simp }
  have hT₀ : ∀ μ v, T₀ μ v = Algebra.trace F K (μ v) := fun μ v => rfl
  have hinj : Function.Injective T₀ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro μ hμ
    apply LinearMap.ext
    intro v
    have hnd := (traceForm_nondegenerate F K).1
    refine hnd (μ v) (fun n => ?_)
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul, ← hT₀, hμ, LinearMap.zero_apply]
  have h1 : Module.finrank F (Module.Dual K V) = Module.finrank F K * Module.finrank K V := by
    rw [← Module.finrank_mul_finrank F K (Module.Dual K V), Subspace.dual_finrank_eq]
  have h2 : Module.finrank F (V →ₗ[F] F) = Module.finrank F K * Module.finrank K V := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one, Module.finrank_mul_finrank]
  have hdim : Module.finrank F (Module.Dual K V) = Module.finrank F (V →ₗ[F] F) := h1.trans h2.symm
  have hbij : Function.Bijective T₀ :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  exact ⟨LinearEquiv.ofBijective T₀ hbij, fun μ v => rfl⟩

end E90DM

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k)
    (hconn : ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (TensorProduct ℤ_[p] (ZMod p) H) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f))
    (ρbar' : ResidualGaloisRep k) (η : ρbar'.V ≃ₗ[k] Module.Dual k ρbar.V)
    (hη : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (w : ρbar'.V),
      η (ρbar'.ρ g w) =
        (ZMod.castHom (dvd_refl p) k ((cycloChar p g : (ZMod p)ˣ) : ZMod p)) • ((η w) ∘ₗ (ρbar.ρ g⁻¹))) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct ℤ_[p] (ZMod p) H)) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar'.V × ρbar'.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar'.dualLiftModuleActAd p 0 σ (e f) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨H, instCR, instHA, hfin, hflat, hcocomm, hloc, e, he_add, he_gal⟩ := hconn
  haveI := hfin; haveI := hflat; haveI := hcocomm
  haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing

  let H' := CartierDual ℤ_[p] H
  have hunip : IsLocalRing (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H')) := by
    haveI : IsLocalRing ((ZMod p) ⊗[ℤ_[p]] H) := hloc

    obtain ⟨e₁⟩ := CartierDual.nonempty_ringEquiv_baseChange ℤ_[p] (ZMod p) H'
    obtain ⟨e₂, -⟩ := CartierDual.exists_bialgEquiv_bidual ℤ_[p] H

    let e₃ : (ZMod p) ⊗[ℤ_[p]] H ≃ₐ[ZMod p] (ZMod p) ⊗[ℤ_[p]] CartierDual ℤ_[p] H' :=
      Algebra.TensorProduct.congr AlgEquiv.refl (e₂ : H ≃ₐc[ℤ_[p]] CartierDual ℤ_[p] H').toAlgEquiv
    let f : (ZMod p) ⊗[ℤ_[p]] H →+* CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H') :=
      e₁.symm.toRingHom.comp e₃.toAlgHom.toRingHom
    have hf : Function.Surjective f := e₁.symm.surjective.comp e₃.surjective
    haveI : Nontrivial ((ZMod p) ⊗[ℤ_[p]] CartierDual ℤ_[p] H') := e₃.symm.toEquiv.nontrivial
    haveI : Nontrivial (CartierDual (ZMod p) ((ZMod p) ⊗[ℤ_[p]] H')) := e₁.toEquiv.nontrivial
    exact IsLocalRing.of_surjective' f hf

  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI instFpV : Module (ZMod p) ρbar.V := Module.compHom ρbar.V (algebraMap (ZMod p) k)
  haveI : IsScalarTower (ZMod p) k ρbar.V := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  haveI : Module.Finite (ZMod p) k := Module.Finite.of_finite
  haveI : FiniteDimensional k ρbar.V := Module.finite_of_finrank_eq_succ ρbar.finrank_eq
  obtain ⟨T, hT⟩ := E90DM.exists_linearEquiv_dual_trace (ZMod p) k ρbar.V
  have halg : ∀ c : ZMod p, algebraMap (ZMod p) k c = ZMod.castHom (dvd_refl p) k c := fun c => rfl

  obtain ⟨d, hd_mul, hd_gal⟩ := CartierDual.exists_equiv_algHom_padicAlgCl_monoidHom_units p H
  obtain ⟨ζ, hζp, hζg⟩ :=
    ExtCitation.exists_isPrimitiveRoot_smul_eq_pow_cycloChar_localGaloisToGlobal p p
  have hinj : ∀ a b : ZMod p, ζ ^ a.val = ζ ^ b.val → a = b := fun a b h =>
    ZMod.val_injective p (hζp.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)
  have hpowadd : ∀ a b : ZMod p, ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
    intro a b
    rw [← pow_add, pow_eq_pow_iff_modEq, ← hζp.eq_orderOf, ← ZMod.natCast_eq_natCast_iff]
    simp only [ZMod.natCast_zmod_val, Nat.cast_add]
  have hpowmul : ∀ a b : ZMod p, ζ ^ (a * b).val = (ζ ^ a.val) ^ b.val := by
    intro a b
    rw [← pow_mul, pow_eq_pow_iff_modEq, ← hζp.eq_orderOf, ← ZMod.natCast_eq_natCast_iff]
    simp only [ZMod.natCast_zmod_val, Nat.cast_mul]

  have he_one : e 1 = 0 := by
    have h := he_add 1 1
    rw [mul_one] at h
    exact (left_eq_add.mp h)
  have he_pow : ∀ (f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)) (n : ℕ), e (f ^ n) = n • e f := by
    intro f n
    induction n with
    | zero => rw [pow_zero, he_one, zero_smul]
    | succ n ih => rw [pow_succ, he_add, ih, succ_nsmul]
  have hP_pow : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p), f ^ p = 1 := by
    intro f
    apply e.injective
    rw [he_pow, he_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  have he_symm_add : ∀ x y, e.symm (x + y) = e.symm x * e.symm y := by
    intro x y
    apply e.injective
    rw [he_add, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
  have hχp : ∀ (χ : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ) f, χ f ^ p = 1 :=
    fun χ f => by rw [← map_pow, hP_pow, map_one]

  have hlogex : ∀ χ : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ,
      ∃ c : ρbar.V × ρbar.V → ZMod p, ∀ x, χ (e.symm x) = ζ ^ (c x).val :=
    fun χ => (hζp.existsUnique_eq_pow_val (fun x => χ (e.symm x)) (fun x => hχp χ _)).exists
  choose lg hlg using hlogex
  have hlg_add : ∀ χ x y, lg χ (x + y) = lg χ x + lg χ y := by
    intro χ x y
    apply hinj
    rw [← hlg, he_symm_add, map_mul, hlg, hlg, hpowadd]
  have hlg_mul : ∀ χ χ' x, lg (χ * χ') x = lg χ x + lg χ' x := by
    intro χ χ' x
    apply hinj
    rw [← hlg, MonoidHom.mul_apply, hlg, hlg, hpowadd]

  let Lg : (WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ) → (ρbar.V × ρbar.V →ₗ[ZMod p] ZMod p) :=
    fun χ => AddMonoidHom.toZModLinearMap p
      { toFun := lg χ, map_zero' := by
          have h := hlg_add χ 0 0; rw [add_zero] at h; exact (left_eq_add.mp h)
        map_add' := hlg_add χ }
  have hLg : ∀ χ x, Lg χ x = lg χ x := fun χ x => rfl

  let μ₁ : WithConv (H' →ₐ[ℤ_[p]] PadicAlgCl p) → Module.Dual k ρbar.V :=
    fun φ => T.symm ((Lg (d φ)).comp (LinearMap.inl (ZMod p) ρbar.V ρbar.V))
  let μ₂ : WithConv (H' →ₐ[ℤ_[p]] PadicAlgCl p) → Module.Dual k ρbar.V :=
    fun φ => T.symm ((Lg (d φ)).comp (LinearMap.inr (ZMod p) ρbar.V ρbar.V))
  let F : WithConv (H' →ₐ[ℤ_[p]] PadicAlgCl p) → ρbar'.V × ρbar'.V :=
    fun φ => (η.symm (μ₁ φ), η.symm (μ₂ φ))
  have hTμ₁ : ∀ φ v, T (μ₁ φ) v = lg (d φ) (v, 0) := by
    intro φ v; simp only [μ₁, LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearMap.inl_apply, hLg]
  have hTμ₂ : ∀ φ v, T (μ₂ φ) v = lg (d φ) (0, v) := by
    intro φ v; simp only [μ₂, LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearMap.inr_apply, hLg]

  have hF_mul : ∀ φ ψ, F (φ * ψ) = F φ + F ψ := by
    intro φ ψ
    have h1 : μ₁ (φ * ψ) = μ₁ φ + μ₁ ψ := by
      apply T.injective
      ext v
      rw [map_add, LinearMap.add_apply, hTμ₁, hTμ₁, hTμ₁, hd_mul, hlg_mul]
    have h2 : μ₂ (φ * ψ) = μ₂ φ + μ₂ ψ := by
      apply T.injective
      ext v
      rw [map_add, LinearMap.add_apply, hTμ₂, hTμ₂, hTμ₂, hd_mul, hlg_mul]
    simp only [F, h1, h2, map_add, Prod.mk_add_mk]

  have hF_inj : Function.Injective F := by
    intro φ ψ h
    simp only [F, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : μ₁ φ = μ₁ ψ := η.symm.injective h1
    have h2' : μ₂ φ = μ₂ ψ := η.symm.injective h2
    apply d.injective
    ext f
    have hf : f = e.symm (e f) := (e.symm_apply_apply f).symm
    have hsplit : e f = ((e f).1, 0) + (0, (e f).2) := by simp
    rw [hf, hlg, hlg, hsplit, hlg_add, hlg_add, ← hTμ₁, ← hTμ₁, ← hTμ₂, ← hTμ₂, h1', h2']

  have hF_surj : Function.Surjective F := by
    rintro ⟨w₁, w₂⟩
    let Λ : ρbar.V × ρbar.V →ₗ[ZMod p] ZMod p := (T (η w₁)).coprod (T (η w₂))
    let χ : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →* (PadicAlgCl p)ˣ :=
      { toFun := fun f => ζ ^ (Λ (e f)).val
        map_one' := by rw [he_one, map_zero, ZMod.val_zero, pow_zero]
        map_mul' := fun f g => by rw [he_add, map_add, hpowadd] }
    have hχ : ∀ f, χ f = ζ ^ (Λ (e f)).val := fun f => rfl
    have hlgχ : ∀ x, lg χ x = Λ x := by
      intro x
      apply hinj
      rw [← hlg, hχ, e.apply_symm_apply]
    refine ⟨d.symm χ, ?_⟩
    have hm1 : μ₁ (d.symm χ) = η w₁ := by
      apply T.injective
      ext v
      rw [hTμ₁, d.apply_symm_apply, hlgχ]
      simp [Λ]
    have hm2 : μ₂ (d.symm χ) = η w₂ := by
      apply T.injective
      ext v
      rw [hTμ₂, d.apply_symm_apply, hlgχ]
      simp [Λ]
    simp only [F, hm1, hm2, LinearEquiv.symm_apply_apply]
  let e' : WithConv (H' →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar'.V × ρbar'.V := Equiv.ofBijective F ⟨hF_inj, hF_surj⟩
  have he' : ∀ φ, e' φ = F φ := fun φ => rfl

  have hF_gal : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (φ φ' : WithConv (H' →ₐ[ℤ_[p]] PadicAlgCl p)),
      (∀ h : H', φ' h = ResidualGaloisRep.localAut p σ (φ h)) →
        F φ' = ρbar'.dualLiftModuleActAd p 0 σ (F φ) := by
    intro σ φ φ' hφ'

    set g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := primeLocalToGlobal (pPrime p) σ with hg
    set c : ZMod p := ((cycloChar p (localGaloisToGlobal p σ) : (ZMod p)ˣ) : ZMod p) with hc
    have hcg : ((cycloChar p g : (ZMod p)ˣ) : ZMod p) = c := rfl

    have hact : ∀ (ρb : ResidualGaloisRep k) (x : ρb.V × ρb.V),
        ρb.dualLiftModuleActAd p 0 σ x =
          (ρb.ρ (primeLocalToGlobal (pPrime p) σ) x.1, ρb.ρ (primeLocalToGlobal (pPrime p) σ) x.2) := by
      intro ρb x
      simp only [ResidualGaloisRep.dualLiftModuleActAd]
      exact Prod.ext rfl (zero_add _)
    have hinvmul : ∀ v, ρbar.ρ g⁻¹ (ρbar.ρ g v) = v := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

    have hσζ : ResidualGaloisRep.localAut p σ ((ζ : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
        ((ζ ^ c.val : (PadicAlgCl p)ˣ) : PadicAlgCl p) := by
      have h := congrArg (fun u : (PadicAlgCl p)ˣ => (u : PadicAlgCl p)) (hζg σ)
      exact h

    have hback : ∀ f : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
        ∃ f₀ : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p),
          (∀ x, f x = ResidualGaloisRep.localAut p σ (f₀ x)) ∧
            e f₀ = (ρbar.ρ g⁻¹ (e f).1, ρbar.ρ g⁻¹ (e f).2) := by
      intro f
      let f₀ : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) := WithConv.toConv
        ((((ResidualGaloisRep.localAut p σ).symm.restrictScalars ℤ_[p]).toAlgHom).comp (WithConv.ofConv f))
      have hf₀ : ∀ x, f x = ResidualGaloisRep.localAut p σ (f₀ x) := by
        intro x
        show f x = ResidualGaloisRep.localAut p σ ((ResidualGaloisRep.localAut p σ).symm (f x))
        rw [AlgEquiv.apply_symm_apply]
      refine ⟨f₀, hf₀, ?_⟩
      have h := he_gal σ f₀ f hf₀
      rw [hact] at h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only at h1 h2
      apply Prod.ext
      · simp only; rw [h1, hinvmul]
      · simp only; rw [h2, hinvmul]

    have hval : ∀ x : ρbar.V × ρbar.V,
        lg (d φ') x = c * lg (d φ) (ρbar.ρ g⁻¹ x.1, ρbar.ρ g⁻¹ x.2) := by
      intro x
      obtain ⟨f₀, hf₀, hef₀⟩ := hback (e.symm x)
      rw [e.apply_symm_apply] at hef₀
      have h1 := hd_gal σ φ φ' hφ' f₀ (e.symm x) hf₀
      have h2 : d φ f₀ = ζ ^ (lg (d φ) (e f₀)).val := by rw [← hlg, e.symm_apply_apply]
      have h3 : d φ' (e.symm x) = ζ ^ (lg (d φ') x).val := hlg (d φ') x
      rw [h3, h2, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow] at h1
      change _ = (ResidualGaloisRep.localAut p σ ((ζ : (PadicAlgCl p)ˣ) : PadicAlgCl p)) ^ _ at h1
      rw [hσζ, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← hpowmul] at h1
      have h4 := hinj _ _ (Units.val_injective h1)
      rw [h4, hef₀, mul_comm]

    have key : ∀ (μ : WithConv (H' →ₐ[ℤ_[p]] PadicAlgCl p) → Module.Dual k ρbar.V)
        (ι : ρbar.V → ρbar.V × ρbar.V)
        (hι : ∀ v, ι (ρbar.ρ g⁻¹ v) = (ρbar.ρ g⁻¹ (ι v).1, ρbar.ρ g⁻¹ (ι v).2))
        (hTμ : ∀ ψ v, T (μ ψ) v = lg (d ψ) (ι v)),
        μ φ' = (ZMod.castHom (dvd_refl p) k c) • ((μ φ) ∘ₗ ρbar.ρ g⁻¹) := by
      intro μ ι hι hTμ
      apply T.injective
      ext v
      rw [hTμ, hval, ← hι, ← hTμ, hT, hT, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul,
        ← halg, ← Algebra.smul_def, map_smul, smul_eq_mul]
    have key1 := key μ₁ (fun v => (v, 0)) (fun v => by simp) hTμ₁
    have key2 := key μ₂ (fun v => (0, v)) (fun v => by simp) hTμ₂
    have hρ' : ∀ w : ρbar'.V, ρbar'.ρ g w =
        η.symm ((ZMod.castHom (dvd_refl p) k c) • ((η w) ∘ₗ ρbar.ρ g⁻¹)) := by
      intro w
      apply η.injective
      rw [hη, LinearEquiv.apply_symm_apply, hcg]
    rw [hact]
    apply Prod.ext
    · show η.symm (μ₁ φ') = ρbar'.ρ g (η.symm (μ₁ φ))
      rw [hρ', LinearEquiv.apply_symm_apply, key1]
    · show η.symm (μ₂ φ') = ρbar'.ρ g (η.symm (μ₂ φ))
      rw [hρ', LinearEquiv.apply_symm_apply, key2]
  refine ⟨H', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hunip, e', ?_, ?_⟩
  · intro φ ψ; rw [he', he', he', hF_mul]
  · intro σ φ φ' hφ; rw [he', he']; exact hF_gal σ φ φ' hφ

end S_ResidualGaloisRep_exists_unipotent_model_dualTwist_of_isLocalRing_baseChange
end P2MW
export P2MW.S_ResidualGaloisRep_exists_unipotent_model_dualTwist_of_isLocalRing_baseChange (solution)
