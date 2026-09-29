-- Prove2me | solution 1 for ResidualGaloisRep.exists_submodule_inertia_sub_mem_and_connected_model_of_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/0358b48a-4bdb-5d09-9f3e-a446ef418984

import Mathlib
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_exists_connected_etale_sequence_padicInt
import Theorems.Thm_HopfAlgebra_toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique
import Theorems.Thm_HopfAlgebra_exists_comp_antipode_convMul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ResidualGaloisRep_exists_submodule_inertia_sub_mem_and_connected_model_of_eq_top

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation
open scoped PadicInt TensorProduct Pointwise

namespace RpConnCrit

variable (p : ℕ) [Fact p.Prime]

theorem mem_decompositionSubgroup (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    τ ∈ (padicIntegers p).decompositionSubgroup ℚ_[p] := by
  rw [MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    mem_padicIntegers_iff, mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]

theorem conj_mem_inertiaSubgroupIn {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hσ : σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p]) (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    τ * σ * τ⁻¹ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by
  change σ ∈ Subgroup.map _ _ at hσ
  change τ * σ * τ⁻¹ ∈ Subgroup.map _ _
  rw [Subgroup.mem_map] at hσ ⊢
  obtain ⟨d, hd, rfl⟩ := hσ
  have hN : ((padicIntegers p).inertiaSubgroup ℚ_[p]).Normal := MonoidHom.normal_ker _
  let t : ↥((padicIntegers p).decompositionSubgroup ℚ_[p]) := ⟨τ, mem_decompositionSubgroup p τ⟩
  refine ⟨t * d * t⁻¹, hN.conj_mem d hd t, ?_⟩
  simp [t]

theorem smul_mem_closure {k M : Type} [Field k] [AddCommGroup M] [Module k M] (D : Set M)
    (hD : ∀ (a : k) (x : M), x ∈ D → a • x ∈ D) (a : k) (x : M) (hx : x ∈ AddSubmonoid.closure D) :
    a • x ∈ AddSubmonoid.closure D := by
  induction hx using AddSubmonoid.closure_induction with
  | mem z hz => exact AddSubmonoid.subset_closure (hD a z hz)
  | zero => rw [smul_zero]; exact zero_mem _
  | add z w _ _ hz hw => rw [smul_add]; exact add_mem hz hw

theorem span_le_closure {k M : Type} [Field k] [AddCommGroup M] [Module k M] (D : Set M)
    (hD : ∀ (a : k) (x : M), x ∈ D → a • x ∈ D) (x : M) (hx : x ∈ Submodule.span k D) :
    x ∈ AddSubmonoid.closure D := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact AddSubmonoid.subset_closure hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy => exact smul_mem_closure D hD a y hy

theorem main {k : Type} [Field k] [Finite k] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k) (hflat : ρbar.IsLocallyFlatCocycleAd p 0) :
    ∃ V₀ : Submodule k ρbar.V,
      (∀ (σ : primeLocalGaloisGroup (pPrime p)), ∀ v ∈ V₀,
        ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v ∈ V₀) ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
          ∀ v : ρbar.V, ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v - v ∈ V₀) ∧
      (V₀ = ⊤ → ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (TensorProduct ℤ_[p] (ZMod p) H) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f)) := by
  classical
  let ρ : primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V :=
    fun σ => ρbar.ρ (primeLocalToGlobal (pPrime p) σ)
  let D : Set ρbar.V := {x | ∃ σ : primeLocalGaloisGroup (pPrime p),
      ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧ ∃ v, x = ρ σ v - v}
  have hDsmul : ∀ (a : k) (x : ρbar.V), x ∈ D → a • x ∈ D := by
    rintro a x ⟨σ, hσ, v, rfl⟩
    exact ⟨σ, hσ, a • v, by rw [smul_sub, map_smul]⟩
  refine ⟨Submodule.span k D, ?_, ?_, ?_⟩
  ·
    intro τ v hv
    have hinv : ∀ w, ρ τ⁻¹ (ρ τ w) = w := by
      intro w
      show ρbar.ρ (primeLocalToGlobal (pPrime p) τ⁻¹) (ρbar.ρ (primeLocalToGlobal (pPrime p) τ) w) = w
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply]
    have h : Submodule.map (ρ τ) (Submodule.span k D) ≤ Submodule.span k D := by
      rw [Submodule.map_span_le]
      rintro x ⟨σ, hσ, w, rfl⟩
      refine Submodule.subset_span ⟨τ * σ * τ⁻¹, conj_mem_inertiaSubgroupIn p hσ τ, ρ τ w, ?_⟩
      show ρbar.ρ (primeLocalToGlobal (pPrime p) τ) (ρbar.ρ (primeLocalToGlobal (pPrime p) σ) w - w) =
        ρbar.ρ (primeLocalToGlobal (pPrime p) (τ * σ * τ⁻¹)) (ρbar.ρ (primeLocalToGlobal (pPrime p) τ) w) -
          ρbar.ρ (primeLocalToGlobal (pPrime p) τ) w
      rw [map_sub, map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact congrArg (fun u => ρ τ (ρ σ u) - ρ τ w) (hinv w).symm
    exact h (Submodule.mem_map_of_mem hv)
  ·
    intro σ hσ v
    exact Submodule.subset_span ⟨σ, hσ, v, rfl⟩
  ·
    intro htop
    obtain ⟨H, instCR, instHA, hfin, hfl, hco, e, he_add, he_act⟩ := hflat
    haveI : Module.Free ℤ_[p] H := Module.free_of_flat_of_isLocalRing
    refine ⟨H, instCR, instHA, hfin, hfl, hco, ?_, e, he_add, he_act⟩

    obtain ⟨H₀, _, _, Hₑ, _, _, π, ι, hfin0, hfree0, hco0, hloc0, hfinE, hfreeE, hcoE, -, hπsurj, -,
      hιinj, hrange, hrank, hcount, hexact, hext, hinert⟩ :=
      HopfAlgebra.exists_connected_etale_sequence_padicInt p H

    have hact0 : ∀ (σ : primeLocalGaloisGroup (pPrime p)) (x : ρbar.V × ρbar.V),
        ρbar.dualLiftModuleActAd p 0 σ x = (ρ σ x.1, ρ σ x.2) := by
      intro σ x
      refine Prod.ext rfl ?_
      show ((0 : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :
          primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ (ρ σ x.1) + ρ σ x.2 = ρ σ x.2
      have h0 : ((0 : cocycles₁ (Rep.res (primeLocalToGlobal (pPrime p)) (Rep.of ρbar.adRep))) :
          primeLocalGaloisGroup (pPrime p) → Module.End k ρbar.V) σ (ρ σ x.1) = 0 := rfl
      rw [h0, zero_add]

    have he1 : e 1 = 0 := by
      have h := he_add 1 1
      rw [mul_one] at h
      have h2 : e 1 + e 1 = e 1 + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    let pt : ρbar.V × ρbar.V → WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) := e.symm
    have hpt_add : ∀ x y, pt (x + y) = pt x * pt y := by
      intro x y
      apply e.injective
      rw [he_add]
      simp [pt]
    have hpt0 : pt 0 = 1 := by
      apply e.injective
      simp [pt, he1]
    let gal : primeLocalGaloisGroup (pPrime p) → WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →
        WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) := fun σ f =>
      WithConv.toConv (((ResidualGaloisRep.localAut p σ).toAlgHom.restrictScalars ℤ_[p]).comp
        (WithConv.ofConv f))
    have hgal : ∀ σ f (h : H), gal σ f h = ResidualGaloisRep.localAut p σ (f h) := fun _ _ _ => rfl
    have hpt_gal : ∀ σ x, pt (ρbar.dualLiftModuleActAd p 0 σ x) = gal σ (pt x) := by
      intro σ x
      apply e.injective
      rw [he_act σ (pt x) (gal σ (pt x)) (hgal σ (pt x))]
      simp [pt]

    haveI : Module.Flat ℤ_[p] H := hfl
    let ιc : Hₑ →ₐ[ℤ_[p]] ↥(HopfAlgebra.hopfKer π) :=
      (ι : Hₑ →ₐ[ℤ_[p]] H).codRestrict (HopfAlgebra.hopfKer π) (fun z => (hrange (ι z)).mpr ⟨z, rfl⟩)
    have hιc_bij : Function.Bijective ιc := by
      refine ⟨fun a b h => hιinj (congrArg Subtype.val h : _), fun y => ?_⟩
      obtain ⟨z, hz⟩ := (hrange y.1).mp y.2
      exact ⟨z, Subtype.ext hz⟩
    haveI : Module.Free ℤ_[p] Hₑ := hfreeE
    haveI : Module.Flat ℤ_[p] ↥(HopfAlgebra.hopfKer π) :=
      Module.Flat.of_linearEquiv (LinearEquiv.ofBijective ιc.toLinearMap hιc_bij).symm
    haveI : Module.Finite ℤ_[p] H₀ := hfin0
    haveI : Module.Free ℤ_[p] H₀ := hfree0
    obtain ⟨hres1, hresmul, -⟩ :=
      HopfAlgebra.toConv_comp_hopfKer_val_mul_and_eq_iff_existsUnique π hπsurj (PadicAlgCl p)
    let res : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) →
        WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[ℤ_[p]] PadicAlgCl p) :=
      fun f => WithConv.toConv ((WithConv.ofConv f).comp (HopfAlgebra.hopfKer π).val)
    have hres_def : ∀ f, res f = WithConv.toConv ((WithConv.ofConv f).comp (HopfAlgebra.hopfKer π).val) :=
      fun _ => rfl
    have hres_one : res 1 = 1 := hres1
    have hres_mul : ∀ f g, res (f * g) = res f * res g := hresmul

    have hinertK : ∀ σ : primeLocalGaloisGroup (pPrime p),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ (h' : ↥(HopfAlgebra.hopfKer π) →ₐ[ℤ_[p]] PadicAlgCl p) (y : ↥(HopfAlgebra.hopfKer π)),
          ResidualGaloisRep.localAut p σ (h' y) = h' y := by
      intro σ hσ h' y
      obtain ⟨z, hz⟩ := (hrange y.1).mp y.2
      have hy : y = ιc z := Subtype.ext hz.symm
      rw [hy]
      exact hinert (ResidualGaloisRep.localAut p σ) hσ (h'.comp ιc) z
    have hres_gal : ∀ σ : primeLocalGaloisGroup (pPrime p),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ f, res (gal σ f) = res f := by
      intro σ hσ f
      rw [hres_def, hres_def]
      congr 1
      ext y
      exact hinertK σ hσ ((WithConv.ofConv f).comp (HopfAlgebra.hopfKer π).val) y

    have hkey : ∀ σ : primeLocalGaloisGroup (pPrime p),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ x, res (pt (ρbar.dualLiftModuleActAd p 0 σ x - x)) = 1 := by
      intro σ hσ x
      obtain ⟨ν', -, -, hν'r⟩ :=
        HopfAlgebra.exists_comp_antipode_convMul_eq_one (WithConv.ofConv (pt x))
      have hinv : pt x * WithConv.toConv ν' = 1 := by simpa using hν'r
      have h2 : pt (ρbar.dualLiftModuleActAd p 0 σ x - x) * pt x = gal σ (pt x) := by
        rw [← hpt_add, sub_add_cancel, hpt_gal]
      have h3 : pt (ρbar.dualLiftModuleActAd p 0 σ x - x) = gal σ (pt x) * WithConv.toConv ν' := by
        rw [← h2, mul_assoc, hinv, mul_one]
      rw [h3, hres_mul, hres_gal σ hσ, ← hres_mul, hinv, hres_one]

    let K : AddSubmonoid (ρbar.V × ρbar.V) :=
      { carrier := {x | res (pt x) = 1}
        add_mem' := fun {x y} hx hy => by
          show res (pt (x + y)) = 1
          rw [hpt_add, hres_mul, hx, hy, mul_one]
        zero_mem' := by
          show res (pt 0) = 1
          rw [hpt0, hres_one] }
    have hmemK : ∀ x, x ∈ K ↔ res (pt x) = 1 := fun _ => Iff.rfl

    have hfst : ∀ v : ρbar.V, ((v, 0) : ρbar.V × ρbar.V) ∈ K := by
      intro v
      have hv : v ∈ Submodule.span k D := by rw [htop]; exact Submodule.mem_top
      have hcl := span_le_closure D hDsmul v hv
      have hle : AddSubmonoid.closure D ≤ K.comap (AddMonoidHom.inl ρbar.V ρbar.V) := by
        rw [AddSubmonoid.closure_le]
        rintro x ⟨σ, hσ, w, rfl⟩
        show ((ρ σ w - w, 0) : ρbar.V × ρbar.V) ∈ K
        have h := hkey σ hσ (w, 0)
        rw [hact0] at h
        rw [hmemK]
        convert h using 3
        ext <;> simp
      exact hle hcl
    have hsnd : ∀ w : ρbar.V, ((0, w) : ρbar.V × ρbar.V) ∈ K := by
      intro w
      have hw : w ∈ Submodule.span k D := by rw [htop]; exact Submodule.mem_top
      have hcl := span_le_closure D hDsmul w hw
      have hle : AddSubmonoid.closure D ≤ K.comap (AddMonoidHom.inr ρbar.V ρbar.V) := by
        rw [AddSubmonoid.closure_le]
        rintro x ⟨σ, hσ, u, rfl⟩
        show ((0, ρ σ u - u) : ρbar.V × ρbar.V) ∈ K
        have h := hkey σ hσ (0, u)
        rw [hact0] at h
        rw [hmemK]
        convert h using 3
        ext <;> simp
      exact hle hcl
    have hall : ∀ x : ρbar.V × ρbar.V, res (pt x) = 1 := by
      intro x
      have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
      rw [hx]
      exact K.add_mem (hfst x.1) (hsnd x.2)

    have htrivE : ∀ h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p,
        h = (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] Hₑ) := by
      intro h
      obtain ⟨f, hf⟩ := hext h
      rw [← hf]
      have h1 : res (WithConv.toConv f) = 1 := by
        have := hall (e (WithConv.toConv f))
        simpa [pt] using this
      have h2 : f.comp (HopfAlgebra.hopfKer π).val =
          (WithConv.ofConv (1 : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p))).comp (HopfAlgebra.hopfKer π).val := by
        have h' := congrArg WithConv.ofConv (h1.trans hres_one.symm)
        simpa [hres_def] using h'
      have h3 : f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) = (f.comp (HopfAlgebra.hopfKer π).val).comp ιc := by
        ext z; rfl
      rw [h3, h2]
      ext z
      change (WithConv.ofConv (1 : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p))) (ι z) =
        algebraMap ℤ_[p] (PadicAlgCl p) (Coalgebra.counit z)
      rw [← CoalgHomClass.counit_comp_apply (ι : Hₑ →ₐc[ℤ_[p]] H) z]
      rfl

    have hcard1 : Nat.card (Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨_, htrivE⟩
    have hrkE : Module.finrank ℤ_[p] Hₑ = 1 := by rw [← hcount, hcard1]
    have hrk : Module.finrank ℤ_[p] H = Module.finrank ℤ_[p] H₀ := by rw [hrank, hrkE, mul_one]
    have hπinj : Function.Injective π := by
      have iso := LinearEquiv.ofFinrankEq H H₀ hrk
      exact OrzechProperty.injective_of_surjective_of_injective iso.toLinearMap
        (π : H →ₐ[ℤ_[p]] H₀).toLinearMap iso.injective hπsurj
    haveI : IsLocalRing H₀ := hloc0
    let eqv : H ≃+* H₀ := RingEquiv.ofBijective (π : H →ₐ[ℤ_[p]] H₀) ⟨hπinj, hπsurj⟩
    haveI : Nontrivial H := eqv.toEquiv.nontrivial
    haveI : IsLocalRing H := IsLocalRing.of_surjective' (eqv.symm : H₀ →+* H) eqv.symm.surjective

    have hsurjT : Function.Surjective
        (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | tmul a h =>
        obtain ⟨r, rfl⟩ := ZMod.ringHom_surjective (algebraMap ℤ_[p] (ZMod p)) a
        refine ⟨r • h, ?_⟩
        rw [map_smul, Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul',
          TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, map_add _ _ _⟩
    haveI : Nontrivial ((ZMod p) ⊗[ℤ_[p]] H) :=
      (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] (ZMod p))
        (Bialgebra.counitAlgHom ℤ_[p] H)).toRingHom.domain_nontrivial
    exact IsLocalRing.of_surjective'
      (Algebra.TensorProduct.includeRight : H →ₐ[ℤ_[p]] (ZMod p) ⊗[ℤ_[p]] H).toRingHom hsurjT

end RpConnCrit

theorem solution
    {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) [CharP k p]
    [Algebra ℤ_[p] (ZMod p)] (hker : RingHom.ker (algebraMap ℤ_[p] (ZMod p)) = Ideal.span {(p : ℤ_[p])})
    (ρbar : ResidualGaloisRep k) (hflat : ρbar.IsLocallyFlatCocycleAd p 0) :
    ∃ V₀ : Submodule k ρbar.V,
      (∀ (σ : primeLocalGaloisGroup (pPrime p)), ∀ v ∈ V₀,
        ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v ∈ V₀) ∧
      (∀ (σ : primeLocalGaloisGroup (pPrime p)),
        ResidualGaloisRep.localAut p σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
          ∀ v : ρbar.V, ρbar.ρ (primeLocalToGlobal (pPrime p) σ) v - v ∈ V₀) ∧
      (V₀ = ⊤ → ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra ℤ_[p] H),
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      IsLocalRing (TensorProduct ℤ_[p] (ZMod p) H) ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρbar.V × ρbar.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : primeLocalGaloisGroup (pPrime p)) (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = ResidualGaloisRep.localAut p σ (f h)) →
            e g = ρbar.dualLiftModuleActAd p 0 σ (e f)) :=
  RpConnCrit.main p hp2 hker ρbar hflat

end S_ResidualGaloisRep_exists_submodule_inertia_sub_mem_and_connected_model_of_eq_top
end P2MW
export P2MW.S_ResidualGaloisRep_exists_submodule_inertia_sub_mem_and_connected_model_of_eq_top (solution)
