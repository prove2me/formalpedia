-- Prove2me | solution 1 for WeierstrassCurve.exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5cb795b7-164b-5d59-a5c0-21db9bcc1826

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_CuspForm_mem_intLattice_iff
import Theorems.Thm_CuspForm_intLattice_fg
import Theorems.Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra
import Theorems.Thm_CuspForm_HasIntegralStructure_eq_zero_of_forall_mem_intLattice
import Theorems.Thm_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0
import Theorems.Thm_E34D_exists_ringHom_algebraicClosure_ker_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra

set_option autoImplicit false

open CuspForm ModPForms

namespace E34Eig

open Submodule in
theorem exists_addMonoidHom_semilinear {R N F : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (hfaith : ∀ r : R, (∀ x : N, r • x = 0) → r = 0)
    [Field F] (θ : R →+* F) {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hθ : ∀ r ∈ 𝔪, θ r = 0) :
    ∃ Λ : N →+ F, Λ ≠ 0 ∧ ∀ (r : R) (x : N), Λ (r • x) = θ r * Λ x := by
  classical

  have hne : (𝔪 • ⊤ : Submodule R N) ≠ ⊤ := by
    intro htop
    obtain ⟨r, hr1, hr0⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 (⊤ : Submodule R N)
        Module.Finite.fg_top (by rw [htop])
    have hr : r = 0 := hfaith r fun x => hr0 x mem_top
    rw [hr, zero_sub] at hr1
    have h1 : (1 : R) ∈ 𝔪 := by simpa using 𝔪.neg_mem hr1
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one 𝔪).mpr h1)
  obtain ⟨x₀, -, hx₀⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)

  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hq₀ : Submodule.Quotient.mk (p := (𝔪 • ⊤ : Submodule R N)) x₀ ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hx₀
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (R ⧸ 𝔪) hq₀

  let θbar : R ⧸ 𝔪 →+* F := Ideal.Quotient.lift 𝔪 θ hθ
  refine ⟨θbar.toAddMonoidHom.comp
      (f.toAddMonoidHom.comp (Submodule.mkQ (𝔪 • ⊤ : Submodule R N)).toAddMonoidHom), ?_, ?_⟩
  · intro h0
    have h1 := DFunLike.congr_fun h0 x₀
    change θbar (f (Submodule.Quotient.mk x₀)) = 0 at h1
    exact hf ((map_eq_zero_iff θbar θbar.injective).mp h1)
  · intro r x
    change θbar (f (Submodule.Quotient.mk (r • x))) = θ r * θbar (f (Submodule.Quotient.mk x))
    rw [← Module.Quotient.mk_smul_mk (M := N) (I := 𝔪), map_smul, smul_eq_mul, map_mul,
      Ideal.Quotient.lift_mk]

theorem exists_addMonoidHom_semilinear_of_ringHom {R N F : Type*} [CommRing R] [AddCommGroup N]
    [Module.Finite ℤ N] (σ : R →+* Module.End ℤ N) (hfaith : ∀ r : R, σ r = 0 → r = 0)
    [Field F] (θ : R →+* F) {𝔪 : Ideal R} (h𝔪 : 𝔪.IsMaximal) (hθ : ∀ r ∈ 𝔪, θ r = 0) :
    ∃ Λ : N →+ F, Λ ≠ 0 ∧ ∀ (r : R) (x : N), Λ (σ r x) = θ r * Λ x := by
  letI : Module R N := Module.compHom N σ
  have hsmul : ∀ (r : R) (x : N), r • x = σ r x := fun _ _ => rfl
  haveI : IsScalarTower ℤ R N :=
    ⟨fun m r x => by rw [hsmul, hsmul, map_zsmul, LinearMap.smul_apply]⟩
  haveI : Module.Finite R N := Module.Finite.of_restrictScalars_finite ℤ R N
  obtain ⟨Λ, h0, h⟩ := exists_addMonoidHom_semilinear (R := R) (N := N)
    (fun r hr => hfaith r (LinearMap.ext fun x => hr x)) θ h𝔪 hθ
  exact ⟨Λ, h0, fun r x => h r x⟩

end E34Eig

namespace E34EigApp

variable {N' : ℕ} [NeZero N'] {k : ℤ}

abbrev V (N' : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma0 N') k

theorem isAddTorsionFree_V (N' : ℕ) (k : ℤ) : IsAddTorsionFree (V N' k) where
  nsmul_right_injective n hn a b hab := by
    have h : (n : ℂ) • a = (n : ℂ) • b := by
      simpa only [Nat.cast_smul_eq_nsmul] using hab
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hn) h

theorem hΓ (N' : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N')).strictPeriods :=
  CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N'

omit [NeZero N'] in

theorem qCoeff_add (f g : V N' k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑f + ⇑g) n = ModularFormClass.qCoeff f n + ModularFormClass.qCoeff g n := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_add one_pos (hΓ N') f g, map_add]

omit [NeZero N'] in

theorem qCoeff_smul (c : ℂ) (f : V N' k) (n : ℕ) :
    ModularFormClass.qCoeff (c • ⇑f) n = c * ModularFormClass.qCoeff f n := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_smul one_pos (hΓ N') c f, map_smul, smul_eq_mul]

abbrev L (N' : ℕ) (k : ℤ) := ↥(CuspForm.intLattice N' k)

private abbrev _root_.E34EigApp.T (N' : ℕ) [NeZero N'] (k : ℤ) (S₀ : Set ℕ) := ↥(heckeAlgebra N' k S₀)

p2m_export "E34EigApp" "T"

abbrev D (N' : ℕ) (k : ℤ) := Module.Dual ℤ (L N' k)

noncomputable def ic (f : L N' k) (n : ℕ) : ℤ :=
  ((CuspForm.mem_intLattice_iff (f : V N' k)).mp f.2 n).choose

omit [NeZero N'] in
theorem ic_spec (f : L N' k) (n : ℕ) :
    ModularFormClass.qCoeff (f : V N' k) n = (ic f n : ℂ) :=
  ((CuspForm.mem_intLattice_iff (f : V N' k)).mp f.2 n).choose_spec

theorem ic_add (f g : L N' k) (n : ℕ) : ic (f + g) n = ic f n + ic g n := by
  have h : ((ic (f + g) n : ℤ) : ℂ) = ((ic f n + ic g n : ℤ) : ℂ) := by
    rw [← ic_spec, Int.cast_add, ← ic_spec, ← ic_spec, Submodule.coe_add, CuspForm.coe_add,
      qCoeff_add]
  exact_mod_cast h

noncomputable def cf (n : ℕ) : Module.Dual ℤ (L N' k) :=
  (AddMonoidHom.mk' (fun f : L N' k => ic f n) (fun f g => ic_add f g n)).toIntLinearMap

@[scoped simp] theorem cf_apply (n : ℕ) (f : L N' k) : cf n f = ic f n := rfl

noncomputable def actL {S₀ : Set ℕ} (hk : 1 ≤ k) (t : heckeAlgebra N' k S₀) : L N' k →ₗ[ℤ] L N' k where
  toFun f := ⟨(t : Module.End ℂ (V N' k)) (f : V N' k),
    CuspForm.mem_intLattice_of_mem_heckeAlgebra hk t.2 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
  map_smul' m f := by
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, map_zsmul, eq_intCast, Int.cast_id]

@[scoped simp] theorem coe_actL {S₀ : Set ℕ} (hk : 1 ≤ k) (t : heckeAlgebra N' k S₀) (f : L N' k) :
    ((actL hk t f : L N' k) : V N' k) = (t : Module.End ℂ (V N' k)) (f : V N' k) := rfl

theorem actL_mul {S₀ : Set ℕ} (hk : 1 ≤ k) (t s : heckeAlgebra N' k S₀) :
    actL hk (t * s) = actL hk t ∘ₗ actL hk s := by
  ext f
  rfl

theorem actL_comm {S₀ : Set ℕ} (hk : 1 ≤ k) (t s : heckeAlgebra N' k S₀) :
    actL hk t ∘ₗ actL hk s = actL hk s ∘ₗ actL hk t := by
  rw [← actL_mul, ← actL_mul, mul_comm]

noncomputable def σ {S₀ : Set ℕ} (hk : 1 ≤ k) :
    heckeAlgebra N' k S₀ →+* Module.End ℤ (Module.Dual ℤ (L N' k)) where
  toFun t := (actL hk t).dualMap
  map_one' := by
    have h : actL hk (1 : heckeAlgebra N' k S₀) = LinearMap.id := by ext f; rfl
    rw [h, LinearMap.dualMap_id]
    rfl
  map_mul' t s := by
    rw [actL_mul, actL_comm, ← LinearMap.dualMap_comp_dualMap]
    rfl
  map_zero' := by
    have h : actL hk (0 : heckeAlgebra N' k S₀) = 0 := by
      ext f
      simp only [coe_actL, ZeroMemClass.coe_zero, LinearMap.zero_apply]
    apply LinearMap.ext; intro g; apply LinearMap.ext; intro f
    simp [LinearMap.dualMap_apply, h]
  map_add' t s := by
    have h : actL hk (t + s) = actL hk t + actL hk s := by
      ext f
      simp only [coe_actL, Subalgebra.coe_add, LinearMap.add_apply, Submodule.coe_add]
    apply LinearMap.ext; intro g; apply LinearMap.ext; intro f
    simp [LinearMap.dualMap_apply, h]

theorem σ_apply {S₀ : Set ℕ} (hk : 1 ≤ k) (t : heckeAlgebra N' k S₀) (g : Module.Dual ℤ (L N' k))
    (f : L N' k) : σ hk t g f = g (actL hk t f) := by
  simp [σ, LinearMap.dualMap_apply]

theorem ic_heckeT {S₀ : Set ℕ} (hk : 1 ≤ k) (hk2 : 2 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (hℓS : ℓ ∉ S₀) (f : L N' k) (n : ℕ) :
    ic (actL hk (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) f) n =
      ic f (n * ℓ) + if ℓ ∣ n then (ℓ : ℤ) ^ (k - 1).toNat * ic f (n / ℓ) else 0 := by
  have hkm : ((ℓ : ℂ) ^ (k - 1 : ℤ)) = (ℓ : ℂ) ^ (k - 1).toNat := by
    rw [← zpow_natCast]
    congr 1
    omega
  have h : ((ic (actL hk (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) f) n : ℤ) : ℂ) =
      ((ic f (n * ℓ) + if ℓ ∣ n then (ℓ : ℤ) ^ (k - 1).toNat * ic f (n / ℓ) else 0 : ℤ) : ℂ) := by
    rw [← ic_spec, coe_actL, heckeAlgebra.coe_T]
    change ModularFormClass.qCoeff (ModularForm.heckeT k ℓ ⇑(f : V N' k)) n = _
    rw [ModularFormClass.qCoeff_heckeT (f : V N' k) (hΓ N') hℓ.ne_zero n,
      ModularForm.coeffHeckeT_apply, ic_spec]
    split_ifs with hd
    · rw [ic_spec, hkm]
      push_cast
      ring
    · push_cast
      ring
  exact_mod_cast h

theorem σ_T_cf {S₀ : Set ℕ} (hk : 1 ≤ k) (hk2 : 2 ≤ k) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N')
    (hℓS : ℓ ∉ S₀) (n : ℕ) :
    σ hk (heckeAlgebra.T hℓ hℓN hℓS : heckeAlgebra N' k S₀) (cf n) =
      cf (n * ℓ) + if ℓ ∣ n then ((ℓ : ℤ) ^ (k - 1).toNat) • cf (n / ℓ) else 0 := by
  apply LinearMap.ext
  intro f
  rw [σ_apply, cf_apply, ic_heckeT hk hk2 hℓ hℓN hℓS f n]
  split_ifs with hd
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, cf_apply, smul_eq_mul]
  · simp only [add_zero, cf_apply]

end E34EigApp
p2m_reactivate "P2MW.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra.E34EigApp"

set_option synthInstance.maxHeartbeats 1600000 in
open E34EigApp in
theorem solution (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℤ)
    (N' : ℕ) [NeZero N'] (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (k : ℤ) (hk : 2 ≤ k) (hint : HasIntegralStructure N' k) (i : ℕ)
    (𝔪ₖ : Ideal (heckeAlgebra N' k S₀)) (h𝔪ₖ : 𝔪ₖ.IsMaximal)
    (hp𝔪ₖ : (p : heckeAlgebra N' k S₀) ∈ 𝔪ₖ)
    (hocc : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (hℓN : ¬ ℓ ∣ N'),
      W.IsGoodPrimeFor ℓ →
        heckeAlgebra.T hℓ hℓN hℓS -
          ((ℓ ^ i * W.apOfModel ℓ : ℤ) : heckeAlgebra N' k S₀) ∈ 𝔪ₖ) :
    ∃ (φ : PowerSeries (AlgebraicClosure (ZMod p))) (lam : ℕ → AlgebraicClosure (ZMod p)),
      φ ∈ modPCusp N' k (AlgebraicClosure (ZMod p)) ∧ IsModPEigen N' S₀ k φ lam ∧
        ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → ¬ ℓ ∣ N' → W.IsGoodPrimeFor ℓ →
          lam ℓ = ((ℓ ^ i * W.apOfModel ℓ : ℤ) : AlgebraicClosure (ZMod p)) := by
  classical
  have hk1 : (1 : ℤ) ≤ k := by omega

  haveI : Module.Finite ℤ (T N' k S₀) :=
    CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hint hk1 S₀
  obtain ⟨θ, hθ⟩ := E34D.exists_ringHom_algebraicClosure_ker_eq (p := p) h𝔪ₖ hp𝔪ₖ
  have hθ0 : ∀ r ∈ 𝔪ₖ, θ r = 0 := fun r hr => by
    rw [← RingHom.mem_ker, hθ]; exact hr

  haveI : IsAddTorsionFree (V N' k) := isAddTorsionFree_V N' k
  haveI : Module.Finite ℤ (L N' k) := Module.Finite.iff_fg.mpr (CuspForm.intLattice_fg N' k)
  haveI : Module.IsTorsionFree ℤ (L N' k) := inferInstance
  haveI : Module.Free ℤ (L N' k) := Module.free_of_finite_type_torsion_free'
  haveI : Module.Finite ℤ (D N' k) := Module.Finite.of_basis (Module.finBasis ℤ (L N' k)).dualBasis

  have hfaith : ∀ t : T N' k S₀, σ hk1 t = 0 → t = 0 := by
    intro t ht
    apply Subtype.ext
    change (t : Module.End ℂ (V N' k)) = 0
    apply CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice hint
    intro f hf
    have hzero : actL hk1 t ⟨f, hf⟩ = 0 := by
      rw [← Module.forall_dual_apply_eq_zero_iff ℤ (actL hk1 t ⟨f, hf⟩)]
      intro g
      have h1 : σ hk1 t g (⟨f, hf⟩ : L N' k) = 0 := by rw [ht, LinearMap.zero_apply, LinearMap.zero_apply]
      rwa [σ_apply] at h1
    simpa using congrArg (fun x : L N' k => (x : V N' k)) hzero
  obtain ⟨Λ, hΛ0, hΛ⟩ :=
    E34Eig.exists_addMonoidHom_semilinear_of_ringHom (σ hk1 (S₀ := S₀)) hfaith θ h𝔪ₖ hθ0

  let φ : PowerSeries (AlgebraicClosure (ZMod p)) := PowerSeries.mk fun n => Λ (cf n)
  have hφc : ∀ n, PowerSeries.coeff n φ = Λ (cf n) := fun n => PowerSeries.coeff_mk _ _
  let lam : ℕ → AlgebraicClosure (ZMod p) := fun ℓ =>
    if h : ℓ.Prime ∧ ¬ ℓ ∣ N' ∧ ℓ ∉ S₀ then θ (heckeAlgebra.T h.1 h.2.1 h.2.2) else 0
  have heigen : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N') (hℓS : ℓ ∉ S₀),
      heckePS k ℓ φ = θ (heckeAlgebra.T hℓ hℓN hℓS) • φ := by
    intro ℓ hℓ hℓN hℓS
    have hkm : ((ℓ : AlgebraicClosure (ZMod p)) ^ (k - 1 : ℤ)) =
        (ℓ : AlgebraicClosure (ZMod p)) ^ (k - 1).toNat := by
      rw [← zpow_natCast]
      congr 1
      omega
    ext n
    rw [map_smul, smul_eq_mul, hφc, ← hΛ, σ_T_cf hk1 hk hℓ hℓN hℓS n]
    unfold heckePS
    rw [PowerSeries.coeff_mk, hφc]
    split_ifs with hd
    · rw [map_add, map_zsmul, hφc, zsmul_eq_mul, hkm]
      push_cast
      ring
    · rw [add_zero, add_zero]

  let bL := Module.finBasis ℤ (L N' k)
  let red : Fin (Module.finrank ℤ (L N' k)) → PowerSeries (AlgebraicClosure (ZMod p)) := fun j =>
    PowerSeries.mk fun n => ((ic (bL j) n : ℤ) : AlgebraicClosure (ZMod p))
  have hred : ∀ j, red j ∈ modPCusp N' k (AlgebraicClosure (ZMod p)) := fun j =>
    Submodule.subset_span ⟨((bL j : L N' k) : V N' k), ic (bL j), fun n => ic_spec _ _, rfl⟩
  have hΛcf : ∀ n, Λ (cf n) = ∑ j, (ic (bL j) n : AlgebraicClosure (ZMod p)) * Λ (bL.coord j) := by
    intro n
    conv_lhs => rw [← bL.sum_dual_apply_smul_coord (cf n)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, zsmul_eq_mul, cf_apply]
  have hφsum : φ = ∑ j, Λ (bL.coord j) • red j := by
    ext n
    rw [hφc, hΛcf, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, PowerSeries.coeff_mk, smul_eq_mul, mul_comm]
  have hφmem : φ ∈ modPCusp N' k (AlgebraicClosure (ZMod p)) := by
    rw [hφsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hred j)

  have hφne : φ ≠ 0 := by

    have hex : ∃ j, Λ (bL.coord j) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hΛ0
      have hlin : Λ.toIntLinearMap = 0 := by
        refine bL.dualBasis.ext fun j => ?_
        rw [LinearMap.zero_apply, Module.Basis.coe_dualBasis]
        exact hall j
      ext g
      exact LinearMap.congr_fun hlin g
    obtain ⟨j₀, hj₀⟩ := hex
    intro hφ0
    have hcoef : ∀ n, ∑ j, (ic (bL j) n : AlgebraicClosure (ZMod p)) * Λ (bL.coord j) = 0 := fun n => by
      rw [← hΛcf, ← hφc, hφ0, map_zero]

    obtain ⟨μ, hμ⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hj₀
    set w : Fin (Module.finrank ℤ (L N' k)) → ZMod p := fun j => μ (Λ (bL.coord j))
    have hw : ∀ n, ∑ j, (ic (bL j) n : ZMod p) * w j = 0 := by
      intro n
      have h := congrArg μ (hcoef n)
      rw [map_zero, map_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← map_intCast (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))), ← Algebra.smul_def, map_smul,
        smul_eq_mul]

    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    let c : Fin (Module.finrank ℤ (L N' k)) → ℤ := fun j => ((w j).val : ℤ)
    have hc : ∀ j, (c j : ZMod p) = w j := fun j => by
      simp [c]
    let x : L N' k := ∑ j, c j • bL j
    have hx : ∀ n, ic x n = ∑ j, c j * ic (bL j) n := by
      intro n
      rw [← cf_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, zsmul_eq_mul, cf_apply, Int.cast_id]
    have hdvd : ∀ n, (p : ℤ) ∣ ic x n := by
      intro n
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hx, Int.cast_sum]
      rw [← hw n]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Int.cast_mul, hc, mul_comm]
    choose d hd using hdvd

    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    set y : V N' k := (p : ℂ)⁻¹ • (x : V N' k) with hy_def
    have hy : y ∈ CuspForm.intLattice N' k := by
      rw [CuspForm.mem_intLattice_iff]
      intro n
      refine ⟨d n, ?_⟩
      rw [hy_def, CuspForm.IsGLPos.coe_smul, qCoeff_smul, ic_spec, hd n]
      push_cast
      field_simp
    have hxy : x = (p : ℤ) • (⟨y, hy⟩ : L N' k) := by
      apply Subtype.ext
      change (x : V N' k) = ((p : ℤ) • (⟨y, hy⟩ : L N' k) : L N' k)
      rw [Submodule.coe_smul_of_tower]
      change (x : V N' k) = (p : ℤ) • y
      rw [← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, hy_def, smul_inv_smul₀ hp0]

    have hcoord : c j₀ = (p : ℤ) * bL.repr ⟨y, hy⟩ j₀ := by
      have h1 : bL.repr x j₀ = c j₀ := congrFun (bL.repr_sum_self c) j₀
      rw [← h1, hxy, map_zsmul, Finsupp.smul_apply, smul_eq_mul]
    have hw0 : w j₀ = 0 := by
      rw [← hc, hcoord]
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    exact hμ hw0
  refine ⟨φ, lam, hφmem, ⟨hφne, ?_⟩, ?_⟩
  · intro ℓ hℓ hℓN hℓS
    have hl : lam ℓ = θ (heckeAlgebra.T hℓ hℓN hℓS) := by
      simp only [lam, dif_pos (show ℓ.Prime ∧ ¬ ℓ ∣ N' ∧ ℓ ∉ S₀ from ⟨hℓ, hℓN, hℓS⟩)]
    rw [hl]
    exact heigen ℓ hℓ hℓN hℓS
  · intro ℓ hℓ hℓS hℓN hgood
    have hl : lam ℓ = θ (heckeAlgebra.T hℓ hℓN hℓS) := by
      simp only [lam, dif_pos (show ℓ.Prime ∧ ¬ ℓ ∣ N' ∧ ℓ ∉ S₀ from ⟨hℓ, hℓN, hℓS⟩)]
    have hmem := hθ0 _ (hocc ℓ hℓ hℓS hℓN hgood)
    rw [map_sub, sub_eq_zero, map_intCast] at hmem
    rw [hl, hmem]

end S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra
end P2MW
export P2MW.S_WeierstrassCurve_exists_mem_modPCusp_isModPEigen_pow_mul_apOfModel_of_ideal_heckeAlgebra (solution)
