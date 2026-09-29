-- Prove2me | solution 1 for PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8004b648-9c90-5fa3-9d76-5c156dc9236a

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_eq_sum_pow_apply_smul_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp

set_option autoImplicit false

universe v

open CartierDual
open scoped TensorProduct

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.nsmulAlgHom Hopf.nsmulAlgHom_eq_sum_pow_apply_smul_pow"
namespace Hopf
p2m_export "PDivisibleGroup.Hopf" "nsmulAlgHom nsmulAlgHom_eq_sum_pow_apply_smul_pow"
namespace Verschiebung
p2m_open "PDivisibleGroup.Hopf PDivisibleGroup"

section

variable {p : ℕ} [Fact p.Prime] {A : Type v} [CommRing A] [HopfAlgebra (ZMod p) A]
  [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A]

omit [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A] in
omit [Module.Finite (ZMod p) A] in
omit [Module.Finite (ZMod p) A] in
omit [Module.Finite (ZMod p) A] in

private theorem nontrivial_A (h1 : Coalgebra.counit (R := ZMod p) (1 : A) = 1) : Nontrivial A := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg (Coalgebra.counit (R := ZMod p) (A := A)) h
  rw [h1, map_zero] at this
  exact one_ne_zero this

omit [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A] in
private theorem charP_A : CharP A p :=
  haveI := nontrivial_A (p := p) (A := A) Bialgebra.counit_one
  charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p

omit [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A] in
private theorem nontrivial_D : Nontrivial (CartierDual (ZMod p) A) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have := congrArg (fun φ : CartierDual (ZMod p) A => φ 1) h
  simp only [one_apply, Bialgebra.counit_one] at this
  exact one_ne_zero (this.trans rfl)

omit [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A] in
private theorem charP_D : CharP (CartierDual (ZMod p) A) p :=
  haveI := nontrivial_D (p := p) (A := A)
  charP_of_injective_algebraMap (algebraMap (ZMod p) (CartierDual (ZMod p) A)).injective p

private theorem sum_smul_pow {B : Type*} [CommRing B] [Algebra (ZMod p) B] [CharP B p]
    {ι : Type*} (s : Finset ι) (c : ι → ZMod p) (x : ι → B) :
    (∑ i ∈ s, c i • x i) ^ p = ∑ i ∈ s, c i • x i ^ p := by
  rw [sum_pow_char]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_pow, ZMod.pow_card]

omit [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A] in

private noncomputable def V {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) : A →ₗ[ZMod p] A :=
  ∑ i, (LinearMap.toSpanSingleton (ZMod p) A (b i)).comp
    ((toDual (ZMod p) A (ofDual (ZMod p) A (b.coord i) ^ p)) : A →ₗ[ZMod p] ZMod p)

omit [Module.Finite (ZMod p) A] in
private theorem V_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) (a : A) :
    V b a = ∑ i, (ofDual (ZMod p) A (b.coord i) ^ p) a • b i := by
  simp only [V, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply]
  rfl

omit [Module.Finite (ZMod p) A] in

private theorem apply_V {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) (φ : CartierDual (ZMod p) A)
    (a : A) : φ (V b a) = (φ ^ p) a := by
  haveI := charP_D (p := p) (A := A)
  rw [V_apply, map_sum]
  simp only [map_smul, smul_eq_mul]

  have hφ : φ = ∑ i, φ (b i) • ofDual (ZMod p) A (b.coord i) := by
    apply CartierDual.ext
    intro x
    have h := Module.Basis.sum_dual_apply_smul_coord b (toDual (ZMod p) A φ)
    have hx := congrArg (fun ψ : Module.Dual (ZMod p) A => ψ x) h
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, toDual_apply] at hx
    rw [← hx]
    change _ = (toDual (ZMod p) A (∑ i, φ (b i) • ofDual (ZMod p) A (b.coord i))) x
    rw [map_sum]
    simp only [map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, toDual_ofDual]
  conv_rhs => rw [hφ, sum_smul_pow]
  change _ = (toDual (ZMod p) A (∑ i, φ (b i) • ofDual (ZMod p) A (b.coord i) ^ p)) a
  rw [map_sum]
  simp only [map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    toDual_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Module.Finite (ZMod p) A] in
private theorem V_pow {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) (a : A) :
    (V b a) ^ p = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) A p a := by
  haveI := charP_A (p := p) (A := A)
  rw [V_apply, sum_smul_pow, PDivisibleGroup.Hopf.nsmulAlgHom_eq_sum_pow_apply_smul_pow b a]

private noncomputable abbrev β {ι : Type*} (b : Module.Basis ι (ZMod p) A) (i : ι) : CartierDual (ZMod p) A :=
  ofDual (ZMod p) A (b.coord i)

omit [Module.Finite (ZMod p) A] in

private theorem dual_expand {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A)
    (ψ : CartierDual (ZMod p) A) : ψ = ∑ i, ψ (b i) • β b i := by
  apply CartierDual.ext
  intro x
  have h := Module.Basis.sum_dual_apply_smul_coord b (toDual (ZMod p) A ψ)
  have hx := congrArg (fun χ : Module.Dual (ZMod p) A => χ x) h
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, toDual_apply] at hx
  rw [← hx]
  change _ = (toDual (ZMod p) A (∑ i, ψ (b i) • β b i)) x
  rw [map_sum]
  simp only [map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, toDual_ofDual]

omit [Module.Finite (ZMod p) A] in

private theorem sum_smul_pow_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A)
    (c : ι → ZMod p) (a : A) :
    ((∑ i, c i • β b i) ^ p) a = ∑ i, c i * (β b i ^ p) a := by
  haveI := charP_D (p := p) (A := A)
  rw [sum_smul_pow]
  change (toDual (ZMod p) A (∑ i, c i • β b i ^ p)) a = _
  rw [map_sum]
  simp only [map_smul, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    toDual_apply]

omit [Coalgebra.IsCocomm (ZMod p) A] in

private theorem eq_of_forall_apply_eq {x y : A} (h : ∀ φ : CartierDual (ZMod p) A, φ x = φ y) : x = y := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff (ZMod p) (x - y)).1 fun ψ => ?_
  rw [map_sub, sub_eq_zero]
  exact h (ofDual (ZMod p) A ψ)

omit [Module.Finite (ZMod p) A] in

private theorem pow_apply_one (φ : CartierDual (ZMod p) A) (n : ℕ) : (φ ^ n) 1 = (φ 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_apply, Bialgebra.counit_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.dualDistrib_apply, toDual_apply, toDual_apply, ih]

private theorem V_one {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) : V b 1 = 1 := by
  refine eq_of_forall_apply_eq (p := p) fun φ => ?_
  rw [apply_V, pow_apply_one, ZMod.pow_card]

omit [Module.Finite (ZMod p) A] in

private theorem pair_V_V {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) (x y : A)
    [CharP (CartierDual (ZMod p) A ⊗[ZMod p] CartierDual (ZMod p) A) p]
    (w : CartierDual (ZMod p) A ⊗[ZMod p] CartierDual (ZMod p) A) :
    TensorProduct.dualDistrib (ZMod p) A A
        (TensorProduct.map (toDual (ZMod p) A).toLinearMap (toDual (ZMod p) A).toLinearMap w) (V b x ⊗ₜ V b y) =
      TensorProduct.dualDistrib (ZMod p) A A
        (TensorProduct.map (toDual (ZMod p) A).toLinearMap (toDual (ZMod p) A).toLinearMap
          (frobenius (CartierDual (ZMod p) A ⊗[ZMod p] CartierDual (ZMod p) A) p w)) (x ⊗ₜ y) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul φ ψ =>
    have e : frobenius (CartierDual (ZMod p) A ⊗[ZMod p] CartierDual (ZMod p) A) p (φ ⊗ₜ[ZMod p] ψ) =
        (φ ^ p) ⊗ₜ[ZMod p] (ψ ^ p) :=
      (frobenius_def p _).trans (Algebra.TensorProduct.tmul_pow φ ψ p)
    rw [e, TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply,
      TensorProduct.dualDistrib_apply]
    change φ (V b x) * ψ (V b y) = (φ ^ p) x * (ψ ^ p) y
    rw [apply_V, apply_V]
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add, map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂]

private theorem V_mul {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) (x y : A) :
    V b (x * y) = V b x * V b y := by
  haveI : Nontrivial (CartierDual (ZMod p) A) := nontrivial_D (p := p) (A := A)
  haveI : Nontrivial (CartierDual (ZMod p) A ⊗[ZMod p] CartierDual (ZMod p) A) :=
    (Algebra.TensorProduct.lmul' (S := CartierDual (ZMod p) A) (ZMod p)).toRingHom.domain_nontrivial
  haveI : CharP (CartierDual (ZMod p) A ⊗[ZMod p] CartierDual (ZMod p) A) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) _).injective p
  refine eq_of_forall_apply_eq (p := p) fun φ => ?_
  have hΔ : frobenius (CartierDual (ZMod p) A ⊗[ZMod p] CartierDual (ZMod p) A) p
      (Coalgebra.comul (R := ZMod p) φ) = Coalgebra.comul (R := ZMod p) (φ ^ p) := by
    rw [frobenius_def]
    exact (map_pow (Bialgebra.comulAlgHom (ZMod p) (CartierDual (ZMod p) A)) φ p).symm
  rw [apply_V, ← comul_pairing (φ ^ p) x y, ← comul_pairing φ (V b x) (V b y), pair_V_V b x y, hΔ]

omit [Module.Finite (ZMod p) A] in

private theorem dualDistrib_map_V {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A)
    (φ ψ : CartierDual (ZMod p) A) (w : A ⊗[ZMod p] A) :
    TensorProduct.dualDistrib (ZMod p) A A (toDual (ZMod p) A φ ⊗ₜ toDual (ZMod p) A ψ)
        (TensorProduct.map (V b) (V b) w) =
      TensorProduct.dualDistrib (ZMod p) A A (toDual (ZMod p) A (φ ^ p) ⊗ₜ toDual (ZMod p) A (ψ ^ p)) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
    change φ (V b x) * ψ (V b y) = (φ ^ p) x * (ψ ^ p) y
    rw [apply_V, apply_V]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

private theorem comul_V {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) (a : A) :
    Coalgebra.comul (R := ZMod p) (V b a) =
      TensorProduct.map (V b) (V b) (Coalgebra.comul (R := ZMod p) a) := by

  have hsurj : Function.Surjective (TensorProduct.dualDistrib (ZMod p) A A) :=
    (TensorProduct.dualDistribEquiv (ZMod p) A A).surjective
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff (ZMod p) _).1 fun θ => ?_
  obtain ⟨z, rfl⟩ := hsurj θ
  rw [map_sub, sub_eq_zero]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    have h1 := mul_apply (ofDual (ZMod p) A f) (ofDual (ZMod p) A g) (V b a)
    have h2 := mul_apply (ofDual (ZMod p) A f ^ p) (ofDual (ZMod p) A g ^ p) a
    simp only [toDual_ofDual] at h1
    rw [← h1, apply_V, mul_pow, h2, ← dualDistrib_map_V b]
    rfl
  | add z₁ z₂ h₁ h₂ => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂]

omit [Module.Finite (ZMod p) A] in
private theorem counit_V {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) (a : A) :
    Coalgebra.counit (R := ZMod p) (V b a) = Coalgebra.counit (R := ZMod p) a := by
  rw [← one_apply (R := ZMod p) (V b a), apply_V, one_pow, one_apply]

private noncomputable def Vb {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) : A →ₐc[ZMod p] A :=
  BialgHom.ofAlgHom (AlgHom.ofLinearMap (V b) (V_one b) (V_mul b))
    (by
      refine AlgHom.ext fun a => ?_
      exact counit_V b a)
    (by
      refine AlgHom.ext fun a => ?_
      change Algebra.TensorProduct.map (AlgHom.ofLinearMap (V b) (V_one b) (V_mul b))
        (AlgHom.ofLinearMap (V b) (V_one b) (V_mul b)) (Coalgebra.comul (R := ZMod p) a) =
        Coalgebra.comul (R := ZMod p) (V b a)
      rw [comul_V b a]
      induction (Coalgebra.comul (R := ZMod p) a) using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]; rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy])

private theorem Vb_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι (ZMod p) A) (a : A) : Vb b a = V b a :=
  rfl

end

end PDivisibleGroup.Hopf.Verschiebung

open PDivisibleGroup.Hopf.Verschiebung in
theorem solution
    (p : ℕ) [Fact p.Prime] (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A]
    [Coalgebra.IsCocomm (ZMod p) A] [Module.Finite (ZMod p) A] :
    ∃ V : A →ₐc[ZMod p] A,
      (∀ a, (V a) ^ p = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) A p a) ∧
      (∀ a, V (a ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) A p a) ∧
      (∀ (φ : CartierDual (ZMod p) A) (a : A), φ (V a) = (φ ^ p) a) := by
  classical
  let b := Module.finBasis (ZMod p) A
  refine ⟨Vb b, fun a => V_pow b a, fun a => ?_, fun φ a => apply_V b φ a⟩
  rw [map_pow]
  exact V_pow b a

end S_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp (solution)
