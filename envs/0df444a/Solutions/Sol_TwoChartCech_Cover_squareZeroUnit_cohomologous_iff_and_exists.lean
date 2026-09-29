-- Prove2me | solution 1 for TwoChartCech.Cover.squareZeroUnit_cohomologous_iff_and_exists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b73b301c-3423-599b-8559-eb5a38731c8f

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists

set_option autoImplicit false

open scoped TensorProduct
open TrivSqZeroExt

universe u

namespace P2mTJ2a

noncomputable section

variable {K : Type u} [Field K]
variable {V : Type u} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

section Decomp

variable (K V)
variable (B : Type u) [CommRing B] [Algebra K B]

def red : TrivSqZeroExt K V ⊗[K] B →ₐ[K] B :=
  Algebra.TensorProduct.lift ((Algebra.ofId K B).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K B)
    (fun _ _ => Commute.all _ _)

def σ : TrivSqZeroExt K V ⊗[K] B →ₗ[K] B ⊗[K] V :=
  (TensorProduct.comm K V B).toLinearMap ∘ₗ TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id

def incl : B ⊗[K] V →ₗ[K] TrivSqZeroExt K V ⊗[K] B :=
  TensorProduct.map (TrivSqZeroExt.inrHom K V) LinearMap.id ∘ₗ (TensorProduct.comm K B V).toLinearMap

variable {K V B}

@[scoped simp] theorem red_tmul (a : TrivSqZeroExt K V) (b : B) : red K V B (a ⊗ₜ b) = a.fst • b := by
  simp [red, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
@[scoped simp] theorem σ_tmul (a : TrivSqZeroExt K V) (b : B) : σ K V B (a ⊗ₜ b) = b ⊗ₜ a.snd := by
  simp [σ]

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
@[scoped simp] theorem incl_tmul (b : B) (v : V) : incl K V B (b ⊗ₜ v) = (TrivSqZeroExt.inr v) ⊗ₜ b := by
  simp [incl]

theorem red_incl (w : B ⊗[K] V) : red K V B (incl K V B w) = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
theorem σ_incl (w : B ⊗[K] V) : σ K V B (incl K V B w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem red_includeRight (b : B) :
    red K V B (Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V) b) = b := by
  simp [Algebra.TensorProduct.includeRight_apply]

theorem σ_includeRight (b : B) :
    σ K V B (Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V) b) = 0 := by
  simp [Algebra.TensorProduct.includeRight_apply]

omit [IsCentralScalar K V] in
theorem σ_one : σ K V B 1 = 0 := by
  rw [Algebra.TensorProduct.one_def, σ_tmul, TrivSqZeroExt.snd_one, TensorProduct.tmul_zero]

theorem includeRight_red_add_incl_σ (z : TrivSqZeroExt K V ⊗[K] B) :
    Algebra.TensorProduct.includeRight (red K V B z) + incl K V B (σ K V B z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      rw [red_tmul, σ_tmul, incl_tmul, map_smul, Algebra.TensorProduct.includeRight_apply,
        TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
      congr 1
      rw [TrivSqZeroExt.ext_iff]
      simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl]
  | add x y hx hy =>
      conv_rhs => rw [← hx, ← hy]
      simp only [map_add]
      abel

theorem eq_one_add_incl_of_red_eq_one {z : TrivSqZeroExt K V ⊗[K] B} (hz : red K V B z = 1) :
    z = 1 + incl K V B (σ K V B z) := by
  conv_lhs => rw [← includeRight_red_add_incl_σ z, hz, map_one]

theorem incl_mul_incl (w w' : B ⊗[K] V) : incl K V B w * incl K V B w' = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
      induction w' using TensorProduct.induction_on with
      | zero => simp
      | tmul b' v' =>
          rw [incl_tmul, incl_tmul, Algebra.TensorProduct.tmul_mul_tmul, TrivSqZeroExt.inr_mul_inr,
            TensorProduct.zero_tmul]
      | add x y hx hy => rw [map_add, mul_add, hx, hy, add_zero]
  | add x y hx hy => rw [map_add, add_mul, hx, hy, add_zero]

theorem includeRight_mul_incl (b : B) (w : B ⊗[K] V) :
    Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V) b * incl K V B w = incl K V B (b • w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b' v =>
      rw [Algebra.TensorProduct.includeRight_apply, incl_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        TensorProduct.smul_tmul', incl_tmul, smul_eq_mul]
  | add x y hx hy => rw [map_add, mul_add, hx, hy, smul_add, map_add]

def unitOf (w : B ⊗[K] V) : (TrivSqZeroExt K V ⊗[K] B)ˣ where
  val := 1 + incl K V B w
  inv := 1 - incl K V B w
  val_inv := by rw [add_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, incl_mul_incl]; abel
  inv_val := by rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, incl_mul_incl]; abel

@[scoped simp] theorem unitOf_val (w : B ⊗[K] V) : (unitOf w : TrivSqZeroExt K V ⊗[K] B) = 1 + incl K V B w := rfl
@[scoped simp] theorem unitOf_inv_val (w : B ⊗[K] V) : (↑(unitOf w)⁻¹ : TrivSqZeroExt K V ⊗[K] B) = 1 - incl K V B w :=
  rfl

theorem one_add_incl_mul (w w' : B ⊗[K] V) :
    (1 + incl K V B w) * (1 + incl K V B w') = 1 + incl K V B (w + w') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, incl_mul_incl, map_add]; abel

theorem red_unitOf (w : B ⊗[K] V) : red K V B ((unitOf w : (TrivSqZeroExt K V ⊗[K] B)ˣ) : TrivSqZeroExt K V ⊗[K] B) = 1 := by
  rw [unitOf_val, map_add, map_one, red_incl, add_zero]

theorem σ_unitOf (w : B ⊗[K] V) : σ K V B ((unitOf w : (TrivSqZeroExt K V ⊗[K] B)ˣ) : TrivSqZeroExt K V ⊗[K] B) = w := by
  rw [unitOf_val, map_add, σ_one, σ_incl, zero_add]

theorem unit_eq (a : (TrivSqZeroExt K V ⊗[K] B)ˣ) :
    (a : TrivSqZeroExt K V ⊗[K] B) =
      Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V)
          ((Units.map (red K V B : TrivSqZeroExt K V ⊗[K] B →* B) a : Bˣ) : B) *
        (1 + incl K V B (σ K V B ((a : TrivSqZeroExt K V ⊗[K] B) * Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V)
          ((↑(Units.map (red K V B : TrivSqZeroExt K V ⊗[K] B →* B) a)⁻¹ : Bˣ) : B)))) := by
  set u : Bˣ := Units.map (red K V B : TrivSqZeroExt K V ⊗[K] B →* B) a with hu
  set b : TrivSqZeroExt K V ⊗[K] B := (a : TrivSqZeroExt K V ⊗[K] B) * Algebra.TensorProduct.includeRight ((↑u⁻¹ : Bˣ) : B) with hb
  have hred : red K V B b = 1 := by
    rw [hb, map_mul, red_includeRight]
    exact u.mul_inv
  have hb1 : b = 1 + incl K V B (σ K V B b) := eq_one_add_incl_of_red_eq_one hred
  rw [← hb1, hb, mul_left_comm, ← map_mul, Units.mul_inv, map_one, mul_one]

theorem unit_inv_eq (a : (TrivSqZeroExt K V ⊗[K] B)ˣ) :
    (↑a⁻¹ : TrivSqZeroExt K V ⊗[K] B) =
      Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V)
          ((↑(Units.map (red K V B : TrivSqZeroExt K V ⊗[K] B →* B) a)⁻¹ : Bˣ) : B) *
        (1 - incl K V B (σ K V B ((a : TrivSqZeroExt K V ⊗[K] B) * Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V)
          ((↑(Units.map (red K V B : TrivSqZeroExt K V ⊗[K] B →* B) a)⁻¹ : Bˣ) : B)))) := by
  have ha := unit_eq a
  set u : Bˣ := Units.map (red K V B : TrivSqZeroExt K V ⊗[K] B →* B) a
  set β := σ K V B ((a : TrivSqZeroExt K V ⊗[K] B) * Algebra.TensorProduct.includeRight ((↑u⁻¹ : Bˣ) : B))
  apply Units.inv_eq_of_mul_eq_one_right
  rw [ha]
  calc Algebra.TensorProduct.includeRight (u : B) * (1 + incl K V B β) *
        (Algebra.TensorProduct.includeRight ((↑u⁻¹ : Bˣ) : B) * (1 - incl K V B β))
      = (Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V) (u : B) *
          Algebra.TensorProduct.includeRight ((↑u⁻¹ : Bˣ) : B)) * ((1 + incl K V B β) * (1 - incl K V B β)) := by ring
    _ = 1 := by
        rw [← map_mul, Units.mul_inv, map_one, one_mul, sub_eq_add_neg, ← map_neg, one_add_incl_mul,
          add_neg_cancel, map_zero, add_zero]

variable {C : Type u} [CommRing C] [Algebra K C] (ρ : B →ₐ[K] C)

theorem map_incl (w : B ⊗[K] V) :
    Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) ρ (incl K V B w) = incl K V C (ρ.toLinearMap.rTensor V w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem red_map (z : TrivSqZeroExt K V ⊗[K] B) :
    red K V C (Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) ρ z) = ρ (red K V B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem σ_map (z : TrivSqZeroExt K V ⊗[K] B) :
    σ K V C (Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) ρ z) = ρ.toLinearMap.rTensor V (σ K V B z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem map_includeRight (b : B) :
    Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) ρ (Algebra.TensorProduct.includeRight b) =
      Algebra.TensorProduct.includeRight (ρ b) := by
  simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

end Decomp

section Cech

variable (𝒰 : TwoChartCech.Cover.{u, u} K) (V)

theorem mkQ_ρ0 (b : 𝒰.A0) : (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ (𝒰.ρ0 b) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨((-b, 0) : 𝒰.A0 × 𝒰.A1), ?_⟩
  rw [TwoChartCech.Sections.cechDiff_apply]
  simp

theorem mkQ_ρ1 (b : 𝒰.A1) : (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ (𝒰.ρ1 b) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨((0, b) : 𝒰.A0 × 𝒰.A1), ?_⟩
  rw [TwoChartCech.Sections.cechDiff_apply]
  simp

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
theorem rTensor_mkQ_rTensor_ρ0 (β : 𝒰.A0 ⊗[K] V) :
    (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V (𝒰.ρ0.toLinearMap.rTensor V β) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have : (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ ∘ₗ 𝒰.ρ0.toLinearMap = 0 :=
    LinearMap.ext fun b => mkQ_ρ0 𝒰 b
  rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
theorem rTensor_mkQ_rTensor_ρ1 (β : 𝒰.A1 ⊗[K] V) :
    (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V (𝒰.ρ1.toLinearMap.rTensor V β) = 0 := by
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have : (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ ∘ₗ 𝒰.ρ1.toLinearMap = 0 :=
    LinearMap.ext fun b => mkQ_ρ1 𝒰 b
  rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in

theorem exists_of_rTensor_mkQ_eq_zero {y : 𝒰.A01 ⊗[K] V}
    (hy : (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V y = 0) :
    ∃ (β0 : 𝒰.A0 ⊗[K] V) (β1 : 𝒰.A1 ⊗[K] V),
      y = 𝒰.ρ1.toLinearMap.rTensor V β1 - 𝒰.ρ0.toLinearMap.rTensor V β0 := by
  have hker : y ∈ LinearMap.ker ((LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V) := hy
  rw [rTensor_mkQ] at hker
  obtain ⟨z, rfl⟩ := hker
  clear hy
  obtain ⟨x, rfl⟩ := LinearMap.rTensor_surjective V
    (g := 𝒰.structureSheaf.cechDiff.rangeRestrict) 𝒰.structureSheaf.cechDiff.surjective_rangeRestrict z
  refine ⟨(TensorProduct.prodLeft K K 𝒰.A0 𝒰.A1 V x).1, (TensorProduct.prodLeft K K 𝒰.A0 𝒰.A1 V x).2, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.subtype_comp_codRestrict]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p v =>
      obtain ⟨p0, p1⟩ := p
      rw [LinearMap.rTensor_tmul, TensorProduct.prodLeft_tmul, TwoChartCech.Sections.cechDiff_apply,
        TwoChartCech.Cover.lineBundle_r0_apply, TwoChartCech.Cover.lineBundle_r1_apply, Units.val_one, one_mul,
        TensorProduct.sub_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
      rfl
  | add x x' hx hx' =>
      simp only [map_add, Prod.fst_add, Prod.snd_add]
      rw [hx, hx']
      abel

end Cech

end

end P2mTJ2a
p2m_reactivate "P2MW.S_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists.P2mTJ2a"

open P2mTJ2a in

theorem solution
    {K : Type u} [Field K] (𝒰 : TwoChartCech.Cover.{u, u} K)
    (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] :
    (∀ t t' : (TrivSqZeroExt K V ⊗[K] 𝒰.A01)ˣ,
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 →
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 →
      ((∃ (a0 : (TrivSqZeroExt K V ⊗[K] 𝒰.A0)ˣ) (a1 : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ),
          (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01) =
            Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) 𝒰.ρ0 (a0 : TrivSqZeroExt K V ⊗[K] 𝒰.A0) *
              (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) *
            Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) 𝒰.ρ1
              ((↑a1⁻¹ : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ) : TrivSqZeroExt K V ⊗[K] 𝒰.A1)) ↔
        (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
            ((TensorProduct.comm K V 𝒰.A01).toLinearMap
              (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01))) =
          (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
            ((TensorProduct.comm K V 𝒰.A01).toLinearMap
              (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01))))) ∧
    (∀ y : 𝒰.structureSheaf.H1 ⊗[K] V, ∃ t : (TrivSqZeroExt K V ⊗[K] 𝒰.A01)ˣ,
      Algebra.TensorProduct.lift ((Algebra.ofId K 𝒰.A01).comp (TrivSqZeroExt.fstHom K K V)) (AlgHom.id K 𝒰.A01)
          (fun _ _ => Commute.all _ _) (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 ∧
      (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V
          ((TensorProduct.comm K V 𝒰.A01).toLinearMap
            (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01))) = y) := by

  change (∀ t t' : (TrivSqZeroExt K V ⊗[K] 𝒰.A01)ˣ, red K V 𝒰.A01 t = 1 → red K V 𝒰.A01 t' = 1 →
      ((∃ (a0 : (TrivSqZeroExt K V ⊗[K] 𝒰.A0)ˣ) (a1 : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ),
          (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01) =
            Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) 𝒰.ρ0 (a0 : TrivSqZeroExt K V ⊗[K] 𝒰.A0) *
              (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) *
            Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) 𝒰.ρ1
              ((↑a1⁻¹ : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ) : TrivSqZeroExt K V ⊗[K] 𝒰.A1)) ↔
        (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V (σ K V 𝒰.A01 t) =
          (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V (σ K V 𝒰.A01 t'))) ∧
    (∀ y : 𝒰.structureSheaf.H1 ⊗[K] V, ∃ t : (TrivSqZeroExt K V ⊗[K] 𝒰.A01)ˣ,
      red K V 𝒰.A01 t = 1 ∧ (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V (σ K V 𝒰.A01 t) = y)
  refine ⟨fun t t' ht ht' => ⟨?_, ?_⟩, fun y => ?_⟩
  ·
    rintro ⟨a0, a1, h⟩
    set u0 : 𝒰.A0ˣ := Units.map (red K V 𝒰.A0 : TrivSqZeroExt K V ⊗[K] 𝒰.A0 →* 𝒰.A0) a0 with hu0
    set u1 : 𝒰.A1ˣ := Units.map (red K V 𝒰.A1 : TrivSqZeroExt K V ⊗[K] 𝒰.A1 →* 𝒰.A1) a1 with hu1
    set β0 := σ K V 𝒰.A0 ((a0 : TrivSqZeroExt K V ⊗[K] 𝒰.A0) * Algebra.TensorProduct.includeRight ((↑u0⁻¹ : 𝒰.A0ˣ) : 𝒰.A0)) with hβ0
    set β1 := σ K V 𝒰.A1 ((a1 : TrivSqZeroExt K V ⊗[K] 𝒰.A1) * Algebra.TensorProduct.includeRight ((↑u1⁻¹ : 𝒰.A1ˣ) : 𝒰.A1)) with hβ1
    have ha0 := unit_eq (V := V) a0
    have ha1 := unit_inv_eq (V := V) a1
    rw [← hu0, ← hβ0] at ha0
    rw [← hu1, ← hβ1] at ha1

    have hg : 𝒰.ρ0 (u0 : 𝒰.A0) = 𝒰.ρ1 (u1 : 𝒰.A1) := by
      have hred := congrArg (red K V 𝒰.A01) h
      rw [ht', map_mul, map_mul, ht, mul_one, red_map, red_map] at hred
      have e0 : red K V 𝒰.A0 (a0 : TrivSqZeroExt K V ⊗[K] 𝒰.A0) = (u0 : 𝒰.A0) := by rw [hu0]; rfl
      have e1 : red K V 𝒰.A1 ((↑a1⁻¹ : (TrivSqZeroExt K V ⊗[K] 𝒰.A1)ˣ) : TrivSqZeroExt K V ⊗[K] 𝒰.A1) =
          ((↑u1⁻¹ : 𝒰.A1ˣ) : 𝒰.A1) := by rw [hu1]; rfl
      rw [e0, e1] at hred

      have := congrArg (· * 𝒰.ρ1 (u1 : 𝒰.A1)) hred
      simp only [one_mul, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one] at this
      exact this.symm

    set w := σ K V 𝒰.A01 (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) with hw
    have ht1 : (t : TrivSqZeroExt K V ⊗[K] 𝒰.A01) = 1 + incl K V 𝒰.A01 w := eq_one_add_incl_of_red_eq_one ht
    have key : (t' : TrivSqZeroExt K V ⊗[K] 𝒰.A01) =
        1 + incl K V 𝒰.A01 (w + 𝒰.ρ0.toLinearMap.rTensor V β0 - 𝒰.ρ1.toLinearMap.rTensor V β1) := by
      rw [h, ha0, ha1, map_mul, map_mul, map_includeRight, map_includeRight, map_add, map_sub, map_one, map_one,
        map_incl, map_incl, ht1]
      set g := 𝒰.ρ0 (u0 : 𝒰.A0)
      have hg' : 𝒰.ρ1 ((↑u1⁻¹ : 𝒰.A1ˣ) : 𝒰.A1) * g = 1 := by
        rw [hg, ← map_mul, Units.inv_mul, map_one]
      calc Algebra.TensorProduct.includeRight g * (1 + incl K V 𝒰.A01 (𝒰.ρ0.toLinearMap.rTensor V β0)) *
            (1 + incl K V 𝒰.A01 w) *
            (Algebra.TensorProduct.includeRight (𝒰.ρ1 ((↑u1⁻¹ : 𝒰.A1ˣ) : 𝒰.A1)) *
              (1 - incl K V 𝒰.A01 (𝒰.ρ1.toLinearMap.rTensor V β1)))
          = (Algebra.TensorProduct.includeRight (R := K) (A := TrivSqZeroExt K V) (𝒰.ρ1 ((↑u1⁻¹ : 𝒰.A1ˣ) : 𝒰.A1)) *
              Algebra.TensorProduct.includeRight g) *
            ((1 + incl K V 𝒰.A01 (𝒰.ρ0.toLinearMap.rTensor V β0)) * (1 + incl K V 𝒰.A01 w) *
              (1 - incl K V 𝒰.A01 (𝒰.ρ1.toLinearMap.rTensor V β1))) := by ring
        _ = 1 + incl K V 𝒰.A01 (w + 𝒰.ρ0.toLinearMap.rTensor V β0 - 𝒰.ρ1.toLinearMap.rTensor V β1) := by
          rw [← map_mul, hg', map_one, one_mul, sub_eq_add_neg, ← map_neg, one_add_incl_mul, one_add_incl_mul]
          congr 2
          abel
    have hσ' : σ K V 𝒰.A01 t' = w + 𝒰.ρ0.toLinearMap.rTensor V β0 - 𝒰.ρ1.toLinearMap.rTensor V β1 := by
      rw [key, map_add, σ_one, σ_incl, zero_add]
    rw [hσ', map_sub, map_add, rTensor_mkQ_rTensor_ρ0, rTensor_mkQ_rTensor_ρ1, add_zero, sub_zero]
  ·
    intro hcls
    have hdiff : (LinearMap.range 𝒰.structureSheaf.cechDiff).mkQ.rTensor V (σ K V 𝒰.A01 t' - σ K V 𝒰.A01 t) = 0 := by
      rw [map_sub, hcls, sub_self]
    obtain ⟨β0, β1, hβ⟩ := exists_of_rTensor_mkQ_eq_zero V 𝒰 hdiff
    refine ⟨unitOf (-β0), unitOf (-β1), ?_⟩
    rw [unitOf_val, unitOf_inv_val, map_add, map_sub, map_one, map_one, map_incl, map_incl,
      eq_one_add_incl_of_red_eq_one ht, eq_one_add_incl_of_red_eq_one ht', sub_eq_add_neg, ← map_neg,
      one_add_incl_mul, one_add_incl_mul, map_neg, map_neg, neg_neg]
    congr 2
    rw [sub_eq_iff_eq_add] at hβ
    rw [hβ]
    abel
  ·
    obtain ⟨w, rfl⟩ := LinearMap.rTensor_surjective V (Submodule.mkQ_surjective _) y
    exact ⟨unitOf w, red_unitOf w, by rw [σ_unitOf]⟩

end S_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists
end P2MW
export P2MW.S_TwoChartCech_Cover_squareZeroUnit_cohomologous_iff_and_exists (solution)
