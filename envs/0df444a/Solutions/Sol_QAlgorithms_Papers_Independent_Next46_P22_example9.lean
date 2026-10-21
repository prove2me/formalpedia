-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P22.example9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:16:05.422093+00:00
-- url     : https://prove2.me/submissions/b0448a72-e82d-4430-9fa2-7cc6d85bb00c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

open QAlgorithms.Papers.Independent.Next46.P22
open scoped TensorProduct

namespace G61P

variable {F A B X : Type*} [Field F]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup X] [Module F X]

theorem ts_lift (z : A ⊗[F] B) (Φ : A →ₗ[F] B →ₗ[F] X) :
    tensorSum z (fun a b => Φ a b) = TensorProduct.lift Φ z := by
  unfold tensorSum
  conv_rhs => rw [(TensorProduct.exists_finset z).choose_spec]
  simp [map_sum]

theorem ts_eq (z : A ⊗[F] B) (f : A → B → X) (Φ : A →ₗ[F] B →ₗ[F] X)
    (h : ∀ a b, f a b = Φ a b) : tensorSum z f = TensorProduct.lift Φ z := by
  have : f = fun a b => Φ a b := funext fun a => funext fun b => h a b
  subst this; exact ts_lift z Φ

theorem ts_mem (z : A ⊗[F] B) (f : A → B → X) (U : Submodule F X) (h : ∀ a b, f a b ∈ U) :
    tensorSum z f ∈ U := by
  unfold tensorSum; exact Submodule.sum_mem _ (fun p _ => h _ _)

theorem ts_bil {C D : Type*} [AddCommGroup C] [Module F C] [AddCommGroup D] [Module F D]
    (z : A ⊗[F] B) (G : A →ₗ[F] B →ₗ[F] X) (f : A → B → X) (hf : ∀ a b, f a b = G a b)
    (z' : C ⊗[F] D) (u : C → D → A) (w : C → D → B)
    (hz : z = tensorSum z' (fun x y => u x y ⊗ₜ[F] w x y)) :
    tensorSum z f = tensorSum z' (fun x y => G (u x y) (w x y)) := by
  rw [ts_eq z f G hf, hz]
  unfold tensorSum
  rw [map_sum]
  simp

theorem map_ts {Y : Type*} [AddCommGroup Y] [Module F Y] (T : X →ₗ[F] Y) (z : A ⊗[F] B) (f : A → B → X) :
    T (tensorSum z f) = tensorSum z (fun a b => T (f a b)) := by
  unfold tensorSum; rw [map_sum]

variable {H L : Type*} [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- bilinear map (x, w) ↦ ⁅α x u, α w v⁆ -/
def lam (alpha : H →ₐ[F] Module.End F L) (u v : L) : H →ₗ[F] H →ₗ[F] L :=
  LinearMap.mk₂ F (fun x w => ⁅alpha x u, alpha w v⁆)
    (by intro a b c; simp [add_lie]) (by intro c a b; simp [smul_lie])
    (by intro a b c; simp [lie_add]) (by intro c a b; simp [lie_smul])

theorem key (alpha : H →ₐ[F] Module.End F L) (ha : ModuleLie alpha) (h : H) (u v : L) :
    ⁅alpha h u, v⁆ = tensorSum (Coalgebra.comul (R := F) h)
      (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆) := by
  -- Φ h1 h2 = α h1 ⁅u, α (S h2) v⁆
  let Φ : H →ₗ[F] H →ₗ[F] L := LinearMap.mk₂ F
    (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆)
    (by intro a b c; simp) (by intro c a b; simp)
    (by intro a b c; simp) (by intro c a b; simp)
  rw [ts_eq _ (fun h1 h2 => alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆) Φ (fun _ _ => rfl)]
  -- Θ' : H ⊗ (H ⊗ H) → L
  let Θ' : H ⊗[F] (H ⊗[F] H) →ₗ[F] L :=
    TensorProduct.lift (lam alpha u v) ∘ₗ
      (LinearMap.lTensor H (LinearMap.mul' F H ∘ₗ (HopfAlgebra.antipode F (A := H)).lTensor H))
  have hΦ : TensorProduct.lift Φ = Θ' ∘ₗ (TensorProduct.assoc F H H H).toLinearMap ∘ₗ
      (Coalgebra.comul (R := F) (A := H)).rTensor H := by
    apply TensorProduct.ext'
    intro h1 h2
    simp only [TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
    show alpha h1 ⁅u, alpha (HopfAlgebra.antipode F h2) v⁆ = _
    rw [ha h1 u _]
    rw [ts_eq _ (fun x y => ⁅alpha x u, alpha y (alpha (HopfAlgebra.antipode F h2) v)⁆) (lam alpha u (alpha (HopfAlgebra.antipode F h2) v)) (fun _ _ => rfl)]
    induction (Coalgebra.comul (R := F) h1) using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp [Θ', lam, TensorProduct.assoc_tmul, Module.End.mul_apply]
    | add p q hp hq => rw [map_add, hp, hq, TensorProduct.add_tmul, map_add, map_add]
  rw [hΦ]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [Coalgebra.coassoc_apply]
  have hΘ : Θ' ∘ₗ (Coalgebra.comul (R := F) (A := H)).lTensor H =
      TensorProduct.lift (lam alpha u v) ∘ₗ
        LinearMap.lTensor H ((Algebra.linearMap F H) ∘ₗ Coalgebra.counit) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul]
    simp only [Θ', LinearMap.comp_assoc, ← LinearMap.lTensor_comp]
  have := congrArg (fun f => f (Coalgebra.comul (R := F) h)) hΘ
  simp only [LinearMap.coe_comp, Function.comp_apply] at this
  rw [this]
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp [lam]

theorem ts_lam (alpha : H →ₐ[F] Module.End F L) (u v : L) (z : H ⊗[F] H) :
    tensorSum z (fun h1 h2 => ⁅alpha h1 u, alpha h2 v⁆) = TensorProduct.lift (lam alpha u v) z :=
  ts_eq z (fun h1 h2 => ⁅alpha h1 u, alpha h2 v⁆) (lam alpha u v) (fun _ _ => rfl)

end G61P

open QAlgorithms.Papers.Independent.Next46.P22
open scoped TensorProduct

section g61aU
attribute [local instance 100] LieRing.ofAssociativeRing

variable {F K : Type*} [Field F] [LieRing K] [LieAlgebra F K]

local notation "𝕌" => UniversalEnvelopingAlgebra F K
local notation "ιU" => UniversalEnvelopingAlgebra.ι F

theorem g61a_ind (P : 𝕌 → Prop) (hι : ∀ a : K, P (ιU a)) (halg : ∀ c : F, P (algebraMap F 𝕌 c))
    (hadd : ∀ u v, P u → P v → P (u + v)) (hmul : ∀ u v, P u → P v → P (u * v)) : ∀ u, P u := by
  intro u
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := F) _ u
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact halg r
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

noncomputable def g61a_cδ : K →ₗ⁅F⁆ 𝕌 ⊗[F] 𝕌 :=
  { toFun := fun a => ιU a ⊗ₜ[F] (1 : 𝕌) + (1 : 𝕌) ⊗ₜ[F] ιU a
    map_add' := fun x y => by
      simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]; abel
    map_smul' := fun c x => by
      simp only [map_smul, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add,
        RingHom.id_apply]
    map_lie' := fun {x y} => by
      simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket,
        Algebra.TensorProduct.tmul_mul_tmul, mul_add, add_mul, one_mul, mul_one,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel }

noncomputable def g61a_cS : K →ₗ⁅F⁆ 𝕌ᵐᵒᵖ :=
  { toFun := fun a => MulOpposite.op (-(ιU a))
    map_add' := fun x y => by simp only [map_add, neg_add, MulOpposite.op_add]
    map_smul' := fun c x => by simp only [map_smul, smul_neg, MulOpposite.op_neg,
      MulOpposite.op_smul, RingHom.id_apply]
    map_lie' := fun {x y} => by
      apply MulOpposite.unop_injective
      simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket, MulOpposite.unop_sub,
        MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_neg]
      noncomm_ring }

noncomputable abbrev g61a_δ : 𝕌 →ₐ[F] 𝕌 ⊗[F] 𝕌 := UniversalEnvelopingAlgebra.lift F g61a_cδ
noncomputable abbrev g61a_ε : 𝕌 →ₐ[F] F := UniversalEnvelopingAlgebra.lift F (0 : K →ₗ⁅F⁆ F)
noncomputable abbrev g61a_Sa : 𝕌 →ₐ[F] 𝕌ᵐᵒᵖ := UniversalEnvelopingAlgebra.lift F g61a_cS
noncomputable def g61a_S : 𝕌 →ₗ[F] 𝕌 :=
  (MulOpposite.opLinearEquiv F).symm.toLinearMap ∘ₗ (g61a_Sa (F := F) (K := K)).toLinearMap

theorem g61a_δι (a : K) : g61a_δ (ιU a) = ιU a ⊗ₜ[F] (1 : 𝕌) + (1 : 𝕌) ⊗ₜ[F] ιU a :=
  UniversalEnvelopingAlgebra.lift_ι_apply F _ a
theorem g61a_ει (a : K) : g61a_ε (ιU a) = 0 :=
  UniversalEnvelopingAlgebra.lift_ι_apply F _ a
theorem g61a_Sι (a : K) : g61a_S (ιU a) = -ιU a := by
  show MulOpposite.unop (g61a_Sa (ιU a)) = _
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]; rfl
theorem g61a_S1 : g61a_S (1 : 𝕌) = 1 := by
  show MulOpposite.unop (g61a_Sa 1) = _
  rw [map_one]; rfl
theorem g61a_Smul (u v : 𝕌) : g61a_S (u * v) = g61a_S v * g61a_S u := by
  show MulOpposite.unop (g61a_Sa (u * v)) = MulOpposite.unop (g61a_Sa v) * MulOpposite.unop (g61a_Sa u)
  rw [map_mul, MulOpposite.unop_mul]

theorem g61a_ext {A : Type*} [Ring A] [Algebra F A] (f g : 𝕌 →ₐ[F] A)
    (h : ∀ a, f (ιU a) = g (ιU a)) : f = g := by
  refine AlgHom.ext (g61a_ind (fun u => f u = g u) h (fun c => by simp)
    (fun u v hu hv => by simp [hu, hv]) (fun u v hu hv => by simp [hu, hv]))

noncomputable def g61a_bialg : Bialgebra F 𝕌 :=
  Bialgebra.ofAlgHom g61a_δ g61a_ε
    (by
      apply UniversalEnvelopingAlgebra.hom_ext
      apply LieHom.ext; intro a
      simp only [LieHom.coe_comp, Function.comp_apply, AlgHom.coe_toLieHom, AlgHom.coe_comp,
        AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom, g61a_δι, map_add,
        Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one,
        Algebra.TensorProduct.assoc_tmul, TensorProduct.add_tmul, TensorProduct.tmul_add,
        Algebra.TensorProduct.one_def]
      abel)
    (by
      apply g61a_ext; intro a
      simp only [AlgHom.comp_apply, g61a_δι, map_add, Algebra.TensorProduct.map_tmul, g61a_ει,
        map_one, AlgHom.id_apply]
      simp)
    (by
      apply g61a_ext; intro a
      simp only [AlgHom.comp_apply, g61a_δι, map_add, Algebra.TensorProduct.map_tmul, g61a_ει,
        map_one, AlgHom.id_apply]
      simp)

noncomputable def g61a_mS : 𝕌 ⊗[F] 𝕌 →ₗ[F] 𝕌 := LinearMap.mul' F 𝕌 ∘ₗ g61a_S.rTensor 𝕌
noncomputable def g61a_mS' : 𝕌 ⊗[F] 𝕌 →ₗ[F] 𝕌 := LinearMap.mul' F 𝕌 ∘ₗ g61a_S.lTensor 𝕌

theorem g61a_mS_mul (x : 𝕌 ⊗[F] 𝕌) (c d : 𝕌) :
    g61a_mS (x * (c ⊗ₜ[F] d)) = g61a_S c * g61a_mS x * d := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [g61a_mS, LinearMap.comp_apply, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul,
      LinearMap.mul'_apply, g61a_Smul, mul_assoc]
  | add p q hp hq => rw [add_mul, map_add, hp, hq, map_add, mul_add, add_mul]

theorem g61a_mS'_mul (y : 𝕌 ⊗[F] 𝕌) (a b : 𝕌) :
    g61a_mS' ((a ⊗ₜ[F] b) * y) = a * g61a_mS' y * g61a_S b := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c d =>
    simp only [g61a_mS', LinearMap.comp_apply, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul,
      LinearMap.mul'_apply, g61a_Smul, mul_assoc]
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add, add_mul]

theorem g61a_mS_scal (x : 𝕌 ⊗[F] 𝕌) (r : F) (hx : g61a_mS x = algebraMap F 𝕌 r) (y : 𝕌 ⊗[F] 𝕌) :
    g61a_mS (x * y) = r • g61a_mS y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c d =>
    rw [g61a_mS_mul, hx, Algebra.algebraMap_eq_smul_one]
    simp [g61a_mS]
  | add p q hp hq => rw [mul_add, map_add, map_add, hp, hq, smul_add]

theorem g61a_mS'_scal (y : 𝕌 ⊗[F] 𝕌) (r : F) (hy : g61a_mS' y = algebraMap F 𝕌 r) (x : 𝕌 ⊗[F] 𝕌) :
    g61a_mS' (x * y) = r • g61a_mS' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [g61a_mS'_mul, hy, Algebra.algebraMap_eq_smul_one]
    simp [g61a_mS']
  | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, smul_add]

theorem g61a_hopf_r (u : 𝕌) : g61a_mS (g61a_δ u) = algebraMap F 𝕌 (g61a_ε u) := by
  induction u using g61a_ind with
  | hι a =>
    rw [g61a_δι, g61a_ει, map_add, map_zero]
    simp only [g61a_mS, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      LinearMap.mul'_apply, g61a_Sι, g61a_S1, mul_one, one_mul]
    abel
  | halg c =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one c]
    simp [g61a_mS, g61a_S1, Algebra.TensorProduct.one_def, Algebra.algebraMap_eq_smul_one]
  | hadd u v hu hv => simp only [map_add, hu, hv] at *
  | hmul u v hu hv =>
    rw [map_mul, g61a_mS_scal _ _ hu, hv, map_mul, map_mul, Algebra.smul_def]

theorem g61a_hopf_l (u : 𝕌) : g61a_mS' (g61a_δ u) = algebraMap F 𝕌 (g61a_ε u) := by
  induction u using g61a_ind with
  | hι a =>
    rw [g61a_δι, g61a_ει, map_add, map_zero]
    simp only [g61a_mS', LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      LinearMap.mul'_apply, g61a_Sι, g61a_S1, mul_one, one_mul]
    abel
  | halg c =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one c]
    simp [g61a_mS', g61a_S1, Algebra.TensorProduct.one_def, Algebra.algebraMap_eq_smul_one]
  | hadd u v hu hv => simp only [map_add, hu, hv] at *
  | hmul u v hu hv =>
    rw [map_mul, g61a_mS'_scal _ _ hv, hu, map_mul, Algebra.smul_def, ← map_mul, mul_comm]

@[instance_reducible]
noncomputable def g61a_hopf : HopfAlgebra F 𝕌 :=
  letI := g61a_bialg (F := F) (K := K)
  { antipode := g61a_S
    mul_antipode_rTensor_comul := LinearMap.ext fun u => g61a_hopf_r u
    mul_antipode_lTensor_comul := LinearMap.ext fun u => g61a_hopf_l u }

variable {L : Type*} [LieRing L] [LieAlgebra F L]

noncomputable def g61a_alpha (delta : K →ₗ⁅F⁆ LieDerivation F L L) : 𝕌 →ₐ[F] Module.End F L :=
  UniversalEnvelopingAlgebra.lift F ((LieDerivation.toLinearMapLieHom F L).comp delta)

theorem g61a_alphaι (delta : K →ₗ⁅F⁆ LieDerivation F L L) (a : K) (v : L) :
    g61a_alpha delta (ιU a) v = delta a v := by
  unfold g61a_alpha
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]; rfl

noncomputable def g61a_Λ (alpha : 𝕌 →ₐ[F] Module.End F L) (u v : L) : 𝕌 →ₗ[F] 𝕌 →ₗ[F] L :=
  LinearMap.mk₂ F (fun x w => ⁅alpha x u, alpha w v⁆)
    (by intro a b c; simp [add_lie]) (by intro c a b; simp [smul_lie])
    (by intro a b c; simp [lie_add]) (by intro c a b; simp [lie_smul])

theorem g61a_ML (delta : K →ₗ⁅F⁆ LieDerivation F L L) (h : 𝕌) :
    ∀ u v : L, g61a_alpha delta h ⁅u, v⁆ =
      TensorProduct.lift (g61a_Λ (g61a_alpha delta) u v) (g61a_δ h) := by
  set α := g61a_alpha delta
  induction h using g61a_ind with
  | hι a =>
    intro u v
    rw [g61a_δι, map_add, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
    simp only [g61a_Λ, LinearMap.mk₂_apply, map_one, Module.End.one_apply]
    rw [g61a_alphaι, g61a_alphaι, g61a_alphaι, LieDerivation.apply_lie_eq_add, add_comm]
  | halg c =>
    intro u v
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
      TensorProduct.lift.tmul]
    simp [g61a_Λ, Algebra.algebraMap_eq_smul_one]
  | hadd x y hx hy =>
    intro u v
    rw [map_add, LinearMap.add_apply, hx, hy, map_add, map_add]
  | hmul x y hx hy =>
    intro u v
    rw [map_mul, Module.End.mul_apply, hy, map_mul]
    induction (g61a_δ y) using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, map_add]
    | tmul c d =>
      rw [TensorProduct.lift.tmul]
      simp only [g61a_Λ, LinearMap.mk₂_apply]
      rw [hx]
      induction (g61a_δ x) using TensorProduct.induction_on with
      | zero => simp
      | add p q hp hq => rw [map_add, hp, hq, add_mul, map_add]
      | tmul p q =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        simp only [g61a_Λ, LinearMap.mk₂_apply, map_mul, Module.End.mul_apply]

end g61aU

theorem solution {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    {K : Type*} [LieRing K] [LieAlgebra F K]
    (delta : K →ₗ⁅F⁆ LieDerivation F L L) :
    ∃ hopf : HopfAlgebra F (UniversalEnvelopingAlgebra F K),
      hopf.toBialgebra.toAlgebra = (inferInstance : Algebra F (UniversalEnvelopingAlgebra F K)) ∧
      (letI : Algebra F (UniversalEnvelopingAlgebra F K) := hopf.toBialgebra.toAlgebra
       letI : Module F (UniversalEnvelopingAlgebra F K) := Algebra.toModule
       letI : HopfAlgebra F (UniversalEnvelopingAlgebra F K) := hopf
       (∀ a : K,
        Coalgebra.comul (R := F) (UniversalEnvelopingAlgebra.ι F a) =
          UniversalEnvelopingAlgebra.ι F a ⊗ₜ[F] (1 : UniversalEnvelopingAlgebra F K) +
          (1 : UniversalEnvelopingAlgebra F K) ⊗ₜ[F] UniversalEnvelopingAlgebra.ι F a ∧
        Coalgebra.counit (R := F) (UniversalEnvelopingAlgebra.ι F a) = 0 ∧
        HopfAlgebra.antipode F (UniversalEnvelopingAlgebra.ι F a) =
          -UniversalEnvelopingAlgebra.ι F a) ∧
       ∃ alpha : UniversalEnvelopingAlgebra F K →ₐ[F] Module.End F L,
        (∀ a v, alpha (UniversalEnvelopingAlgebra.ι F a) v = delta a v) ∧ ModuleLie alpha) := by
  refine ⟨g61a_hopf, rfl, fun a => ⟨g61a_δι a, g61a_ει a, g61a_Sι a⟩,
    g61a_alpha delta, g61a_alphaι delta, ?_⟩
  intro h u v
  show g61a_alpha delta h ⁅u, v⁆ = tensorSum (g61a_δ h)
    (fun h1 h2 => ⁅g61a_alpha delta h1 u, g61a_alpha delta h2 v⁆)
  rw [G61P.ts_eq _ (fun h1 h2 => ⁅g61a_alpha delta h1 u, g61a_alpha delta h2 v⁆)
    (g61a_Λ (g61a_alpha delta) u v) (fun _ _ => rfl)]
  exact g61a_ML delta h u v
