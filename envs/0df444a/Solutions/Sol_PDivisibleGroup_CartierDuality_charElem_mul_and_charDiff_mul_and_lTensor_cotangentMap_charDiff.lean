-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fea7e135-6281-5906-95d1-879f89165ac3

import Mathlib
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff

set_option autoImplicit false

open PDivisibleGroup Coalgebra WithConv
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct"

namespace PDivCharDiff

section Transpose

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Bialgebra R A]

theorem cd_add_apply (φ ψ : CartierDual R A) (a : A) : (φ + ψ) a = φ a + ψ a := rfl

theorem mul'_apply_apply (w : CartierDual R A ⊗[R] CartierDual R A) (a : A) :
    LinearMap.mul' R (CartierDual R A) w a =
      TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap w)
        (comul (R := R) a) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]; rfl
  | tmul φ ψ =>
      rw [LinearMap.mul'_apply, TensorProduct.map_tmul]
      exact CartierDual.mul_apply φ ψ a
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply]
      rw [cd_add_apply, hx, hy]

noncomputable def tr (f : A →ₗ[R] A) : CartierDual R A →ₗ[R] CartierDual R A :=
  (CartierDual.ofDual R A).toLinearMap ∘ₗ f.dualMap ∘ₗ (CartierDual.toDual R A).toLinearMap

@[scoped simp] theorem tr_apply (f : A →ₗ[R] A) (φ : CartierDual R A) (a : A) : tr f φ a = φ (f a) := rfl

theorem tr_id : tr (LinearMap.id : A →ₗ[R] A) = LinearMap.id := by
  apply LinearMap.ext; intro φ; apply CartierDual.ext; intro a; rfl

theorem dualDistrib_map_tr (f g : A →ₗ[R] A) (u : CartierDual R A ⊗[R] CartierDual R A)
    (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap
          (TensorProduct.map (tr f) (tr g) u)) z =
      TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap u)
        (TensorProduct.map f g z) := by
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul φ ψ =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

variable [Module.Finite R A] [Module.Free R A]

theorem comul_pairing' (φ : CartierDual R A) (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap
          (comul (R := R) φ)) z = φ (LinearMap.mul' R A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
      rw [LinearMap.mul'_apply]
      exact CartierDual.comul_pairing φ a b
  | add x y hx hy => simp only [map_add, hx, hy]

theorem convMul_tr_apply (f g : A →ₗ[R] A) (φ : CartierDual R A) (a : A) :
    (toConv (tr f) * toConv (tr g)).ofConv φ a = φ ((toConv f * toConv g).ofConv a) := by
  rw [LinearMap.convMul_apply, LinearMap.convMul_apply, ofConv_toConv, ofConv_toConv,
    ofConv_toConv, ofConv_toConv, mul'_apply_apply, dualDistrib_map_tr, comul_pairing']

theorem convPow_id_apply (n : ℕ) (φ : CartierDual R A) (a : A) :
    ((toConv (LinearMap.id : CartierDual R A →ₗ[R] CartierDual R A)) ^ n).ofConv φ a =
      φ (((toConv (LinearMap.id : A →ₗ[R] A)) ^ n).ofConv a) := by
  induction n generalizing φ a with
  | zero =>
      rw [pow_zero, pow_zero]
      change (algebraMap R (CartierDual R A) (counit (R := R) φ)) a =
        φ (algebraMap R A (counit (R := R) a))
      rw [CartierDual.algebraMap_apply, CartierDual.counit_apply, Algebra.algebraMap_eq_smul_one,
        map_smul, smul_eq_mul]
  | succ n ih =>
      have hT : ((toConv (LinearMap.id : CartierDual R A →ₗ[R] CartierDual R A)) ^ n).ofConv =
          tr (((toConv (LinearMap.id : A →ₗ[R] A)) ^ n).ofConv) := by
        apply LinearMap.ext; intro ψ; apply CartierDual.ext; intro b
        rw [tr_apply]
        exact ih ψ b
      rw [pow_succ, pow_succ]
      have key := convMul_tr_apply (((toConv (LinearMap.id : A →ₗ[R] A)) ^ n).ofConv)
        LinearMap.id φ a
      rw [tr_id, ← hT, toConv_ofConv, toConv_ofConv] at key
      exact key

theorem nsmulAlgHom_cartierDual_apply [Coalgebra.IsCocomm R A] (n : ℕ) (φ : CartierDual R A)
    (a : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R (CartierDual R A) n φ a =
      φ (PDivisibleGroup.Hopf.nsmulAlgHom R A n a) := by
  have h1 := congrArg (fun f => f φ a)
    (PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom R (CartierDual R A) n)
  have h2 := congrArg (fun f => f a) (PDivisibleGroup.Hopf.toLinearMap_nsmulAlgHom R A n)
  simp only [AlgHom.toLinearMap_apply] at h1 h2
  rw [h1, h2]
  exact convPow_id_apply n φ a

end Transpose

section Test

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]
variable {A : Type} [AddCommGroup A] [Module R A]

noncomputable def T (φ : Module.Dual R A) : S ⊗[R] A →ₗ[R] S :=
  (TensorProduct.rid R S).toLinearMap ∘ₗ φ.lTensor S

@[scoped simp] theorem T_tmul (φ : Module.Dual R A) (s : S) (a : A) : T S φ (s ⊗ₜ[R] a) = φ a • s := by
  simp [T]

theorem T_tmul' (φ : Module.Dual R A) (s : S) (a : A) : T S φ (s ⊗ₜ[R] a) = s * algebraMap R S (φ a) := by
  rw [T_tmul, Algebra.smul_def, mul_comm]

theorem T_sum_coord {ι : Type} [Fintype ι] (b : Module.Basis ι R A) (lam : Module.Dual R A →ₗ[R] S)
    (φ : Module.Dual R A) : T S φ (∑ i, lam (b.coord i) ⊗ₜ[R] b i) = lam φ := by
  rw [map_sum]
  simp_rw [T_tmul, ← map_smul lam]
  rw [← map_sum, Module.Basis.sum_dual_apply_smul_coord]

theorem eq_zero_of_forall_T_eq_zero {ι : Type} [Fintype ι] (b : Module.Basis ι R A) (x : S ⊗[R] A)
    (hx : ∀ φ : Module.Dual R A, T S φ x = 0) : x = 0 := by
  classical

  let bS : Module.Basis ι S (S ⊗[R] A) := Algebra.TensorProduct.basis S b

  have hcoord : ∀ (y : S ⊗[R] A) (j : ι), bS.repr y j = T S (b.coord j) y := by
    intro y j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
        rw [T_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def, mul_comm]
        rfl
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, map_add]
  refine bS.ext_elem fun j => ?_
  rw [hcoord, hx, map_zero, Finsupp.zero_apply]

theorem eq_of_forall_T_eq {ι : Type} [Fintype ι] (b : Module.Basis ι R A) {x y : S ⊗[R] A}
    (hxy : ∀ φ : Module.Dual R A, T S φ x = T S φ y) : x = y := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_T_eq_zero S b _ fun φ => by rw [map_sub, hxy φ, sub_self]

theorem T_lTensor {B : Type} [AddCommGroup B] [Module R B] (g : B →ₗ[R] A) (φ : Module.Dual R A)
    (x : S ⊗[R] B) : T S φ (g.lTensor S x) = T S (φ ∘ₗ g) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => rw [LinearMap.lTensor_tmul, T_tmul, T_tmul, LinearMap.comp_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end Test

section Char

variable {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (S : Type) [CommRing S] [Algebra R S]

noncomputable abbrev bas (G : PDivisibleGroup R p h) (v : ℕ) := Module.Free.chooseBasis R (G.level v)

noncomputable def lam (v : ℕ) (ψ : G'.Point S v) : Module.Dual R (G.level v) →ₗ[R] S :=
  (Point.toAlgHom ψ).toLinearMap ∘ₗ (D.toDualEquiv v).symm.toLinearMap

theorem lam_apply (v : ℕ) (ψ : G'.Point S v) (φ : Module.Dual R (G.level v)) :
    lam D S v ψ φ = Point.toAlgHom ψ ((D.toDualEquiv v).symm φ) := rfl

theorem charElem_eq (v : ℕ) (ψ : G'.Point S v) :
    D.charElem S v ψ = ∑ i, lam D S v ψ ((bas G v).coord i) ⊗ₜ[R] bas G v i := rfl

theorem T_charElem (v : ℕ) (ψ : G'.Point S v) (φ : Module.Dual R (G.level v)) :
    T S φ (D.charElem S v ψ) = Point.toAlgHom ψ ((D.toDualEquiv v).symm φ) := by
  rw [charElem_eq, T_sum_coord]
  rfl

theorem lift_charElem (v : ℕ) (f : G.Point S v) (ψ : G'.Point S v) :
    Algebra.TensorProduct.lift (AlgHom.id R S) (Point.toAlgHom f) (fun _ _ => .all _ _)
      (D.charElem S v ψ) = D.pair S v f ψ := by
  rw [D.charElem_def, map_sum, D.pair_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, mul_comm]

theorem charElem_one (v : ℕ) : D.charElem S v (1 : G'.Point S v) = 1 := by
  refine eq_of_forall_T_eq S (bas G v) fun φ => ?_
  rw [T_charElem, Point.one_apply, Algebra.TensorProduct.one_def, T_tmul', one_mul,
    CartierDuality.toDualEquiv_symm_apply, D.counit_eq_equiv_apply_one, BialgEquiv.apply_symm_apply]
  rfl

noncomputable def Lam (v : ℕ) (ψ ψ' : G'.Point S v) :
    CartierDual R (G.level v) ⊗[R] CartierDual R (G.level v) →ₗ[R] S :=
  LinearMap.mul' R S ∘ₗ TensorProduct.map
    ((Point.toAlgHom ψ).toLinearMap ∘ₗ ((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] _).toLinearMap)
    ((Point.toAlgHom ψ').toLinearMap ∘ₗ ((D.equiv v).symm : CartierDual R (G.level v) →ₐc[R] _).toLinearMap)

theorem Lam_tmul (v : ℕ) (ψ ψ' : G'.Point S v) (α β : CartierDual R (G.level v)) :
    Lam D S v ψ ψ' (α ⊗ₜ[R] β) =
      Point.toAlgHom ψ ((D.equiv v).symm α) * Point.toAlgHom ψ' ((D.equiv v).symm β) := by
  simp only [Lam, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

theorem sum_smul_lam (v : ℕ) (ψ : G'.Point S v) (α : CartierDual R (G.level v)) :
    ∑ i, α (bas G v i) • lam D S v ψ ((bas G v).coord i) = Point.toAlgHom ψ ((D.equiv v).symm α) := by
  have h1 : ∑ i, α (bas G v i) • lam D S v ψ ((bas G v).coord i) =
      lam D S v ψ (∑ i, (CartierDual.toDual R _ α) (bas G v i) • (bas G v).coord i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  rw [h1, Module.Basis.sum_dual_apply_smul_coord]
  rfl

theorem charElem_mul (v : ℕ) (ψ ψ' : G'.Point S v) :
    D.charElem S v (ψ * ψ') = D.charElem S v ψ * D.charElem S v ψ' := by
  classical
  refine eq_of_forall_T_eq S (bas G v) fun φ => ?_
  set φd : CartierDual R (G.level v) := CartierDual.ofDual R (G.level v) φ with hφd

  have hL : T S φ (D.charElem S v (ψ * ψ')) = Lam D S v ψ ψ' (comul (R := R) φd) := by
    let eS : CartierDual R (G.level v) →ₐc[R] G'.level v := (D.equiv v).symm
    rw [T_charElem, CartierDuality.toDualEquiv_symm_apply, ← hφd, Point.mul_apply,
      show (D.equiv v).symm φd = eS φd from rfl, ← CoalgHomClass.map_comp_comul_apply eS φd]

    induction (comul (R := R) φd) using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul α β =>
        rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Lam_tmul]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]

  have hR : T S φ (D.charElem S v ψ * D.charElem S v ψ') = Lam D S v ψ ψ' (comul (R := R) φd) := by
    have hkey : ∀ w : CartierDual R (G.level v) ⊗[R] CartierDual R (G.level v),
        (∑ i, ∑ k, (TensorProduct.dualDistrib R (G.level v) (G.level v)
            (TensorProduct.map (CartierDual.toDual R (G.level v)).toLinearMap
              (CartierDual.toDual R (G.level v)).toLinearMap w) (bas G v i ⊗ₜ[R] bas G v k)) •
            (lam D S v ψ ((bas G v).coord i) * lam D S v ψ' ((bas G v).coord k))) =
          Lam D S v ψ ψ' w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul α β =>
          rw [Lam_tmul, ← sum_smul_lam D S v ψ α, ← sum_smul_lam D S v ψ' β, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          rw [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, smul_mul_smul_comm]
          rfl
      | add x y hx hy =>
          simp only [map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib, hx, hy]
    rw [← hkey, charElem_eq, charElem_eq, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, T_tmul, CartierDual.comul_pairing]
    rfl
  rw [hL, hR]

theorem map_charElem {S' : Type} [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (v : ℕ)
    (ψ : G'.Point S v) :
    Algebra.TensorProduct.map σ (AlgHom.id R (G.level v)) (D.charElem S v ψ) =
      D.charElem S' v (G'.pointMap σ v ψ) := by
  rw [D.charElem_def, D.charElem_def, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, toAlgHom_pointMap, AlgHom.comp_apply]

noncomputable abbrev epsS (v : ℕ) : S ⊗[R] G.level v →ₗ[R] S := T S (counit (R := R) (A := G.level v))

theorem epsS_charElem (v : ℕ) (ψ : G'.Point S v) : epsS S v (D.charElem S v ψ) = 1 := by
  rw [T_charElem, CartierDuality.toDualEquiv_symm_apply, ← CartierDual.one_def, map_one, map_one]

theorem cotangentClass_mul (v : ℕ) (a a' : G.level v) :
    G.cotangentClass v (a * a') =
      counit (R := R) a • G.cotangentClass v a' + counit (R := R) a' • G.cotangentClass v a := by
  rw [cotangentClass_apply, cotangentClass_apply, cotangentClass_apply,
    ← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower, ← map_add, Ideal.toCotangent_eq,
    pow_two]
  refine Ideal.mul_mem_mul (Hopf.sub_algebraMap_counit_mem_augIdeal R _ a)
    (Hopf.sub_algebraMap_counit_mem_augIdeal R _ a') |> fun hmem => ?_
  convert hmem using 1
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Bialgebra.counit_mul, map_mul,
    Algebra.smul_def]
  ring

theorem lTensor_cotangentClass_mul (v : ℕ) (x y : S ⊗[R] G.level v) :
    (G.cotangentClass v).lTensor S (x * y) =
      epsS S v x • (G.cotangentClass v).lTensor S y + epsS S v y • (G.cotangentClass v).lTensor S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t a' =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
            LinearMap.lTensor_tmul, T_tmul, T_tmul, cotangentClass_mul, TensorProduct.tmul_add,
            TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
            smul_mul_assoc, smul_mul_assoc, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
            mul_comm t s]
      | add y₁ y₂ h₁ h₂ =>
          rw [mul_add, map_add, h₁, h₂, map_add, map_add, smul_add, add_smul]
          abel
  | add x₁ x₂ h₁ h₂ =>
      rw [add_mul, map_add, h₁, h₂, map_add, map_add, add_smul, smul_add]
      abel

theorem charDiff_mul (v : ℕ) (ψ ψ' : G'.Point S v) :
    D.charDiff S v (ψ * ψ') = D.charDiff S v ψ + D.charDiff S v ψ' := by
  rw [D.charDiff_def, D.charDiff_def, D.charDiff_def, charElem_mul, lTensor_cotangentClass_mul,
    epsS_charElem, epsS_charElem, one_smul, one_smul, add_comm]

theorem charDiff_one (v : ℕ) : D.charDiff S v (1 : G'.Point S v) = 0 := by
  rw [D.charDiff_def, charElem_one, Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul,
    cotangentClass_one, TensorProduct.tmul_zero]

theorem map_charDiff {S' : Type} [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (v : ℕ)
    (ψ : G'.Point S v) :
    TensorProduct.map σ.toLinearMap LinearMap.id (D.charDiff S v ψ) =
      D.charDiff S' v (G'.pointMap σ v ψ) := by
  rw [D.charDiff_def, D.charDiff_def, ← map_charElem, D.charElem_def, map_sum, map_sum, map_sum,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.lTensor_tmul, TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    LinearMap.lTensor_tmul]
  rfl

theorem lTensor_transition_charElem (v : ℕ) (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1))
    (hψ : G'.pointIncl S v ψ = ψ₁ ^ p) :
    (G.transitionAlgHom v).toLinearMap.lTensor S (D.charElem S (v + 1) ψ₁) = D.charElem S v ψ := by
  refine eq_of_forall_T_eq S (bas G v) fun φ => ?_
  rw [T_lTensor, T_charElem, T_charElem]
  obtain ⟨x₁, hx₁⟩ := G'.transition_surjective v ((D.toDualEquiv v).symm φ)

  have h1 : Point.toAlgHom ψ ((D.toDualEquiv v).symm φ) =
      Point.toAlgHom ψ₁ (Hopf.nsmulAlgHom R _ p x₁) := by
    rw [← hx₁, ← pointIncl_apply, hψ, Point.toAlgHom_pow, AlgHom.comp_apply]

  have h2 : (D.toDualEquiv (v + 1)).symm (φ ∘ₗ (G.transitionAlgHom v).toLinearMap) =
      Hopf.nsmulAlgHom R _ p x₁ := by
    rw [LinearEquiv.symm_apply_eq]
    have h3 : φ = D.toDualEquiv v (G'.transition v x₁) := by
      rw [hx₁, LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro a
    have h4 : D.equiv (v + 1) (Hopf.nsmulAlgHom R _ p x₁) =
        Hopf.nsmulAlgHom R _ p (D.equiv (v + 1) x₁) :=
      (Hopf.nsmulAlgHom_bialgHom_apply
        (D.equiv (v + 1) : G'.level (v + 1) →ₐc[R] CartierDual R (G.level (v + 1))) p x₁).symm
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, CartierDuality.toDualEquiv_apply, h3,
      CartierDuality.toDualEquiv_apply, transitionAlgHom_apply, D.equiv_transition, h4,
      nsmulAlgHom_cartierDual_apply]
  rw [h1, h2]

theorem cotangentMap_comp_cotangentClass (v : ℕ) :
    (G.cotangentMap v) ∘ₗ (G.cotangentClass (v + 1)) =
      (G.cotangentClass v) ∘ₗ (G.transitionAlgHom v).toLinearMap := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, cotangentClass_apply, cotangentMap_toCotangent,
    AlgHom.toLinearMap_apply, cotangentClass_apply]
  congr 1
  ext
  change G.transition v (a - algebraMap R _ (counit (R := R) a)) =
    G.transitionAlgHom v a - algebraMap R _ (counit (R := R) (G.transitionAlgHom v a))
  rw [map_sub, transitionAlgHom_apply, counit_transition]
  congr 1
  exact (G.transitionAlgHom v).commutes _

theorem lTensor_cotangentMap_charDiff (v : ℕ) (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1))
    (hψ : G'.pointIncl S v ψ = ψ₁ ^ p) :
    (G.cotangentMap v).lTensor S (D.charDiff S (v + 1) ψ₁) = D.charDiff S v ψ := by
  rw [D.charDiff_def, D.charDiff_def, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    cotangentMap_comp_cotangentClass, LinearMap.lTensor_comp, LinearMap.comp_apply,
    lTensor_transition_charElem D S v ψ ψ₁ hψ]

end Char

end PDivCharDiff
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff.PDivCharDiff"

open PDivCharDiff in

theorem solution
    {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (S : Type) [CommRing S] [Algebra R S] (v : ℕ) :
    (∀ (ψ : G'.Point S v) (φ : Module.Dual R (G.level v)),
        TensorProduct.rid R S (φ.lTensor S (D.charElem S v ψ)) =
          Point.toAlgHom ψ ((D.toDualEquiv v).symm φ)) ∧
    (∀ (f : G.Point S v) (ψ : G'.Point S v),
        Algebra.TensorProduct.lift (AlgHom.id R S) (Point.toAlgHom f) (fun _ _ => .all _ _)
          (D.charElem S v ψ) = D.pair S v f ψ) ∧
    (∀ ψ ψ' : G'.Point S v, D.charElem S v (ψ * ψ') = D.charElem S v ψ * D.charElem S v ψ') ∧
    D.charElem S v 1 = 1 ∧
    (∀ ψ ψ' : G'.Point S v, D.charDiff S v (ψ * ψ') = D.charDiff S v ψ + D.charDiff S v ψ') ∧
    D.charDiff S v 1 = 0 ∧
    (∀ (S' : Type) [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (ψ : G'.Point S v),
        Algebra.TensorProduct.map σ (AlgHom.id R (G.level v)) (D.charElem S v ψ) =
          D.charElem S' v (G'.pointMap σ v ψ)) ∧
    (∀ (S' : Type) [CommRing S'] [Algebra R S'] (σ : S →ₐ[R] S') (ψ : G'.Point S v),
        TensorProduct.map σ.toLinearMap LinearMap.id (D.charDiff S v ψ) =
          D.charDiff S' v (G'.pointMap σ v ψ)) ∧
    (∀ (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1)), G'.pointIncl S v ψ = ψ₁ ^ p →
        (G.transitionAlgHom v).toLinearMap.lTensor S (D.charElem S (v + 1) ψ₁) = D.charElem S v ψ) ∧
    (∀ (ψ : G'.Point S v) (ψ₁ : G'.Point S (v + 1)), G'.pointIncl S v ψ = ψ₁ ^ p →
        (G.cotangentMap v).lTensor S (D.charDiff S (v + 1) ψ₁) = D.charDiff S v ψ) :=
  ⟨fun ψ φ => T_charElem D S v ψ φ, lift_charElem D S v, charElem_mul D S v, charElem_one D S v,
    charDiff_mul D S v, charDiff_one D S v, fun _ _ _ σ ψ => map_charElem D S σ v ψ,
    fun _ _ _ σ ψ => map_charDiff D S σ v ψ, lTensor_transition_charElem D S v,
    lTensor_cotangentMap_charDiff D S v⟩

end S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff (solution)
