-- Prove2me | solution 1 for PDivisibleGroup.exists_prod_bialgHom_bijective_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/72059755-54c3-5ca0-80f0-36f354fa0c99

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_prod_bialgHom_bijective_points

set_option autoImplicit false

open scoped TensorProduct
open PDivisibleGroup.Hopf

namespace ProdAux

section Incl

variable (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

noncomputable def inclLeftBialgHom : A →ₐc[R] A ⊗[R] B :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)
    (by
      ext a
      simp [Algebra.TensorProduct.includeLeft_apply, TensorProduct.counit_tmul])
    (by
      ext a
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeLeft_apply,
        TensorProduct.comul_tmul, Bialgebra.comul_one]

      rw [Algebra.TensorProduct.one_def]
      induction CoalgebraStruct.comul (R := R) a using TensorProduct.induction_on with
      | zero => rw [map_zero, TensorProduct.zero_tmul, LinearEquiv.map_zero]
      | tmul x y =>
        rw [Algebra.TensorProduct.map_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
        rfl
      | add x y hx hy => rw [map_add, TensorProduct.add_tmul, LinearEquiv.map_add, hx, hy])

@[scoped simp] theorem inclLeftBialgHom_apply (a : A) : inclLeftBialgHom R A B a = a ⊗ₜ[R] 1 := rfl

theorem coe_inclLeftBialgHom : (inclLeftBialgHom R A B : A →ₐ[R] A ⊗[R] B) = Algebra.TensorProduct.includeLeft := by
  ext a; rfl

noncomputable def inclRightBialgHom : B →ₐc[R] A ⊗[R] B :=
  BialgHom.ofAlgHom (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)
    (by
      ext b
      simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul])
    (by
      ext b
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Algebra.TensorProduct.includeRight_apply,
        TensorProduct.comul_tmul, Bialgebra.comul_one]
      rw [Algebra.TensorProduct.one_def]
      induction CoalgebraStruct.comul (R := R) b using TensorProduct.induction_on with
      | zero => rw [map_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero]
      | tmul x y =>
        rw [Algebra.TensorProduct.map_tmul, TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
        rfl
      | add x y hx hy => rw [map_add, TensorProduct.tmul_add, LinearEquiv.map_add, hx, hy])

@[scoped simp] theorem inclRightBialgHom_apply (b : B) : inclRightBialgHom R A B b = 1 ⊗ₜ[R] b := rfl

theorem coe_inclRightBialgHom : (inclRightBialgHom R A B : B →ₐ[R] A ⊗[R] B) = Algebra.TensorProduct.includeRight := by
  ext b; rfl

end Incl

section NSMul

variable (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

theorem nsmulAlgHom_tensorProduct (n : ℕ) :
    nsmulAlgHom R (A ⊗[R] B) n = Algebra.TensorProduct.map (nsmulAlgHom R A n) (nsmulAlgHom R B n) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  have ha : nsmulAlgHom R (A ⊗[R] B) n (a ⊗ₜ[R] 1) = nsmulAlgHom R A n a ⊗ₜ[R] 1 := by
    have := nsmulAlgHom_bialgHom_apply (R := R) (A := A ⊗[R] B) (inclLeftBialgHom R A B) n a
    simpa using this
  have hb : nsmulAlgHom R (A ⊗[R] B) n (1 ⊗ₜ[R] b) = 1 ⊗ₜ[R] nsmulAlgHom R B n b := by
    have := nsmulAlgHom_bialgHom_apply (R := R) (A := A ⊗[R] B) (inclRightBialgHom R A B) n b
    simpa using this
  have hab : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hab, map_mul, map_mul, ha, hb, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    map_one, map_one]

theorem augIdeal_tensorProduct :
    augIdeal R (A ⊗[R] B) =
      (augIdeal R A).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) ⊔
      (augIdeal R B).map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) := by

  have hsA : Function.Surjective (Bialgebra.counitAlgHom R A) := fun r => ⟨algebraMap R A r, by simp⟩
  have hsB : Function.Surjective (Bialgebra.counitAlgHom R B) := fun r => ⟨algebraMap R B r, by simp⟩
  have hker := Algebra.TensorProduct.map_ker (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R B) hsA hsB
  have hcomp : (Bialgebra.counitAlgHom R (A ⊗[R] B) : A ⊗[R] B →ₐ[R] R) =
      (Algebra.TensorProduct.lid R R).toAlgHom.comp
        (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R B)) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp [TensorProduct.counit_tmul, mul_comm]
  unfold augIdeal
  rw [← hker]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have hx : (Bialgebra.counitAlgHom R (A ⊗[R] B)) x = Algebra.TensorProduct.lid R R
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R B) x) :=
    DFunLike.congr_fun hcomp x
  show (Bialgebra.counitAlgHom R (A ⊗[R] B)) x = 0 ↔ (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R B)) x = 0
  rw [hx, map_eq_zero_iff _ (Algebra.TensorProduct.lid R R).injective]

theorem torsionIdeal_tensorProduct (n : ℕ) :
    torsionIdeal R (A ⊗[R] B) n =
      (torsionIdeal R A n).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) ⊔
      (torsionIdeal R B n).map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) := by
  have h1 : (torsionIdeal R A n).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) =
      ((augIdeal R A).map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).map
        (Algebra.TensorProduct.map (nsmulAlgHom R A n) (nsmulAlgHom R B n)) := by
    rw [torsionIdeal]
    change Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom
        (Ideal.map (nsmulAlgHom R A n).toRingHom (augIdeal R A)) =
      Ideal.map (Algebra.TensorProduct.map (nsmulAlgHom R A n) (nsmulAlgHom R B n)).toRingHom
        (Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom (augIdeal R A))
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    simp [Algebra.TensorProduct.map_tmul]
  have h2 : (torsionIdeal R B n).map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) =
      ((augIdeal R B).map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).map
        (Algebra.TensorProduct.map (nsmulAlgHom R A n) (nsmulAlgHom R B n)) := by
    rw [torsionIdeal]
    change Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
        (Ideal.map (nsmulAlgHom R B n).toRingHom (augIdeal R B)) =
      Ideal.map (Algebra.TensorProduct.map (nsmulAlgHom R A n) (nsmulAlgHom R B n)).toRingHom
        (Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom (augIdeal R B))
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext b
    simp [Algebra.TensorProduct.map_tmul]
  rw [h1, h2, torsionIdeal, augIdeal_tensorProduct, nsmulAlgHom_tensorProduct, Ideal.map_sup]

end NSMul

end ProdAux
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_prod_bialgHom_bijective_points.ProdAux"

namespace ProductPoints

variable {R : Type} [CommRing R] {A B : Type} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
variable (L : Type) [CommRing L] [Algebra R L]

noncomputable def restrict (x : A ⊗[R] B →ₐ[R] L) : (A →ₐ[R] L) × (B →ₐ[R] L) :=
  (x.comp Algebra.TensorProduct.includeLeft, x.comp Algebra.TensorProduct.includeRight)

noncomputable def glue (fg : (A →ₐ[R] L) × (B →ₐ[R] L)) : A ⊗[R] B →ₐ[R] L :=
  Algebra.TensorProduct.lift fg.1 fg.2 (fun _ _ => Commute.all _ _)

theorem glue_restrict (x : A ⊗[R] B →ₐ[R] L) : glue L (restrict L x) = x := by
  apply Algebra.TensorProduct.ext
  · ext a; simp [glue, restrict]
  · ext b; simp [glue, restrict]

theorem restrict_glue (fg : (A →ₐ[R] L) × (B →ₐ[R] L)) : restrict L (glue L fg) = fg := by
  obtain ⟨f, g⟩ := fg
  ext a
  · simp [glue, restrict]
  · simp [glue, restrict]

noncomputable def pointsEquiv : (A ⊗[R] B →ₐ[R] L) ≃ (A →ₐ[R] L) × (B →ₐ[R] L) :=
  ⟨restrict L, glue L, glue_restrict L, restrict_glue L⟩

theorem ofConv_comp_mul {C : Type} [CommRing C] [Bialgebra R C] (π : C →ₐc[R] A ⊗[R] B)
    (x y : WithConv (A ⊗[R] B →ₐ[R] L)) :
    WithConv.toConv ((WithConv.ofConv (x * y)).comp (π : C →ₐ[R] A ⊗[R] B)) =
      WithConv.toConv ((WithConv.ofConv x).comp (π : C →ₐ[R] A ⊗[R] B)) *
        WithConv.toConv ((WithConv.ofConv y).comp (π : C →ₐ[R] A ⊗[R] B)) :=
  map_mul (PDivisibleGroup.Hopf.convCompMonoidHom L π) x y

theorem bijective_and_mul (iA : A →ₐc[R] A ⊗[R] B) (iB : B →ₐc[R] A ⊗[R] B)
    (hiA : (iA : A →ₐ[R] A ⊗[R] B) = Algebra.TensorProduct.includeLeft)
    (hiB : (iB : B →ₐ[R] A ⊗[R] B) = Algebra.TensorProduct.includeRight) :
    Function.Bijective (fun x : WithConv (A ⊗[R] B →ₐ[R] L) =>
      (WithConv.toConv ((WithConv.ofConv x).comp (iA : A →ₐ[R] A ⊗[R] B)),
       WithConv.toConv ((WithConv.ofConv x).comp (iB : B →ₐ[R] A ⊗[R] B)))) ∧
    ∀ x y : WithConv (A ⊗[R] B →ₐ[R] L),
      WithConv.toConv ((WithConv.ofConv (x * y)).comp (iA : A →ₐ[R] A ⊗[R] B)) =
        WithConv.toConv ((WithConv.ofConv x).comp (iA : A →ₐ[R] A ⊗[R] B)) *
          WithConv.toConv ((WithConv.ofConv y).comp (iA : A →ₐ[R] A ⊗[R] B)) ∧
      WithConv.toConv ((WithConv.ofConv (x * y)).comp (iB : B →ₐ[R] A ⊗[R] B)) =
        WithConv.toConv ((WithConv.ofConv x).comp (iB : B →ₐ[R] A ⊗[R] B)) *
          WithConv.toConv ((WithConv.ofConv y).comp (iB : B →ₐ[R] A ⊗[R] B)) := by
  refine ⟨?_, fun x y => ⟨ofConv_comp_mul L iA x y, ofConv_comp_mul L iB x y⟩⟩
  rw [hiA, hiB]
  let e : WithConv (A ⊗[R] B →ₐ[R] L) ≃ WithConv (A →ₐ[R] L) × WithConv (B →ₐ[R] L) :=
    (WithConv.equiv (A ⊗[R] B →ₐ[R] L)).trans ((pointsEquiv L).trans
      ((WithConv.equiv (A →ₐ[R] L)).symm.prodCongr (WithConv.equiv (B →ₐ[R] L)).symm))
  exact e.bijective

end ProductPoints
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_prod_bialgHom_bijective_points.ProdAux"

open ProdAux

set_option maxHeartbeats 3200000 in

theorem solution
    {R : Type} [CommRing R] {p h h' : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h) (H : PDivisibleGroup R p h') :
    ∃ (P : PDivisibleGroup R p (h + h'))
      (iG : ∀ v : ℕ, G.level v →ₐc[R] P.level v) (iH : ∀ v : ℕ, H.level v →ₐc[R] P.level v),
      (∀ v : ℕ, (iG v).comp (G.transition v) = (P.transition v).comp (iG (v + 1))) ∧
      (∀ v : ℕ, (iH v).comp (H.transition v) = (P.transition v).comp (iH (v + 1))) ∧
      ∀ (L : Type) [CommRing L] [Algebra R L] (v : ℕ),
        Function.Bijective (fun x : P.Point L v =>
          ((PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) :
              G.Point L v),
           (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) :
              H.Point L v))) ∧
        ∀ x y : P.Point L v,
          (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iG v : G.level v →ₐ[R] P.level v)) :
              G.Point L v) =
            PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iG v : G.level v →ₐ[R] P.level v)) *
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iG v : G.level v →ₐ[R] P.level v)) ∧
          (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom (x * y)).comp (iH v : H.level v →ₐ[R] P.level v)) :
              H.Point L v) =
            PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (iH v : H.level v →ₐ[R] P.level v)) *
              PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (iH v : H.level v →ₐ[R] P.level v)) := by
  classical

  have hfun : ∀ (v : ℕ) (x : G.level (v + 1) ⊗[R] H.level (v + 1)),
      Bialgebra.TensorProduct.map (G.transition v) (H.transition v) x =
        Algebra.TensorProduct.map (G.transition v : G.level (v + 1) →ₐ[R] G.level v)
          (H.transition v : H.level (v + 1) →ₐ[R] H.level v) x := by
    intro v x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rw [Bialgebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let P : PDivisibleGroup R p (h + h') :=
    { level := fun v => G.level v ⊗[R] H.level v
      instCommRing := fun v => inferInstance
      instHopfAlgebra := fun v => inferInstance
      instIsCocomm := fun v => inferInstance
      instModuleFinite := fun v => inferInstance
      instModuleFree := fun v => inferInstance
      transition := fun v => Bialgebra.TensorProduct.map (G.transition v) (H.transition v)
      transition_surjective := fun v => by
        have hs : Function.Surjective (Algebra.TensorProduct.map (G.transition v : G.level (v + 1) →ₐ[R] G.level v)
            (H.transition v : H.level (v + 1) →ₐ[R] H.level v)) :=
          TensorProduct.map_surjective (G.transition_surjective v) (H.transition_surjective v)
        intro y
        obtain ⟨x, hx⟩ := hs y
        exact ⟨x, (hfun v x).trans hx⟩
      finrank_level := fun v => by
        rcases subsingleton_or_nontrivial R with hR | hR
        ·
          have e1 : ∀ (M : Type) [AddCommGroup M] [Module R M], Module.finrank R M = 1 := fun M _ _ =>
            Module.finrank_eq_of_rank_eq (by rw [rank_subsingleton, Nat.cast_one])
          have hG := G.finrank_level v
          have hH := H.finrank_level v
          rw [e1] at hG hH ⊢
          rw [mul_add, pow_add, ← hG, ← hH, one_mul]
        · rw [Module.finrank_tensorProduct, G.finrank_level, H.finrank_level, ← pow_add]
          congr 1; ring
      ker_transition := fun v => by
        have hk : RingHom.ker (Bialgebra.TensorProduct.map (G.transition v) (H.transition v)) =
            RingHom.ker (Algebra.TensorProduct.map (G.transition v : G.level (v + 1) →ₐ[R] G.level v)
              (H.transition v : H.level (v + 1) →ₐ[R] H.level v)) := by
          ext x
          rw [RingHom.mem_ker, RingHom.mem_ker]
          exact Iff.of_eq (congrArg (· = 0) (hfun v x))
        have hG : RingHom.ker (G.transition v : G.level (v + 1) →ₐ[R] G.level v) =
            torsionIdeal R (G.level (v + 1)) (p ^ v) :=
          Ideal.ext fun x => by rw [RingHom.mem_ker]; exact G.mem_ker_transition_iff v x
        have hH : RingHom.ker (H.transition v : H.level (v + 1) →ₐ[R] H.level v) =
            torsionIdeal R (H.level (v + 1)) (p ^ v) :=
          Ideal.ext fun x => by rw [RingHom.mem_ker]; exact H.mem_ker_transition_iff v x
        rw [hk, Algebra.TensorProduct.map_ker _ _ (G.transition_surjective v) (H.transition_surjective v),
          hG, hH, ← ProdAux.torsionIdeal_tensorProduct] }
  refine ⟨P, fun v => ProdAux.inclLeftBialgHom R (G.level v) (H.level v),
    fun v => ProdAux.inclRightBialgHom R (G.level v) (H.level v), ?_, ?_, ?_⟩
  · intro v
    apply BialgHom.coe_algHom_injective
    ext a
    show (G.transition v a) ⊗ₜ[R] (1 : H.level v) =
      Bialgebra.TensorProduct.map (G.transition v) (H.transition v) (a ⊗ₜ[R] (1 : H.level (v + 1)))
    rw [Bialgebra.TensorProduct.map_tmul, map_one]
  · intro v
    apply BialgHom.coe_algHom_injective
    ext b
    show (1 : G.level v) ⊗ₜ[R] (H.transition v b) =
      Bialgebra.TensorProduct.map (G.transition v) (H.transition v) ((1 : G.level (v + 1)) ⊗ₜ[R] b)
    rw [Bialgebra.TensorProduct.map_tmul, map_one]
  · intro L _ _ v
    exact ProductPoints.bijective_and_mul L (ProdAux.inclLeftBialgHom R (G.level v) (H.level v))
      (ProdAux.inclRightBialgHom R (G.level v) (H.level v))
      (ProdAux.coe_inclLeftBialgHom R (G.level v) (H.level v)) (ProdAux.coe_inclRightBialgHom R (G.level v) (H.level v))

end S_PDivisibleGroup_exists_prod_bialgHom_bijective_points
end P2MW
export P2MW.S_PDivisibleGroup_exists_prod_bialgHom_bijective_points (solution)
