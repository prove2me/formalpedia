-- Prove2me | solution 1 for PDivisibleGroup.exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0989f16a-b561-5253-8292-75af7bb0dfe7

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w

set_option linter.unusedSectionVars false

namespace S42SLP

section Image

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {A : Type} [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

structure ImageDatum (φ : A →ₐc[R] A) : Type 1 where
  Q : Type
  [instCommRing : CommRing Q]
  [instHopf : HopfAlgebra R Q]
  [instFinite : Module.Finite R Q]
  [instFlat : Module.Flat R Q]
  π : A →ₐc[R] Q
  ι : Q →ₐc[R] A
  π_surjective : Function.Surjective π
  ι_injective : Function.Injective ι
  ι_comp_π : ι.comp π = φ

attribute [scoped instance] ImageDatum.instCommRing ImageDatum.instHopf ImageDatum.instFinite ImageDatum.instFlat

theorem ImageDatum.nonempty (φ : A →ₐc[R] A) : Nonempty (ImageDatum φ) := by
  obtain ⟨Q, _, _, _, _, π, ι, hπ, hι, hιπ, -, -⟩ :=
    HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem φ
  exact ⟨⟨Q, π, ι, hπ, hι, hιπ⟩⟩

namespace ImageDatum

variable {φ : A →ₐc[R] A} (D : ImageDatum φ)

scoped instance instFree : Module.Free R D.Q := Module.free_iff_isTorsionFree.2 inferInstance

theorem ι_π (a : A) : D.ι (D.π a) = φ a := by
  rw [← BialgHom.comp_apply, D.ι_comp_π]

theorem π_ι (hφ : φ.comp φ = φ) (q : D.Q) : D.π (D.ι q) = q := by
  obtain ⟨a, rfl⟩ := D.π_surjective q
  apply D.ι_injective
  rw [D.ι_π, D.ι_π, ← BialgHom.comp_apply, hφ]

theorem π_comp_ι (hφ : φ.comp φ = φ) : D.π.comp D.ι = BialgHom.id R D.Q :=
  BialgHom.ext (D.π_ι hφ)

theorem isCocomm [Coalgebra.IsCocomm R A] : Coalgebra.IsCocomm R D.Q := by
  refine ⟨LinearMap.ext fun q => ?_⟩
  obtain ⟨a, rfl⟩ := D.π_surjective q
  have h := congrArg (fun f : A →ₗ[R] A ⊗[R] A => f a) (Coalgebra.comm_comp_comul R A)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  have hc : ∀ (f : A →ₗ[R] D.Q) (t : A ⊗[R] A), TensorProduct.comm R D.Q D.Q (TensorProduct.map f f t) =
      TensorProduct.map f f (TensorProduct.comm R A A t) := by
    intro f t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← CoalgHomClass.map_comp_comul_apply D.π a]
  exact (hc _ _).trans (by rw [h])

def pointEquiv (hφ : φ.comp φ = φ) (L : Type) [CommRing L] [Algebra R L] :
    (D.Q →ₐ[R] L) ≃ {x : A →ₐ[R] L // x.comp (φ : A →ₐ[R] A) = x} where
  toFun y := ⟨y.comp (D.π : A →ₐ[R] D.Q), by
    ext a
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
    rw [← D.ι_π, D.π_ι hφ]⟩
  invFun x := x.1.comp (D.ι : D.Q →ₐ[R] A)
  left_inv y := by
    ext q
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, D.π_ι hφ]
  right_inv x := by
    apply Subtype.ext
    ext a
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, D.ι_π]
    exact AlgHom.congr_fun x.2 a

end ImageDatum
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.S42SLP.ImageDatum"

end Image
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.S42SLP.ImageDatum"

section Descend

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {B : Type*} [CommRing B] [Bialgebra R B] {C : Type*} [CommRing C] [Algebra R C]

theorem ker_eq_map_of_comp_eq {f : B →ₐ[R] C} {π : A →ₐ[R] B} (hπ : Function.Surjective π)
    {g : A →ₐ[R] C} (h : f.comp π = g) :
    RingHom.ker f = Ideal.map π (RingHom.ker g) := by
  have hk : RingHom.ker g = Ideal.comap π (RingHom.ker f) := by
    ext a; rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ← AlgHom.comp_apply, h]
  rw [hk, Ideal.map_comap_of_surjective _ hπ]

theorem exists_mem_augIdeal_apply_eq (φ : A →ₐc[R] B) (hφ : Function.Surjective φ) {b : B}
    (hb : b ∈ PDivisibleGroup.Hopf.augIdeal R B) : ∃ a ∈ PDivisibleGroup.Hopf.augIdeal R A, φ a = b := by
  obtain ⟨a, rfl⟩ := hφ b
  refine ⟨a - algebraMap R A (Coalgebra.counit (R := R) a),
    PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal R A a, ?_⟩
  have hb' : Coalgebra.counit (R := R) a = 0 := by
    rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, CoalgHomClass.counit_comp_apply] at hb
    exact hb
  rw [hb', map_zero, sub_zero]

theorem map_torsionIdeal_eq (φ : A →ₐc[R] B) (hφ : Function.Surjective φ) (n : ℕ) :
    Ideal.map (φ : A →ₐ[R] B) (PDivisibleGroup.Hopf.torsionIdeal R A n) =
      PDivisibleGroup.Hopf.torsionIdeal R B n := by
  apply le_antisymm
  · rw [PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, BialgHom.coe_toAlgHom,
      ← PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply φ n a]
    refine PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal R B ?_ n
    rw [PDivisibleGroup.Hopf.mem_augIdeal_iff, CoalgHomClass.counit_comp_apply]
    exact ha
  · rw [PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨a, ha, rfl⟩ := exists_mem_augIdeal_apply_eq φ hφ hb
    rw [Ideal.mem_comap, PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply φ n a]
    exact Ideal.mem_map_of_mem (φ : A →ₐ[R] B) (PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal R A ha n)

end Descend
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.S42SLP.ImageDatum"

section SubTower

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra O (AlgebraicClosure ℚ)] {h : ℕ} (H : PDivisibleGroup O p h)
  (ε : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
  (hε : ∀ v, (ε v).comp (ε v) = ε v)
  (hεt : ∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
  (h₁ : ℕ)
  (hcard : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
      (PDivisibleGroup.Point.toAlgHom x).comp (ε v : H.level v →ₐ[O] H.level v) =
        PDivisibleGroup.Point.toAlgHom x} = p ^ (v * h₁))
  (D : ∀ v, ImageDatum (ε v))

noncomputable def subTransition (v : ℕ) : (D (v + 1)).Q →ₐc[O] (D v).Q :=
  ((D v).π.comp (H.transition v)).comp (D (v + 1)).ι

include hε hεt in
theorem subTransition_comp_π (v : ℕ) :
    (subTransition H ε D v).comp (D (v + 1)).π = (D v).π.comp (H.transition v) := by
  apply BialgHom.ext
  intro a
  show (D v).π (H.transition v ((D (v + 1)).ι ((D (v + 1)).π a))) = (D v).π (H.transition v a)
  rw [ImageDatum.ι_π, ← BialgHom.comp_apply (H.transition v) (ε (v + 1)), hεt, BialgHom.comp_apply,
    ← (D v).ι_π, ImageDatum.π_ι _ (hε v)]

include hε hεt in
theorem subTransition_surjective (v : ℕ) : Function.Surjective (subTransition H ε D v) := by
  intro y
  obtain ⟨x, rfl⟩ := (D v).π_surjective y
  obtain ⟨x', rfl⟩ := H.transition_surjective v x
  exact ⟨(D (v + 1)).π x', by rw [← BialgHom.comp_apply, subTransition_comp_π H ε hε hεt D v]; rfl⟩

include hε hεt in
theorem ker_subTransition (v : ℕ) :
    RingHom.ker (subTransition H ε D v) = PDivisibleGroup.Hopf.torsionIdeal O (D (v + 1)).Q (p ^ v) := by
  have hπ' := (D (v + 1)).π_surjective

  have h1 : RingHom.ker (subTransition H ε D v : (D (v + 1)).Q →ₐ[O] (D v).Q) =
      Ideal.map ((D (v + 1)).π : H.level (v + 1) →ₐ[O] (D (v + 1)).Q)
        (RingHom.ker (((D v).π : H.level v →ₐ[O] (D v).Q).comp (H.transition v : H.level (v + 1) →ₐ[O] H.level v))) := by
    refine ker_eq_map_of_comp_eq hπ' ?_
    apply AlgHom.ext
    intro a
    exact DFunLike.congr_fun (subTransition_comp_π H ε hε hεt D v) a

  rw [← map_torsionIdeal_eq (D (v + 1)).π hπ', ← H.ker_transition]
  change RingHom.ker (subTransition H ε D v : (D (v + 1)).Q →ₐ[O] (D v).Q) = _
  rw [h1]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [RingHom.mem_ker, AlgHom.comp_apply] at hx
    rw [Ideal.mem_comap]

    have hεx : H.transition v (ε (v + 1) x) = 0 := by
      rw [← BialgHom.comp_apply, hεt, BialgHom.comp_apply, ← (D v).ι_π]
      show (D v).ι (((D v).π : H.level v →ₐ[O] (D v).Q) ((H.transition v : H.level (v + 1) →ₐ[O] H.level v) x)) = 0
      rw [hx, map_zero]
    have hx' : ((D (v + 1)).π : H.level (v + 1) →ₐ[O] (D (v + 1)).Q) x = (D (v + 1)).π (ε (v + 1) x) := by
      show (D (v + 1)).π x = (D (v + 1)).π (ε (v + 1) x)
      rw [← (D (v + 1)).ι_π, ImageDatum.π_ι _ (hε (v + 1))]
    rw [hx']
    exact Ideal.mem_map_of_mem _ hεx
  · exact Ideal.map_mono fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [AlgHom.comp_apply]
      show (D v).π (H.transition v x) = 0
      rw [hx, map_zero]

include hε hcard in
theorem finrank_Q (v : ℕ) : Module.finrank O (D v).Q = p ^ (v * h₁) := by
  classical
  rw [← HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O (D v).Q (AlgebraicClosure ℚ), ← hcard v,
    Nat.card_congr ((D v).pointEquiv (hε v) (AlgebraicClosure ℚ))]
  refine Nat.card_congr (Equiv.subtypeEquiv ⟨PDivisibleGroup.Point.ofAlgHom, PDivisibleGroup.Point.toAlgHom,
    fun _ => rfl, fun _ => rfl⟩ fun x => Iff.rfl)

noncomputable def subGroup : PDivisibleGroup O p h₁ where
  level v := (D v).Q
  instIsCocomm v := (D v).isCocomm
  transition := subTransition H ε D
  transition_surjective := subTransition_surjective H ε hε hεt D
  finrank_level := finrank_Q H ε hε h₁ hcard D
  ker_transition := ker_subTransition H ε hε hεt D

end SubTower
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.S42SLP.ImageDatum"

section Theta

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A] [Coalgebra.IsCocomm O A]
  {ε ε' : A →ₐc[O] A} (D₁ : ImageDatum ε) (D₂ : ImageDatum ε')

theorem algMap_eq {B C B' C' : Type} [CommRing B] [CommRing C] [CommRing B'] [CommRing C']
    [Algebra O B] [Algebra O C] [Algebra O B'] [Algebra O C'] (f : B →ₐ[O] B') (g : C →ₐ[O] C') (x : B ⊗[O] C) :
    Algebra.TensorProduct.map f g x = TensorProduct.map f.toLinearMap g.toLinearMap x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem algMap_algMap {B C B' C' B'' C'' : Type} [CommRing B] [CommRing C] [CommRing B'] [CommRing C'] [CommRing B''] [CommRing C'']
    [Algebra O B] [Algebra O C] [Algebra O B'] [Algebra O C'] [Algebra O B''] [Algebra O C'']
    (f : B' →ₐ[O] B'') (g : C' →ₐ[O] C'') (f' : B →ₐ[O] B') (g' : C →ₐ[O] C') (x : B ⊗[O] C) :
    Algebra.TensorProduct.map f g (Algebra.TensorProduct.map f' g' x) =
      Algebra.TensorProduct.map (f.comp f') (g.comp g') x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a b => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem comul_bialgHom {B C : Type} [CommRing B] [CommRing C] [Bialgebra O B] [Bialgebra O C]
    (φ : B →ₐc[O] C) (b : B) : Coalgebra.comul (R := O) (φ b) =
      Algebra.TensorProduct.map (φ : B →ₐ[O] C) (φ : B →ₐ[O] C) (Coalgebra.comul (R := O) b) := by
  rw [algMap_eq]
  exact (CoalgHomClass.map_comp_comul_apply φ b).symm

noncomputable def theta : A →ₐc[O] D₁.Q ⊗[O] D₂.Q :=
  (Bialgebra.TensorProduct.map D₁.π D₂.π).comp (Bialgebra.comulBialgHom O A)

theorem theta_apply (b : A) : theta D₁ D₂ b =
    Algebra.TensorProduct.map (D₁.π : A →ₐ[O] D₁.Q) (D₂.π : A →ₐ[O] D₂.Q) (Coalgebra.comul (R := O) b) := rfl

noncomputable def lam : D₁.Q ⊗[O] D₂.Q →ₐ[O] A :=
  Algebra.TensorProduct.lift (D₁.ι : D₁.Q →ₐ[O] A) (D₂.ι : D₂.Q →ₐ[O] A) fun _ _ => Commute.all _ _

theorem lam_tmul (q₁ : D₁.Q) (q₂ : D₂.Q) : lam D₁ D₂ (q₁ ⊗ₜ[O] q₂) = D₁.ι q₁ * D₂.ι q₂ :=
  Algebra.TensorProduct.lift_tmul _ _ _ q₁ q₂

theorem lam_eq_lmul'_comp_map : lam D₁ D₂ =
    (Algebra.TensorProduct.lmul' O (S := A)).comp (Algebra.TensorProduct.map (D₁.ι : D₁.Q →ₐ[O] A) (D₂.ι : D₂.Q →ₐ[O] A)) := by
  apply Algebra.TensorProduct.ext'
  intro q₁ q₂
  rw [lam_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
  rfl

variable (hsum : WithConv.toConv (ε : A →ₐ[O] A) * WithConv.toConv (ε' : A →ₐ[O] A) = WithConv.toConv (AlgHom.id O A))

include hsum in

theorem lam_theta (b : A) : lam D₁ D₂ (theta D₁ D₂ b) = b := by
  have h := congrArg (fun f : WithConv (A →ₐ[O] A) => f.ofConv b) hsum
  simp only [AlgHom.convMul_def, WithConv.ofConv_toConv, AlgHom.comp_apply, AlgHom.id_apply] at h
  rw [theta_apply, lam_eq_lmul'_comp_map, AlgHom.comp_apply, algMap_algMap]
  have h1 : ((D₁.ι : D₁.Q →ₐ[O] A).comp (D₁.π : A →ₐ[O] D₁.Q)) = (ε : A →ₐ[O] A) :=
    AlgHom.ext fun a => D₁.ι_π a
  have h2 : ((D₂.ι : D₂.Q →ₐ[O] A).comp (D₂.π : A →ₐ[O] D₂.Q)) = (ε' : A →ₐ[O] A) :=
    AlgHom.ext fun a => D₂.ι_π a
  rw [h1, h2]
  exact h

variable (hε : ε.comp ε = ε) (hε' : ε'.comp ε' = ε')
  (hεε' : (ε : A →ₐ[O] A).comp (ε' : A →ₐ[O] A) = (Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A))
  (hε'ε : (ε' : A →ₐ[O] A).comp (ε : A →ₐ[O] A) = (Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A))

include hε'ε in

theorem π₂_ε (a : A) : D₂.π (ε a) = algebraMap O D₂.Q (Coalgebra.counit (R := O) a) := by
  apply D₂.ι_injective
  rw [D₂.ι_π, AlgHomClass.commutes]
  have := AlgHom.congr_fun hε'ε a
  simpa only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply] using this

include hεε' in
theorem π₁_ε' (a : A) : D₁.π (ε' a) = algebraMap O D₁.Q (Coalgebra.counit (R := O) a) := by
  apply D₁.ι_injective
  rw [D₁.ι_π, AlgHomClass.commutes]
  have := AlgHom.congr_fun hεε' a
  simpa only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply] using this

include hε hε'ε in
theorem theta_ι₁ (q : D₁.Q) : theta D₁ D₂ (D₁.ι q) = q ⊗ₜ[O] 1 := by
  obtain ⟨a, rfl⟩ := D₁.π_surjective q
  rw [D₁.ι_π, theta_apply, comul_bialgHom, algMap_algMap]
  have h1 : ((D₁.π : A →ₐ[O] D₁.Q).comp (ε : A →ₐ[O] A)) = (D₁.π : A →ₐ[O] D₁.Q) := by
    apply AlgHom.ext; intro x
    show D₁.π (ε x) = D₁.π x
    rw [← D₁.ι_π, ImageDatum.π_ι _ hε]
  have h2 : ((D₂.π : A →ₐ[O] D₂.Q).comp (ε : A →ₐ[O] A)) = (Algebra.ofId O D₂.Q).comp (Bialgebra.counitAlgHom O A) := by
    apply AlgHom.ext; intro x
    exact π₂_ε D₂ hε'ε x
  rw [h1, h2, algMap_eq]

  have key : TensorProduct.map (D₁.π : A →ₐ[O] D₁.Q).toLinearMap
      ((Algebra.ofId O D₂.Q).comp (Bialgebra.counitAlgHom O A)).toLinearMap =
      (TensorProduct.map (D₁.π : A →ₐ[O] D₁.Q).toLinearMap (Algebra.linearMap O D₂.Q)) ∘ₗ
        (LinearMap.lTensor A (Coalgebra.counit (R := O) (A := A))) := by
    rw [LinearMap.lTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
    rfl
  rw [key, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul, TensorProduct.map_tmul]
  simp

include hε' hεε' in
theorem theta_ι₂ (q : D₂.Q) : theta D₁ D₂ (D₂.ι q) = 1 ⊗ₜ[O] q := by
  obtain ⟨a, rfl⟩ := D₂.π_surjective q
  rw [D₂.ι_π, theta_apply, comul_bialgHom, algMap_algMap]
  have h1 : ((D₂.π : A →ₐ[O] D₂.Q).comp (ε' : A →ₐ[O] A)) = (D₂.π : A →ₐ[O] D₂.Q) := by
    apply AlgHom.ext; intro x
    show D₂.π (ε' x) = D₂.π x
    rw [← D₂.ι_π, ImageDatum.π_ι _ hε']
  have h2 : ((D₁.π : A →ₐ[O] D₁.Q).comp (ε' : A →ₐ[O] A)) = (Algebra.ofId O D₁.Q).comp (Bialgebra.counitAlgHom O A) := by
    apply AlgHom.ext; intro x
    exact π₁_ε' D₁ hεε' x
  rw [h1, h2, algMap_eq]
  have key : TensorProduct.map ((Algebra.ofId O D₁.Q).comp (Bialgebra.counitAlgHom O A)).toLinearMap
      (D₂.π : A →ₐ[O] D₂.Q).toLinearMap =
      (TensorProduct.map (Algebra.linearMap O D₁.Q) (D₂.π : A →ₐ[O] D₂.Q).toLinearMap) ∘ₗ
        (LinearMap.rTensor A (Coalgebra.counit (R := O) (A := A))) := by
    rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
    rfl
  rw [key, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
  simp

include hε hε' hεε' hε'ε in
theorem theta_lam (t : D₁.Q ⊗[O] D₂.Q) : theta D₁ D₂ (lam D₁ D₂ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul q₁ q₂ =>
    rw [lam_tmul, map_mul, theta_ι₁ D₁ D₂ hε hε'ε, theta_ι₂ D₁ D₂ hε' hεε', Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

include hsum hε hε' hεε' hε'ε in
theorem theta_bijective : Function.Bijective (theta D₁ D₂) :=
  Function.bijective_iff_has_inverse.2 ⟨lam D₁ D₂, lam_theta D₁ D₂ hsum, theta_lam D₁ D₂ hε hε' hεε' hε'ε⟩

end Theta
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.S42SLP.ImageDatum"

end S42SLP
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.S42SLP.ImageDatum P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self.S42SLP"

open S42SLP in
theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O (AlgebraicClosure ℚ)]
    {h : ℕ} (H : PDivisibleGroup O p h)
    (ε ε' : ∀ v : ℕ, H.level v →ₐc[O] H.level v)
    (hε : ∀ v, (ε v).comp (ε v) = ε v) (hε' : ∀ v, (ε' v).comp (ε' v) = ε' v)
    (hεε' : ∀ v, (ε v : H.level v →ₐ[O] H.level v).comp (ε' v : H.level v →ₐ[O] H.level v) =
      (Algebra.ofId O (H.level v)).comp (Bialgebra.counitAlgHom O (H.level v)))
    (hε'ε : ∀ v, (ε' v : H.level v →ₐ[O] H.level v).comp (ε v : H.level v →ₐ[O] H.level v) =
      (Algebra.ofId O (H.level v)).comp (Bialgebra.counitAlgHom O (H.level v)))
    (hsum : ∀ v, WithConv.toConv (ε v : H.level v →ₐ[O] H.level v) *
        WithConv.toConv (ε' v : H.level v →ₐ[O] H.level v) =
      WithConv.toConv (AlgHom.id O (H.level v)))
    (hεt : ∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hε't : ∀ v, (H.transition v).comp (ε' (v + 1)) = (ε' v).comp (H.transition v))
    (h₁ h₂ : ℕ) (hh : h₁ + h₂ = h)
    (hcard₁ : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
        (PDivisibleGroup.Point.toAlgHom x).comp (ε v : H.level v →ₐ[O] H.level v) =
          PDivisibleGroup.Point.toAlgHom x} = p ^ (v * h₁))
    (hcard₂ : ∀ v, Nat.card {x : H.Point (AlgebraicClosure ℚ) v //
        (PDivisibleGroup.Point.toAlgHom x).comp (ε' v : H.level v →ₐ[O] H.level v) =
          PDivisibleGroup.Point.toAlgHom x} = p ^ (v * h₂)) :
    ∃ (H₁ : PDivisibleGroup O p h₁) (H₂ : PDivisibleGroup O p h₂)
      (π₁ : ∀ v, H.level v →ₐc[O] H₁.level v) (π₂ : ∀ v, H.level v →ₐc[O] H₂.level v)
      (σ₁ : ∀ v, H₁.level v →ₐ[O] H.level v) (σ₂ : ∀ v, H₂.level v →ₐ[O] H.level v)
      (Θ : ∀ v, H.level v →ₐc[O] H₁.level v ⊗[O] H₂.level v),
      (∀ v, Function.Surjective (π₁ v)) ∧ (∀ v, Function.Surjective (π₂ v)) ∧
      (∀ v, (π₁ v).comp (H.transition v) = (H₁.transition v).comp (π₁ (v + 1))) ∧
      (∀ v, (π₂ v).comp (H.transition v) = (H₂.transition v).comp (π₂ (v + 1))) ∧
      (∀ v, (π₁ v : H.level v →ₐ[O] H₁.level v).comp (σ₁ v) = AlgHom.id O (H₁.level v)) ∧
      (∀ v, (σ₁ v).comp (π₁ v : H.level v →ₐ[O] H₁.level v) = (ε v : H.level v →ₐ[O] H.level v)) ∧
      (∀ v, (π₂ v : H.level v →ₐ[O] H₂.level v).comp (σ₂ v) = AlgHom.id O (H₂.level v)) ∧
      (∀ v, (σ₂ v).comp (π₂ v : H.level v →ₐ[O] H₂.level v) = (ε' v : H.level v →ₐ[O] H.level v)) ∧
      (∀ v, Function.Bijective (Θ v)) ∧
      (∀ v b, Θ v b = Algebra.TensorProduct.map (π₁ v : H.level v →ₐ[O] H₁.level v)
        (π₂ v : H.level v →ₐ[O] H₂.level v) (Coalgebra.comul (R := O) b)) := by
  classical
  let D₁ : ∀ v, ImageDatum (ε v) := fun v => Classical.choice (ImageDatum.nonempty (ε v))
  let D₂ : ∀ v, ImageDatum (ε' v) := fun v => Classical.choice (ImageDatum.nonempty (ε' v))
  refine ⟨subGroup H ε hε hεt h₁ hcard₁ D₁, subGroup H ε' hε' hε't h₂ hcard₂ D₂,
    fun v => (D₁ v).π, fun v => (D₂ v).π,
    fun v => ((D₁ v).ι : (D₁ v).Q →ₐ[O] H.level v), fun v => ((D₂ v).ι : (D₂ v).Q →ₐ[O] H.level v),
    fun v => theta (D₁ v) (D₂ v),
    fun v => (D₁ v).π_surjective, fun v => (D₂ v).π_surjective,
    fun v => (subTransition_comp_π H ε hε hεt D₁ v).symm, fun v => (subTransition_comp_π H ε' hε' hε't D₂ v).symm,
    fun v => AlgHom.ext fun q => (D₁ v).π_ι (hε v) q, fun v => AlgHom.ext fun a => (D₁ v).ι_π a,
    fun v => AlgHom.ext fun q => (D₂ v).π_ι (hε' v) q, fun v => AlgHom.ext fun a => (D₂ v).ι_π a,
    fun v => theta_bijective (D₁ v) (D₂ v) (hsum v) (hε v) (hε' v) (hεε' v) (hε'ε v),
    fun v b => rfl⟩

end S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self
end P2MW
export P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self (solution)
