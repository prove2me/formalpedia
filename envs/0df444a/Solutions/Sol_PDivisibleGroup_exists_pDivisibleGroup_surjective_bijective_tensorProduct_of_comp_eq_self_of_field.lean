-- Prove2me | solution 1 for PDivisibleGroup.exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d091b021-66d7-569c-a3d1-f742a1901f5b

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Tower
import Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
import Theorems.Thm_HopfAlgebra_finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v w

set_option linter.unusedSectionVars false

namespace S42TowersHopf

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

end ImageDatum
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.S42TowersHopf.ImageDatum"

end Image
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.S42TowersHopf.ImageDatum"

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
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.S42TowersHopf.ImageDatum"

section SubTower

variable {p : ℕ} {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {h : ℕ} (H : PDivisibleGroup R p h)
  (ε : ∀ v : ℕ, H.level v →ₐc[R] H.level v)
  (hε : ∀ v, (ε v).comp (ε v) = ε v)
  (hεt : ∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
  (D : ∀ v, ImageDatum (ε v))

noncomputable def subTransition (v : ℕ) : (D (v + 1)).Q →ₐc[R] (D v).Q :=
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
    RingHom.ker (subTransition H ε D v) = PDivisibleGroup.Hopf.torsionIdeal R (D (v + 1)).Q (p ^ v) := by
  have hπ' := (D (v + 1)).π_surjective

  have h1 : RingHom.ker (subTransition H ε D v : (D (v + 1)).Q →ₐ[R] (D v).Q) =
      Ideal.map ((D (v + 1)).π : H.level (v + 1) →ₐ[R] (D (v + 1)).Q)
        (RingHom.ker (((D v).π : H.level v →ₐ[R] (D v).Q).comp (H.transition v : H.level (v + 1) →ₐ[R] H.level v))) := by
    refine ker_eq_map_of_comp_eq hπ' ?_
    apply AlgHom.ext
    intro a
    exact DFunLike.congr_fun (subTransition_comp_π H ε hε hεt D v) a

  rw [← map_torsionIdeal_eq (D (v + 1)).π hπ', ← H.ker_transition]
  change RingHom.ker (subTransition H ε D v : (D (v + 1)).Q →ₐ[R] (D v).Q) = _
  rw [h1]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [RingHom.mem_ker, AlgHom.comp_apply] at hx
    rw [Ideal.mem_comap]

    have hεx : H.transition v (ε (v + 1) x) = 0 := by
      rw [← BialgHom.comp_apply, hεt, BialgHom.comp_apply, ← (D v).ι_π]
      show (D v).ι (((D v).π : H.level v →ₐ[R] (D v).Q) ((H.transition v : H.level (v + 1) →ₐ[R] H.level v) x)) = 0
      rw [hx, map_zero]
    have hx' : ((D (v + 1)).π : H.level (v + 1) →ₐ[R] (D (v + 1)).Q) x = (D (v + 1)).π (ε (v + 1) x) := by
      show (D (v + 1)).π x = (D (v + 1)).π (ε (v + 1) x)
      rw [← (D (v + 1)).ι_π, ImageDatum.π_ι _ (hε (v + 1))]
    rw [hx']
    exact Ideal.mem_map_of_mem _ hεx
  · exact Ideal.map_mono fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [AlgHom.comp_apply]
      show (D v).π (H.transition v x) = 0
      rw [hx, map_zero]

noncomputable def subGroup (h₁ : ℕ) (hrank : ∀ v, Module.finrank R (D v).Q = p ^ (v * h₁)) :
    PDivisibleGroup R p h₁ where
  level v := (D v).Q
  instIsCocomm v := (D v).isCocomm
  transition := subTransition H ε D
  transition_surjective := subTransition_surjective H ε hε hεt D
  finrank_level := hrank
  ker_transition := ker_subTransition H ε hε hεt D

end SubTower
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.S42TowersHopf.ImageDatum"

section TowerRank

variable {F : Type} [Field F] {p : ℕ}
  {L : ℕ → Type} [∀ w, CommRing (L w)] [∀ w, HopfAlgebra F (L w)] [∀ w, Coalgebra.IsCocomm F (L w)]
  [∀ w, Module.Finite F (L w)]
  (t : ∀ w, L (w + 1) →ₐc[F] L w)
  (ht : ∀ w, Function.Surjective (t w))
  (hkerL : ∀ w, RingHom.ker (t w) = PDivisibleGroup.Hopf.torsionIdeal F (L (w + 1)) (p ^ w))

include ht hkerL in

theorem finrank_succ_le (v : ℕ) :
    Module.finrank F (L (v + 1)) ≤ Module.finrank F (L 1) * Module.finrank F (L v) := by
  classical
  let φ : L (v + 1) →ₐc[F] L (v + 1) := PDivisibleGroup.Hopf.nsmulBialgHom F (L (v + 1)) p
  have h5 := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range F φ
  have hφ : (φ : L (v + 1) →ₐ[F] L (v + 1)) = PDivisibleGroup.Hopf.nsmulAlgHom F (L (v + 1)) p :=
    PDivisibleGroup.Hopf.toAlgHom_nsmulBialgHom F (L (v + 1)) p
  have hI : Ideal.map (φ : L (v + 1) →ₐ[F] L (v + 1)) (RingHom.ker (Bialgebra.counitAlgHom F (L (v + 1)))) =
      PDivisibleGroup.Hopf.torsionIdeal F (L (v + 1)) (p ^ 1) := by
    rw [hφ, pow_one]; rfl
  have h1le : 1 ≤ v + 1 := Nat.le_add_left 1 v
  have hTs := PDivisibleGroup.Tower.transitionOfLE_surjective t ht 1 (v + 1) h1le
  have hT : RingHom.ker (PDivisibleGroup.Tower.transitionOfLE t 1 (v + 1) h1le : L (v + 1) →ₐ[F] L 1) =
      PDivisibleGroup.Hopf.torsionIdeal F (L (v + 1)) (p ^ 1) :=
    PDivisibleGroup.Tower.ker_transitionOfLE ht hkerL 1 (v + 1) h1le

  have hq : Module.finrank F (L (v + 1) ⧸ Ideal.map (φ : L (v + 1) →ₐ[F] L (v + 1))
      (RingHom.ker (Bialgebra.counitAlgHom F (L (v + 1))))) = Module.finrank F (L 1) := by
    rw [(Ideal.quotientEquivAlgOfEq F hI).toLinearEquiv.finrank_eq,
      ← (Ideal.quotientEquivAlgOfEq F hT).toLinearEquiv.finrank_eq]
    exact (Ideal.quotientKerAlgEquivOfSurjective hTs).toLinearEquiv.finrank_eq

  have hker : LinearMap.ker (t v : L (v + 1) →ₐ[F] L v).toLinearMap ≤
      LinearMap.ker (φ : L (v + 1) →ₐ[F] L (v + 1)).toLinearMap := by
    intro x hx
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply] at hx ⊢
    have hx' : x ∈ PDivisibleGroup.Hopf.torsionIdeal F (L (v + 1)) (p ^ v) := by
      rw [← hkerL v]; exact hx
    rw [hφ]
    have hle : PDivisibleGroup.Hopf.torsionIdeal F (L (v + 1)) (p ^ v) ≤
        RingHom.ker (PDivisibleGroup.Hopf.nsmulAlgHom F (L (v + 1)) p) := by
      rw [PDivisibleGroup.Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker, PDivisibleGroup.Hopf.nsmulAlgHom_nsmulAlgHom_apply, ← pow_succ',
        PDivisibleGroup.Tower.nsmulAlgHom_pow_apply ht hkerL (v + 1) y,
        (PDivisibleGroup.Hopf.mem_augIdeal_iff F _ y).1 hy, map_zero]
    exact hle hx'
  have e1 := LinearMap.finrank_range_add_finrank_ker (φ : L (v + 1) →ₐ[F] L (v + 1)).toLinearMap
  have e2 := LinearMap.finrank_range_add_finrank_ker (t v : L (v + 1) →ₐ[F] L v).toLinearMap
  have e3 : Module.finrank F ↥(LinearMap.range (t v : L (v + 1) →ₐ[F] L v).toLinearMap) =
      Module.finrank F (L v) := by
    have htop : LinearMap.range (t v : L (v + 1) →ₐ[F] L v).toLinearMap = ⊤ := LinearMap.range_eq_top.2 (ht v)
    rw [htop, finrank_top]
  have e4 := Submodule.finrank_mono hker
  have e5 : Module.finrank F ↥(φ : L (v + 1) →ₐ[F] L (v + 1)).range =
      Module.finrank F ↥(LinearMap.range (φ : L (v + 1) →ₐ[F] L (v + 1)).toLinearMap) := by
    rw [← Subalgebra.finrank_toSubmodule]
    have hs : Subalgebra.toSubmodule (φ : L (v + 1) →ₐ[F] L (v + 1)).range =
        LinearMap.range (φ : L (v + 1) →ₐ[F] L (v + 1)).toLinearMap := by
      ext x
      rw [Subalgebra.mem_toSubmodule, AlgHom.mem_range, LinearMap.mem_range]
      rfl
    rw [hs]
  have hr : Module.finrank F ↥(φ : L (v + 1) →ₐ[F] L (v + 1)).range ≤ Module.finrank F (L v) := by omega
  rw [h5, hq]
  exact Nat.mul_le_mul_left _ hr

end TowerRank
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.S42TowersHopf.ImageDatum"

theorem eq_and_eq_of_mul_eq_mul_of_le {x X y Y : ℕ} (hx : x ≤ X) (hy : y ≤ Y) (hxy : x * y = X * Y)
    (hX : 0 < X) (hY : 0 < Y) : x = X ∧ y = Y := by
  have hy0 : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · rw [h0, mul_zero] at hxy; exact absurd hxy.symm (Nat.mul_ne_zero hX.ne' hY.ne')
    · exact h0
  have hxX : x = X := by
    refine le_antisymm hx ?_
    have h1 : X * Y ≤ x * Y := by rw [← hxy]; exact Nat.mul_le_mul_left _ hy
    exact Nat.le_of_mul_le_mul_right h1 hY
  refine ⟨hxX, le_antisymm hy ?_⟩
  have h2 : X * Y ≤ X * y := by rw [← hxy, hxX]
  exact Nat.le_of_mul_le_mul_left h2 hX

theorem exists_heights_of_mul_eq_pow {p h : ℕ} (hp : p.Prime) (a b : ℕ → ℕ)
    (hab : ∀ v, a v * b v = p ^ (v * h))
    (ha : ∀ v, a (v + 1) ≤ a 1 * a v) (hb : ∀ v, b (v + 1) ≤ b 1 * b v) :
    ∃ h₁ h₂ : ℕ, h₁ + h₂ = h ∧ (∀ v, a v = p ^ (v * h₁)) ∧ (∀ v, b v = p ^ (v * h₂)) := by
  have h1 : a 1 * b 1 = p ^ h := by rw [hab 1, one_mul]
  obtain ⟨h₁, -, hh₁⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ h1)
  obtain ⟨h₂, -, hh₂⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ h1)
  have hsum : h₁ + h₂ = h := by
    apply Nat.pow_right_injective hp.two_le
    show p ^ (h₁ + h₂) = p ^ h
    rw [pow_add, ← hh₁, ← hh₂, h1]
  refine ⟨h₁, h₂, hsum, ?_⟩
  have key : ∀ v, a v = p ^ (v * h₁) ∧ b v = p ^ (v * h₂) := by
    intro v
    induction v with
    | zero =>
      have h0 : a 0 * b 0 = 1 := by rw [hab 0, zero_mul, pow_zero]
      rw [zero_mul, zero_mul, pow_zero]
      exact ⟨Nat.eq_one_of_mul_eq_one_right h0, Nat.eq_one_of_mul_eq_one_left h0⟩
    | succ v ih =>
      obtain ⟨iha, ihb⟩ := ih
      have hA : a 1 * a v = p ^ ((v + 1) * h₁) := by rw [hh₁, iha, ← pow_add, add_mul, one_mul, add_comm]
      have hB : b 1 * b v = p ^ ((v + 1) * h₂) := by rw [hh₂, ihb, ← pow_add, add_mul, one_mul, add_comm]
      have hprod : a (v + 1) * b (v + 1) = (a 1 * a v) * (b 1 * b v) := by
        rw [hab, hA, hB, ← pow_add, ← hsum]
        congr 1
        ring
      have hpos : 0 < p := hp.pos
      obtain ⟨h3, h4⟩ := eq_and_eq_of_mul_eq_mul_of_le (ha v) (hb v) hprod
        (by rw [hA]; exact pow_pos hpos _) (by rw [hB]; exact pow_pos hpos _)
      exact ⟨h3.trans hA, h4.trans hB⟩
  exact ⟨fun v => (key v).1, fun v => (key v).2⟩

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
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.S42TowersHopf.ImageDatum"

end S42TowersHopf
p2m_reactivate "P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.S42TowersHopf.ImageDatum P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field.S42TowersHopf"

open S42TowersHopf in

theorem solution
    {F : Type} [Field F] (p : ℕ) [Fact p.Prime]
    {h : ℕ} (H : PDivisibleGroup F p h)
    (ε ε' : ∀ v : ℕ, H.level v →ₐc[F] H.level v)
    (hε : ∀ v, (ε v).comp (ε v) = ε v) (hε' : ∀ v, (ε' v).comp (ε' v) = ε' v)
    (hεε' : ∀ v, (ε v : H.level v →ₐ[F] H.level v).comp (ε' v : H.level v →ₐ[F] H.level v) =
      (Algebra.ofId F (H.level v)).comp (Bialgebra.counitAlgHom F (H.level v)))
    (hε'ε : ∀ v, (ε' v : H.level v →ₐ[F] H.level v).comp (ε v : H.level v →ₐ[F] H.level v) =
      (Algebra.ofId F (H.level v)).comp (Bialgebra.counitAlgHom F (H.level v)))
    (hsum : ∀ v, WithConv.toConv (ε v : H.level v →ₐ[F] H.level v) *
        WithConv.toConv (ε' v : H.level v →ₐ[F] H.level v) =
      WithConv.toConv (AlgHom.id F (H.level v)))
    (hεt : ∀ v, (H.transition v).comp (ε (v + 1)) = (ε v).comp (H.transition v))
    (hε't : ∀ v, (H.transition v).comp (ε' (v + 1)) = (ε' v).comp (H.transition v)) :
    ∃ (h₁ h₂ : ℕ), h₁ + h₂ = h ∧
    ∃ (H₁ : PDivisibleGroup F p h₁) (H₂ : PDivisibleGroup F p h₂)
      (π₁ : ∀ v, H.level v →ₐc[F] H₁.level v) (π₂ : ∀ v, H.level v →ₐc[F] H₂.level v)
      (σ₁ : ∀ v, H₁.level v →ₐ[F] H.level v) (σ₂ : ∀ v, H₂.level v →ₐ[F] H.level v)
      (Θ : ∀ v, H.level v →ₐc[F] H₁.level v ⊗[F] H₂.level v),
      (∀ v, Function.Surjective (π₁ v)) ∧ (∀ v, Function.Surjective (π₂ v)) ∧
      (∀ v, (π₁ v).comp (H.transition v) = (H₁.transition v).comp (π₁ (v + 1))) ∧
      (∀ v, (π₂ v).comp (H.transition v) = (H₂.transition v).comp (π₂ (v + 1))) ∧
      (∀ v, (π₁ v : H.level v →ₐ[F] H₁.level v).comp (σ₁ v) = AlgHom.id F (H₁.level v)) ∧
      (∀ v, (σ₁ v).comp (π₁ v : H.level v →ₐ[F] H₁.level v) = (ε v : H.level v →ₐ[F] H.level v)) ∧
      (∀ v, (π₂ v : H.level v →ₐ[F] H₂.level v).comp (σ₂ v) = AlgHom.id F (H₂.level v)) ∧
      (∀ v, (σ₂ v).comp (π₂ v : H.level v →ₐ[F] H₂.level v) = (ε' v : H.level v →ₐ[F] H.level v)) ∧
      (∀ v, Function.Bijective (Θ v)) ∧
      (∀ v b, Θ v b = Algebra.TensorProduct.map (π₁ v : H.level v →ₐ[F] H₁.level v)
        (π₂ v : H.level v →ₐ[F] H₂.level v) (Coalgebra.comul (R := F) b)) := by
  classical
  let D₁ : ∀ v, ImageDatum (ε v) := fun v => Classical.choice (ImageDatum.nonempty (ε v))
  let D₂ : ∀ v, ImageDatum (ε' v) := fun v => Classical.choice (ImageDatum.nonempty (ε' v))
  haveI hc₁ : ∀ v, Coalgebra.IsCocomm F (D₁ v).Q := fun v => (D₁ v).isCocomm
  haveI hc₂ : ∀ v, Coalgebra.IsCocomm F (D₂ v).Q := fun v => (D₂ v).isCocomm

  have hprod : ∀ v, Module.finrank F (D₁ v).Q * Module.finrank F (D₂ v).Q = p ^ (v * h) := fun v => by
    rw [← H.finrank_level v, ← Module.finrank_tensorProduct]
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofBijective
      ((theta (D₁ v) (D₂ v) : H.level v →ₐ[F] (D₁ v).Q ⊗[F] (D₂ v).Q).toLinearMap)
      (theta_bijective (D₁ v) (D₂ v) (hsum v) (hε v) (hε' v) (hεε' v) (hε'ε v)))).symm

  have ha : ∀ v, Module.finrank F (D₁ (v + 1)).Q ≤ Module.finrank F (D₁ 1).Q * Module.finrank F (D₁ v).Q :=
    fun v => finrank_succ_le (L := fun w => (D₁ w).Q) (subTransition H ε D₁)
      (subTransition_surjective H ε hε hεt D₁) (ker_subTransition H ε hε hεt D₁) v
  have hb : ∀ v, Module.finrank F (D₂ (v + 1)).Q ≤ Module.finrank F (D₂ 1).Q * Module.finrank F (D₂ v).Q :=
    fun v => finrank_succ_le (L := fun w => (D₂ w).Q) (subTransition H ε' D₂)
      (subTransition_surjective H ε' hε' hε't D₂) (ker_subTransition H ε' hε' hε't D₂) v
  obtain ⟨h₁, h₂, hh, hr₁, hr₂⟩ := exists_heights_of_mul_eq_pow (Fact.out : p.Prime)
    (fun v => Module.finrank F (D₁ v).Q) (fun v => Module.finrank F (D₂ v).Q) hprod ha hb
  refine ⟨h₁, h₂, hh, subGroup H ε hε hεt D₁ h₁ hr₁, subGroup H ε' hε' hε't D₂ h₂ hr₂,
    fun v => (D₁ v).π, fun v => (D₂ v).π,
    fun v => ((D₁ v).ι : (D₁ v).Q →ₐ[F] H.level v), fun v => ((D₂ v).ι : (D₂ v).Q →ₐ[F] H.level v),
    fun v => theta (D₁ v) (D₂ v),
    fun v => (D₁ v).π_surjective, fun v => (D₂ v).π_surjective,
    fun v => (subTransition_comp_π H ε hε hεt D₁ v).symm, fun v => (subTransition_comp_π H ε' hε' hε't D₂ v).symm,
    fun v => AlgHom.ext fun q => (D₁ v).π_ι (hε v) q, fun v => AlgHom.ext fun a => (D₁ v).ι_π a,
    fun v => AlgHom.ext fun q => (D₂ v).π_ι (hε' v) q, fun v => AlgHom.ext fun a => (D₂ v).ι_π a,
    fun v => theta_bijective (D₁ v) (D₂ v) (hsum v) (hε v) (hε' v) (hεε' v) (hε'ε v),
    fun v b => rfl⟩

end S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field
end P2MW
export P2MW.S_PDivisibleGroup_exists_pDivisibleGroup_surjective_bijective_tensorProduct_of_comp_eq_self_of_field (solution)
