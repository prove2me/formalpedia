-- Prove2me | solution 1 for PDivisibleGroup.exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/e6c563de-e071-5b54-b33e-4f5d272de403

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_PDivisibleGroup_Tower
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed
import Theorems.Thm_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers

set_option autoImplicit false

open scoped TensorProduct

universe u v w
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws47
namespace Gamma

open HopfAlgebra PDivisibleGroup PDivisibleGroup.Tower PDivisibleGroup.Hopf

theorem nsmulAlgHom_pow_mem_hopfKer_transitionLE
    {R : Type} [CommRing R] (p i₀ : ℕ)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)] [∀ w, Coalgebra.IsCocomm R (B w)]
    (t : ∀ w, B (w + 1) →ₐc[R] B w)
    (hkill₀ : ∀ b : B i₀, PDivisibleGroup.Hopf.nsmulAlgHom R (B i₀) (p ^ i₀) b = algebraMap R (B i₀) (Coalgebra.counit b))
    (v : ℕ) (b : B (i₀ + v)) :
    PDivisibleGroup.Hopf.nsmulAlgHom R (B (i₀ + v)) (p ^ i₀) b ∈ HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v) := by
  set N := nsmulAlgHom R (B (i₀ + v)) (p ^ i₀) with hN
  set T := transitionLE t i₀ v with hT

  have hTN : ∀ x : B (i₀ + v), T (N x) = algebraMap R (B i₀) (Coalgebra.counit (R := R) x) := by
    intro x
    rw [hN, ← nsmulAlgHom_bialgHom_apply T (p ^ i₀) x, hkill₀, hT, counit_transitionLE]
  rw [mem_hopfKer_iff, coaction_apply]

  have hΔ : Coalgebra.comul (R := R) (N b) =
      Algebra.TensorProduct.map N N (Coalgebra.comul (R := R) b) := by
    have h := DFunLike.congr_fun (map_comp_comulAlgHom_nsmulAlgHom R (B (i₀ + v)) (p ^ i₀)) b
    simpa using h.symm
  rw [hΔ]

  have key : ∀ x : B (i₀ + v) ⊗[R] B (i₀ + v),
      Algebra.TensorProduct.map (AlgHom.id R (B (i₀ + v))) (T : B (i₀ + v) →ₐ[R] B i₀) (Algebra.TensorProduct.map N N x) =
        TensorProduct.map N.toLinearMap (Algebra.linearMap R (B i₀)) ((Coalgebra.counit (R := R) (A := B (i₀ + v))).lTensor (B (i₀ + v)) x) := by
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c d =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
        Algebra.linearMap_apply, AlgHom.toLinearMap_apply]
      show N c ⊗ₜ[R] T (N d) = N c ⊗ₜ[R] algebraMap R (B i₀) (Coalgebra.counit (R := R) d)
      rw [hTN]
  rw [key, Coalgebra.lTensor_counit_comul, TensorProduct.map_tmul, Algebra.linearMap_apply, map_one]
  rfl

end Ws47.Gamma

open HopfAlgebra PDivisibleGroup PDivisibleGroup.Tower PDivisibleGroup.Hopf in
theorem Ws47.PHI.exists_bialgHom_coe_eq
    {R : Type} [CommRing R] (p h i₀ : ℕ) (G : PDivisibleGroup R p h)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (π : ∀ w, G.level w →ₐc[R] B w)
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra R (L v)]
    [∀ v, Coalgebra.IsCocomm R (L v)] [∀ v, Module.Free R (L v)] [∀ v, Module.Finite R (L v)]
    (ι : ∀ v, L v →ₐc[R] B (i₀ + v)) (hιinj : ∀ v, Function.Injective (ι v))
    (φ : ∀ v, G.level v →ₐ[R] L v)
    (hdef : ∀ (v : ℕ) (a' : G.level (i₀ + v)),
      ι v (φ v (PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) a')) =
        π (i₀ + v) (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (i₀ + v)) (p ^ i₀) a')) :
    ∃ φc : ∀ v, G.level v →ₐc[R] L v, ∀ v, (φc v : G.level v →ₐ[R] L v) = φ v := by
  classical
  haveI : ∀ w, Module.Flat R (B w) := fun w => inferInstance
  haveI : ∀ v, Module.Flat R (L v) := fun v => inferInstance
  have main : ∀ v, ∃ φc : G.level v →ₐc[R] L v, (φc : G.level v →ₐ[R] L v) = φ v := by
    intro v
    set T : G.level (i₀ + v) →ₐc[R] G.level v := transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) with hT
    have hTs : Function.Surjective T := transitionOfLE_surjective G.transition G.transition_surjective v (i₀ + v) _
    set Q : G.level (i₀ + v) →ₐc[R] B (i₀ + v) := (π (i₀ + v)).comp (nsmulBialgHom R (G.level (i₀ + v)) (p ^ i₀)) with hQ
    have hdef' : ∀ a', ι v (φ v (T a')) = Q a' := fun a' => by
      rw [hQ, BialgHom.comp_apply, nsmulBialgHom_apply]; exact hdef v a'
    set ιₗ : L v →ₗ[R] B (i₀ + v) := (ι v).toLinearMap with hιₗ
    set φₗ : G.level v →ₗ[R] L v := (φ v).toLinearMap with hφₗ

    have hιι : Function.Injective (TensorProduct.map ιₗ ιₗ) := by
      have h1 : Function.Injective (ιₗ.lTensor (L v)) := Module.Flat.lTensor_preserves_injective_linearMap _ (hιinj v)
      have h2 : Function.Injective (ιₗ.rTensor (B (i₀ + v))) := Module.Flat.rTensor_preserves_injective_linearMap _ (hιinj v)
      rw [← LinearMap.rTensor_comp_lTensor]
      exact h2.comp h1

    have hpt : ∀ z : G.level (i₀ + v) ⊗[R] G.level (i₀ + v),
        TensorProduct.map ιₗ ιₗ (TensorProduct.map φₗ φₗ
          (TensorProduct.map (T : G.level (i₀ + v) →ₗ[R] G.level v) (T : G.level (i₀ + v) →ₗ[R] G.level v) z)) =
        TensorProduct.map (Q : G.level (i₀ + v) →ₗ[R] B (i₀ + v)) (Q : G.level (i₀ + v) →ₗ[R] B (i₀ + v)) z := by
      intro z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b =>
        simp only [TensorProduct.map_tmul]
        show ι v (φ v (T a)) ⊗ₜ[R] ι v (φ v (T b)) = Q a ⊗ₜ[R] Q b
        rw [hdef', hdef']
    refine ⟨{ φ v with
      map_smul' := fun r x => by simp
      counit_comp := ?_
      map_comp_comul := ?_ }, AlgHom.ext fun _ => rfl⟩
    ·
      ext x
      obtain ⟨a', rfl⟩ := hTs x
      show Coalgebra.counit (R := R) (φ v (T a')) = Coalgebra.counit (R := R) (T a')
      rw [← CoalgHomClass.counit_comp_apply (ι v) (φ v (T a')), hdef', CoalgHomClass.counit_comp_apply,
        CoalgHomClass.counit_comp_apply]
    ·
      ext x
      obtain ⟨a', rfl⟩ := hTs x
      apply hιι
      show TensorProduct.map ιₗ ιₗ (TensorProduct.map φₗ φₗ (Coalgebra.comul (R := R) (T a'))) =
        TensorProduct.map ιₗ ιₗ (Coalgebra.comul (R := R) (φ v (T a')))
      have eR : TensorProduct.map ιₗ ιₗ (Coalgebra.comul (R := R) (φ v (T a'))) = Coalgebra.comul (R := R) (Q a') := by
        rw [← hdef']; exact CoalgHomClass.map_comp_comul_apply (ι v) _
      have eL : Coalgebra.comul (R := R) (T a') =
          TensorProduct.map (T : G.level (i₀ + v) →ₗ[R] G.level v) (T : G.level (i₀ + v) →ₗ[R] G.level v)
            (Coalgebra.comul (R := R) a') := (CoalgHomClass.map_comp_comul_apply T a').symm
      have eQ : Coalgebra.comul (R := R) (Q a') =
          TensorProduct.map (Q : G.level (i₀ + v) →ₗ[R] B (i₀ + v)) (Q : G.level (i₀ + v) →ₗ[R] B (i₀ + v))
            (Coalgebra.comul (R := R) a') := (CoalgHomClass.map_comp_comul_apply Q a').symm
      rw [eR, eL, eQ]
      exact hpt _
  choose φc hφc using main
  exact ⟨φc, hφc⟩

namespace Ws47
namespace PHI

open HopfAlgebra PDivisibleGroup PDivisibleGroup.Tower PDivisibleGroup.Hopf

theorem hkill₀
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B v) (hπ : ∀ v, Function.Surjective (π v)) (i₀ : ℕ) :
    ∀ b : B i₀, PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (B i₀) (p ^ i₀) b = algebraMap (PadicAlgCl.ringOfIntegers p K) (B i₀) (Coalgebra.counit b) := by
  intro b
  obtain ⟨a, rfl⟩ := hπ i₀ b
  rw [PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply (π i₀) (p ^ i₀) a,
    PDivisibleGroup.Tower.nsmulAlgHom_pow_apply G.transition_surjective G.ker_transition i₀ a]
  rw [show (π i₀) (algebraMap _ (G.level i₀) (Coalgebra.counit a)) = algebraMap _ (B i₀) (Coalgebra.counit a)
      from (π i₀ : G.level i₀ →ₐ[PadicAlgCl.ringOfIntegers p K] B i₀).commutes _]
  congr 1
  exact (CoalgHomClass.counit_comp_apply (π i₀) a).symm

theorem ker_transitionOfLE_le_ker
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B v) (i₀ v : ℕ) :
    RingHom.ker (PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀)) ≤
      RingHom.ker ((π (i₀ + v) : G.level (i₀ + v) →ₐ[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v)).comp (PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀))) := by
  rw [ker_transitionOfLE G.transition_surjective G.ker_transition v (i₀ + v) _, torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker]
  show π (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ v) a)) = 0
  rw [nsmulAlgHom_nsmulAlgHom_apply, ← pow_add,
    nsmulAlgHom_pow_apply G.transition_surjective G.ker_transition (i₀ + v) a,
    (Hopf.mem_augIdeal_iff _ _ a).mp ha, map_zero, map_zero]

theorem Aux.exists_lift_of_forall_mem_range {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (ι : B →ₐ[R] C) (hι : Function.Injective ι) (g : A →ₐ[R] C)
    (hg : ∀ a, g a ∈ ι.range) : ∃ ψ : A →ₐ[R] B, ∀ a, ι (ψ a) = g a := by
  classical
  let e : B ≃ₐ[R] ι.range := AlgEquiv.ofInjective ι hι
  refine ⟨(e.symm : ι.range →ₐ[R] B).comp (g.codRestrict ι.range hg), fun a => ?_⟩
  set y : ι.range := g.codRestrict ι.range hg a with hy
  have h1 : e (e.symm y) = y := e.apply_symm_apply y
  have h2 := congrArg Subtype.val h1
  rw [AlgEquiv.ofInjective_apply] at h2
  exact h2

theorem Aux.exists_factor_of_ker_le {R A A' B : Type} [CommRing R] [CommRing A] [CommRing A'] [CommRing B]
    [Algebra R A] [Algebra R A'] [Algebra R B] (T : A →ₐ[R] A') (hT : Function.Surjective T) (ψ : A →ₐ[R] B)
    (hker : ∀ a ∈ RingHom.ker T, ψ a = 0) : ∃ φ : A' →ₐ[R] B, ∀ a, φ (T a) = ψ a := by
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker T) ψ hker).comp
    ((Ideal.quotientKerAlgEquivOfSurjective hT).symm : A' →ₐ[R] A ⧸ RingHom.ker T), fun a => ?_⟩
  rw [AlgHom.comp_apply]
  show Ideal.Quotient.liftₐ (RingHom.ker T) ψ hker ((Ideal.quotientKerAlgEquivOfSurjective hT).symm (T a)) = ψ a
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply hT a, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

theorem exists_algHom_hdef
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v)
    (m : ∀ j, B j →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p)
    (i₀ : ℕ)
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (L v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (L v)]
    (t' : ∀ v, L (v + 1) →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v) (ι : ∀ v, L v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v))
    (hιinj : ∀ v, Function.Injective (ι v))
    (hιrange : ∀ v, (ι v : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (hιt : ∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1))) :
    ∃ φ : ∀ v, G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v, ∀ (v : ℕ) (a' : G.level (i₀ + v)),
        ι v (φ v ((PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀)) a')) = π (i₀ + v) ((PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀)) a') := by
  classical

  have hland : ∀ (v : ℕ) (a' : G.level (i₀ + v)),
      ((π (i₀ + v) : G.level (i₀ + v) →ₐ[PadicAlgCl.ringOfIntegers p K] B (i₀ + v)).comp
        (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀))) a' ∈
        (ι v : L v →ₐ[PadicAlgCl.ringOfIntegers p K] B (i₀ + v)).range := by
    intro v a'
    rw [hιrange v, AlgHom.comp_apply]
    show π (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) a') ∈ _
    rw [← nsmulAlgHom_bialgHom_apply (π (i₀ + v)) (p ^ i₀) a']
    exact Ws47.Gamma.nsmulAlgHom_pow_mem_hopfKer_transitionLE p i₀ B t (hkill₀ p K G B π hπ i₀) v _
  have hψ : ∀ v, ∃ ψ : G.level (i₀ + v) →ₐ[PadicAlgCl.ringOfIntegers p K] L v,
      ∀ a', ι v (ψ a') = π (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) a') := fun v =>
    Aux.exists_lift_of_forall_mem_range _ (hιinj v) _ (hland v)
  choose ψ hψ using hψ

  have hφ : ∀ v, ∃ φ : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] L v,
      ∀ a', φ (transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) a') = ψ v a' := by
    intro v
    refine Aux.exists_factor_of_ker_le
      (transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) : G.level (i₀ + v) →ₐ[PadicAlgCl.ringOfIntegers p K] G.level v)
      (transitionOfLE_surjective G.transition G.transition_surjective v (i₀ + v) _) (ψ v) fun a ha => ?_
    apply hιinj v
    rw [hψ, map_zero]
    have := ker_transitionOfLE_le_ker p K G B π i₀ v ha
    simpa using this
  choose φ hφ using hφ
  exact ⟨φ, fun v a' => by rw [hφ, hψ]⟩

theorem comp_transition_eq_of_hdef
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v)
    (m : ∀ j, B j →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p)
    (i₀ : ℕ)
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (L v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (L v)]
    (t' : ∀ v, L (v + 1) →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v) (ι : ∀ v, L v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v))
    (hιinj : ∀ v, Function.Injective (ι v))
    (hιrange : ∀ v, (ι v : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (hιt : ∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1)))
    (φ : ∀ v, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v)
    (hdef : ∀ (v : ℕ) (a' : G.level (i₀ + v)),
        ι v ((φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) ((PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀)) a')) = π (i₀ + v) ((PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀)) a')) :
    ∀ v, (φ v).comp (G.transition v) = (t' v).comp (φ (v + 1)) := by
  intro v
  set T : ∀ w, G.level (i₀ + w) →ₐc[PadicAlgCl.ringOfIntegers p K] G.level w :=
    fun w => transitionOfLE G.transition w (i₀ + w) (Nat.le_add_left w i₀) with hT
  have hTs : Function.Surjective (T (v + 1)) :=
    transitionOfLE_surjective G.transition G.transition_surjective (v + 1) (i₀ + (v + 1)) _

  have hsq : ∀ a'' : G.level (i₀ + (v + 1)), T v (G.transition (i₀ + v) a'') = G.transition v (T (v + 1) a'') := by
    intro a''
    have h1 : transitionOfLE G.transition v (i₀ + v + 1) (by omega) =
        (T v).comp (G.transition (i₀ + v)) := transitionOfLE_succ G.transition v (i₀ + v) (Nat.le_add_left v i₀) _
    have h2 : transitionOfLE G.transition v (i₀ + v + 1) (by omega) =
        (G.transition v).comp (T (v + 1)) := transitionOfLE_eq_comp_left G.transition v (i₀ + v + 1) (by omega)
    have := DFunLike.congr_fun (h1.symm.trans h2) a''
    simpa using this
  refine BialgHom.ext fun x => ?_
  obtain ⟨a'', rfl⟩ := hTs x
  apply hιinj v
  have hl : ι v (φ v (T v (G.transition (i₀ + v) a''))) =
      π (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) (G.transition (i₀ + v) a'')) := hdef v _
  have hr : ι (v + 1) (φ (v + 1) (T (v + 1) a'')) =
      π (i₀ + v + 1) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v + 1)) (p ^ i₀) a'') := hdef (v + 1) a''
  have hιt' : ι v (t' v (φ (v + 1) (T (v + 1) a''))) = t (i₀ + v) (ι (v + 1) (φ (v + 1) (T (v + 1) a''))) :=
    DFunLike.congr_fun (hιt v) _
  have hπt' : π (i₀ + v) (G.transition (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v + 1)) (p ^ i₀) a'')) =
      t (i₀ + v) (π (i₀ + v + 1) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v + 1)) (p ^ i₀) a'')) :=
    DFunLike.congr_fun (hπt (i₀ + v)) _
  calc ι v (((φ v).comp (G.transition v)) (T (v + 1) a''))
      = ι v (φ v (T v (G.transition (i₀ + v) a''))) := by rw [BialgHom.comp_apply, ← hsq]
    _ = π (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) (G.transition (i₀ + v) a'')) := hl
    _ = π (i₀ + v) (G.transition (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v + 1)) (p ^ i₀) a'')) := by
        rw [nsmulAlgHom_bialgHom_apply]
    _ = t (i₀ + v) (π (i₀ + v + 1) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v + 1)) (p ^ i₀) a'')) := hπt'
    _ = t (i₀ + v) (ι (v + 1) (φ (v + 1) (T (v + 1) a''))) := by rw [hr]
    _ = ι v (t' v (φ (v + 1) (T (v + 1) a''))) := hιt'.symm
    _ = ι v (((t' v).comp (φ (v + 1))) (T (v + 1) a'')) := by rw [BialgHom.comp_apply]

section PTS
variable {R : Type} [CommRing R]

noncomputable def equivOfRange {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (ι : A →ₐ[R] B) (hinj : Function.Injective ι) (S : Subalgebra R B) (hS : ι.range = S) : A ≃ₐ[R] ↥S :=
  (AlgEquiv.ofInjective ι hinj).trans (Subalgebra.equivOfEq _ _ hS)

theorem coe_equivOfRange {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (ι : A →ₐ[R] B) (hinj : Function.Injective ι) (S : Subalgebra R B) (hS : ι.range = S) (a : A) :
    ((equivOfRange ι hinj S hS a : ↥S) : B) = ι a := by
  subst hS; rfl

theorem key_apply {p h i₀ v : ℕ} (G : PDivisibleGroup R p h)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    (π : ∀ w, G.level w →ₐc[R] B w) (t : ∀ w, B (w + 1) →ₐc[R] B w)
    (Lv : Type) [CommRing Lv] [HopfAlgebra R Lv]
    (ιv : Lv →ₐc[R] B (i₀ + v)) (hinj : Function.Injective ιv)
    (hrange : (ιv : Lv →ₐ[R] B (i₀ + v)).range = HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (φv : G.level v →ₐ[R] Lv)
    (hdef : ∀ a' : G.level (i₀ + v),
      ιv (φv (PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) a')) =
        π (i₀ + v) (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (i₀ + v)) (p ^ i₀) a'))
    {Ω : Type} [CommRing Ω] [Algebra R Ω] (g : B (i₀ + v) →ₐ[R] Ω) (a' : G.level (i₀ + v)) :
    ((g.comp (HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)).val).comp
        (equivOfRange (ιv : Lv →ₐ[R] B (i₀ + v)) hinj _ hrange).toAlgHom)
      (φv (PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) a')) =
      g (π (i₀ + v) (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (i₀ + v)) (p ^ i₀) a')) := by
  rw [← hdef]
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom, Subalgebra.coe_val]
  rw [coe_equivOfRange]
  rfl

theorem toAlgHom_pointInclLE {p h : ℕ} (G : PDivisibleGroup R p h) (Ω : Type) [CommRing Ω] [Algebra R Ω]
    {v w : ℕ} (hvw : v ≤ w) (x : G.Point Ω v) :
    PDivisibleGroup.Point.toAlgHom (G.pointInclLE Ω hvw x) =
      (PDivisibleGroup.Point.toAlgHom x).comp
        (PDivisibleGroup.Tower.transitionOfLE G.transition v w hvw : G.level w →ₐ[R] G.level v) := by
  induction hvw with
  | refl =>
    rw [G.pointInclLE_self, PDivisibleGroup.Tower.transitionOfLE_self]
    ext a; rfl
  | step hvw ih =>
    rw [G.pointInclLE_succ hvw, PDivisibleGroup.Tower.transitionOfLE_succ _ v _ hvw]
    ext a
    show PDivisibleGroup.Point.toAlgHom (G.pointInclLE Ω hvw x) (G.transition _ a) = _
    rw [ih]; rfl

theorem tate_compat {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h) (Ω : Type) [CommRing Ω] [Algebra R Ω]
    (x : TateModule p (G.Points Ω)) (i₀ v : ℕ)
    (f : G.Point Ω (i₀ + v)) (hf : G.pointsMkAdd Ω (i₀ + v) (Additive.ofMul f) = (x : ℕ → G.Points Ω) (i₀ + v))
    (y : G.Point Ω v) (hy : G.pointsMkAdd Ω v (Additive.ofMul y) = (x : ℕ → G.Points Ω) v) (a' : G.level (i₀ + v)) :
    (PDivisibleGroup.Point.toAlgHom f) (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (i₀ + v)) (p ^ i₀) a') =
      (PDivisibleGroup.Point.toAlgHom y)
        (PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) a') := by
  have h2 : f ^ (p ^ i₀) = G.pointInclLE Ω (Nat.le_add_left v i₀) y := by
    have hinj := G.pointsMkAdd_injective (L := Ω) (i₀ + v)
    apply_fun Additive.ofMul using Additive.ofMul.injective
    apply hinj
    rw [G.pointsMkAdd_pointInclLE, hy, ofMul_pow, map_nsmul, hf]
    have hc := TateModule.compat_pow x v i₀
    rw [Nat.add_comm v i₀] at hc
    rw [← hc, natCast_zsmul]
  have h1 : (PDivisibleGroup.Point.toAlgHom f) (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (i₀ + v)) (p ^ i₀) a')
      = PDivisibleGroup.Point.toAlgHom (f ^ (p ^ i₀)) a' :=
    (PDivisibleGroup.Hopf.pow_apply_eq_apply_nsmulAlgHom f (p ^ i₀) a').symm
  rw [h1, h2, toAlgHom_pointInclLE]
  rfl

theorem pi_transitionLE {p h : ℕ} (G : PDivisibleGroup R p h)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    (π : ∀ w, G.level w →ₐc[R] B w) (t : ∀ w, B (w + 1) →ₐc[R] B w)
    (hπt : ∀ w, (π w).comp (G.transition w) = (t w).comp (π (w + 1))) (a : ℕ) :
    ∀ (u : ℕ) (x : G.level (a + u)),
      π a (PDivisibleGroup.Tower.transitionLE G.transition a u x) = PDivisibleGroup.Tower.transitionLE t a u (π (a + u) x)
  | 0, x => rfl
  | u + 1, x => by
    rw [PDivisibleGroup.Tower.transitionLE_succ_apply, PDivisibleGroup.Tower.transitionLE_succ_apply,
      pi_transitionLE G B π t hπt a u]
    congr 1
    exact DFunLike.congr_fun (hπt (a + u)) x

theorem pi_transitionOfLE {p h : ℕ} (G : PDivisibleGroup R p h)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    (π : ∀ w, G.level w →ₐc[R] B w) (t : ∀ w, B (w + 1) →ₐc[R] B w)
    (hπt : ∀ w, (π w).comp (G.transition w) = (t w).comp (π (w + 1))) (a u : ℕ) (x : G.level (a + u)) :
    π a (PDivisibleGroup.Tower.transitionOfLE G.transition a (a + u) (Nat.le_add_right a u) x) =
      PDivisibleGroup.Tower.transitionOfLE t a (a + u) (Nat.le_add_right a u) (π (a + u) x) := by
  have h1 := PDivisibleGroup.Tower.transitionLE_eq_transitionOfLE G.transition a u
  have h2 := PDivisibleGroup.Tower.transitionLE_eq_transitionOfLE t a u
  rw [← h1, ← h2]
  exact pi_transitionLE G B π t hπt a u x

theorem exists_point_rep {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h) (Ω : Type) [CommRing Ω] [Algebra R Ω]
    (z : TateModule p (G.Points Ω)) (n : ℕ) :
    ∃ w : G.Point Ω n, G.pointsMkAdd Ω n (Additive.ofMul w) = (z : ℕ → G.Points Ω) n := by
  obtain ⟨v', x, hx⟩ := PDivisibleGroup.Points.exists_mkAdd G ((z : ℕ → G.Points Ω) n)

  set w' := G.pointInclLE Ω (le_max_right n v') x with hw'
  have hw'z : G.pointsMkAdd Ω (max n v') (Additive.ofMul w') = (z : ℕ → G.Points Ω) n := by
    rw [hw', G.pointsMkAdd_pointInclLE, hx]
  have htor : w' ^ (p ^ n) = 1 := by
    apply_fun Additive.ofMul using Additive.ofMul.injective
    apply G.pointsMkAdd_injective (L := Ω) (max n v')
    rw [ofMul_pow, map_nsmul, hw'z, ofMul_one, map_zero, ← natCast_zsmul]
    exact TateModule.torsion z n
  obtain ⟨w, hw⟩ := G.exists_pointInclLE_eq_of_pow_eq_one (le_max_left n v') w' htor
  refine ⟨w, ?_⟩
  rw [← G.pointsMkAdd_pointInclLE (le_max_left n v'), hw, hw'z]

theorem exists_factor_of_pow_eq_one {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)
    (Ω : Type) [CommRing Ω] [Algebra R Ω]
    (M : Submodule ℤ_[p] (TateModule p (G.Points Ω)))
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points Ω)), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    (π : ∀ w, G.level w →ₐc[R] B w) (t : ∀ w, B (w + 1) →ₐc[R] B w)
    (hπt : ∀ w, (π w).comp (G.transition w) = (t w).comp (π (w + 1)))
    (hpts : ∀ (w : ℕ) (g : G.Point Ω w),
        (∃ g' : B w →ₐ[R] Ω, g'.comp (π w : G.level w →ₐ[R] B w) = PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd Ω w (Additive.ofMul g) = (x : ℕ → G.Points Ω) w)
    (i₀ v : ℕ) (u : G.Point Ω (i₀ + v))
    (hu : ∃ g : B (i₀ + v) →ₐ[R] Ω, g.comp (π (i₀ + v) : G.level (i₀ + v) →ₐ[R] B (i₀ + v)) = PDivisibleGroup.Point.toAlgHom u)
    (hpow : u ^ (p ^ i₀) = 1) :
    ∃ g₀ : B i₀ →ₐ[R] Ω,
      g₀.comp (((PDivisibleGroup.Tower.transitionLE t i₀ v).comp (π (i₀ + v)) : G.level (i₀ + v) →ₐc[R] B i₀) :
        G.level (i₀ + v) →ₐ[R] B i₀) = PDivisibleGroup.Point.toAlgHom u := by
  have hp : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨x, hxM, hx⟩ := (hpts (i₀ + v) u).1 hu

  have hxv : (x : ℕ → G.Points Ω) v = 0 := by
    have hc := TateModule.compat_pow x v i₀
    rw [Nat.add_comm v i₀] at hc
    rw [← hc, natCast_zsmul, ← hx, ← map_nsmul, ← ofMul_pow, hpow, ofMul_one, map_zero]

  set z := TateModule.shiftOfProjEqZero v x hxv with hzdef
  have hz : ((p : ℤ_[p]) ^ v) • z = x := TateModule.pow_smul_shiftOfProjEqZero v x hxv
  have hzM : z ∈ M := hMsat ((p : ℤ_[p]) ^ v) z (pow_ne_zero _ hp) (by rw [hz]; exact hxM)
  have hxz : (x : ℕ → G.Points Ω) (i₀ + v) = (z : ℕ → G.Points Ω) i₀ := rfl
  obtain ⟨w, hw⟩ := exists_point_rep G Ω z i₀
  obtain ⟨g₀, hg₀⟩ := (hpts i₀ w).2 ⟨z, hzM, hw⟩

  have huw : u = G.pointInclLE Ω (Nat.le_add_right i₀ v) w := by
    apply_fun Additive.ofMul using Additive.ofMul.injective
    apply G.pointsMkAdd_injective (L := Ω) (i₀ + v)
    rw [G.pointsMkAdd_pointInclLE, hw, hx, hxz]
  refine ⟨g₀, ?_⟩
  rw [huw, toAlgHom_pointInclLE, ← hg₀]
  ext a
  show g₀ (PDivisibleGroup.Tower.transitionLE t i₀ v (π (i₀ + v) a)) =
    g₀ (π i₀ (PDivisibleGroup.Tower.transitionOfLE G.transition i₀ (i₀ + v) (Nat.le_add_right i₀ v) a))
  rw [pi_transitionOfLE G B π t hπt i₀ v a, PDivisibleGroup.Tower.transitionLE_eq_transitionOfLE]

theorem mem_mrange_convComp_iff {H K Ω : Type} [CommRing H] [Bialgebra R H] [CommRing K] [Bialgebra R K]
    [CommRing Ω] [Algebra R Ω] (π : H →ₐc[R] K) (f : H →ₐ[R] Ω) :
    (∃ g : K →ₐ[R] Ω, g.comp (π : H →ₐ[R] K) = f) ↔
      WithConv.toConv f ∈ MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω π) := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨WithConv.toConv g, by rw [PDivisibleGroup.Hopf.convCompMonoidHom_apply]; exact congrArg _ hg⟩
  · rintro ⟨g', hg'⟩
    refine ⟨g'.ofConv, ?_⟩
    rw [PDivisibleGroup.Hopf.convCompMonoidHom_apply] at hg'
    exact WithConv.toConv_injective hg'

theorem mem_mrange_convComp_iff' {H K Ω : Type} [CommRing H] [Bialgebra R H] [CommRing K] [Bialgebra R K]
    [CommRing Ω] [Algebra R Ω] (π : H →ₐc[R] K) (f : WithConv (H →ₐ[R] Ω)) :
    f ∈ MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω π) ↔ ∃ g : K →ₐ[R] Ω, g.comp (π : H →ₐ[R] K) = f.ofConv := by
  rw [← mem_mrange_convComp_iff π f.ofConv]

theorem mrange_convComp_comp_le {H K K₀ Ω : Type} [CommRing H] [Bialgebra R H] [CommRing K] [Bialgebra R K]
    [CommRing K₀] [Bialgebra R K₀] [CommRing Ω] [Algebra R Ω] (π : H →ₐc[R] K) (ρ : K →ₐc[R] K₀) :
    MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω (ρ.comp π)) ≤
      MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω π) := by
  rintro f ⟨g', rfl⟩
  refine ⟨WithConv.toConv (g'.ofConv.comp (ρ : K →ₐ[R] K₀)), ?_⟩
  rw [PDivisibleGroup.Hopf.convCompMonoidHom_apply, PDivisibleGroup.Hopf.convCompMonoidHom_apply]
  rfl

theorem toConv_inv_mem_mrange {p h : ℕ} (G : PDivisibleGroup R p h) (Ω : Type) [CommRing Ω] [Algebra R Ω]
    {w : ℕ} {K : Type} [CommRing K] [HopfAlgebra R K] (π : G.level w →ₐc[R] K)
    (x : G.Point Ω w)
    (hx : PDivisibleGroup.Point.toConv x ∈ MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω π)) :
    PDivisibleGroup.Point.toConv x⁻¹ ∈ MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω π) := by
  obtain ⟨g', hg'⟩ := hx
  obtain ⟨u, hu⟩ := PDivisibleGroup.Hopf.isUnit_toConv_algHom (R := R) g'.ofConv
  have hu' : (u : WithConv (K →ₐ[R] Ω)) = g' := by rw [hu]
  refine ⟨((u⁻¹ : (WithConv (K →ₐ[R] Ω))ˣ) : WithConv (K →ₐ[R] Ω)), ?_⟩
  have hx1 : (PDivisibleGroup.Point.ofConv (PDivisibleGroup.Hopf.convCompMonoidHom Ω π ↑u⁻¹) : G.Point Ω w) * x = 1 := by
    show PDivisibleGroup.Hopf.convCompMonoidHom Ω π ↑u⁻¹ * PDivisibleGroup.Point.toConv x = (1 : WithConv (G.level w →ₐ[R] Ω))
    rw [← hg', ← hu', ← map_mul, Units.inv_mul, map_one]
  have hinv := eq_inv_of_mul_eq_one_left hx1
  rw [← hinv]
  rfl

theorem eq_comp_of_comp_symm_eq {A S' Ω : Type} [CommRing A] [Algebra R A] [CommRing S'] [Algebra R S']
    [CommRing Ω] [Algebra R Ω] (e : A ≃ₐ[R] S') (δ : A →ₐ[R] Ω) (g : S' →ₐ[R] Ω)
    (h : δ.comp (e.symm : S' →ₐ[R] A) = g) : δ = g.comp (e : A →ₐ[R] S') := by
  ext z
  have hz := DFunLike.congr_fun h (e z)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply] at hz
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom]
  exact hz

theorem injective_core {p h : ℕ} [Fact p.Prime] [IsDomain R] (G : PDivisibleGroup R p h)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] (hR : Function.Injective (algebraMap R Ω))
    (M : Submodule ℤ_[p] (TateModule p (G.Points Ω)))
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points Ω)), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ w, CommRing (B w)] [∀ w, HopfAlgebra R (B w)]
    [∀ w, Coalgebra.IsCocomm R (B w)] [∀ w, Module.Finite R (B w)] [∀ w, Module.Free R (B w)]
    (π : ∀ w, G.level w →ₐc[R] B w) (t : ∀ w, B (w + 1) →ₐc[R] B w)
    (hπ : ∀ w, Function.Surjective (π w)) (ht : ∀ w, Function.Surjective (t w))
    (hπt : ∀ w, (π w).comp (G.transition w) = (t w).comp (π (w + 1)))
    (hpts : ∀ (w : ℕ) (g : G.Point Ω w),
        (∃ g' : B w →ₐ[R] Ω, g'.comp (π w : G.level w →ₐ[R] B w) = PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd Ω w (Additive.ofMul g) = (x : ℕ → G.Points Ω) w)
    (i₀ v : ℕ) (Lv : Type) [CommRing Lv] [HopfAlgebra R Lv] [Module.Free R Lv] [Module.Finite R Lv]
    (ιv : Lv →ₐc[R] B (i₀ + v)) (hinj : Function.Injective ιv)
    (hrange : (ιv : Lv →ₐ[R] B (i₀ + v)).range = HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (φv : G.level v →ₐ[R] Lv)
    (hdef : ∀ a' : G.level (i₀ + v),
      ιv (φv (PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) a')) =
        π (i₀ + v) (PDivisibleGroup.Hopf.nsmulAlgHom R (G.level (i₀ + v)) (p ^ i₀) a'))
    (γ γ' : Lv →ₐ[R] Ω) (hγ : γ.comp φv = γ'.comp φv) : γ = γ' := by
  classical
  have hρsurj : Function.Surjective (PDivisibleGroup.Tower.transitionLE t i₀ v) :=
    PDivisibleGroup.Tower.transitionLE_surjective t ht i₀ v
  let e := equivOfRange (ιv : Lv →ₐ[R] B (i₀ + v)) hinj
    (HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) hrange
  haveI : Module.Finite R ↥(HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) :=
    Module.Finite.equiv e.toLinearEquiv
  haveI : Module.Free R ↥(HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) :=
    Module.Free.of_equiv e.toLinearEquiv
  obtain ⟨r, h1, h2, h3, h4⟩ :=
    HopfAlgebra.exists_restriction_points_hopfKer_mul_and_eq_one_iff_and_surjective_of_isAlgClosed
      R Ω hR (π (i₀ + v)) (hπ (i₀ + v)) (PDivisibleGroup.Tower.transitionLE t i₀ v) hρsurj
      (MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω
        ((PDivisibleGroup.Tower.transitionLE t i₀ v).comp (π (i₀ + v)))))
      (MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω (π (i₀ + v))))
      (mrange_convComp_comp_le _ _) (fun f => mem_mrange_convComp_iff _ f) (fun f => mem_mrange_convComp_iff _ f)
  let ef : Lv →ₐ[R] ↥(HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) := e.toAlgHom
  let es : ↥(HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)) →ₐ[R] Lv := e.symm.toAlgHom
  have hes : ∀ z, es (ef z) = z := fun z => e.symm_apply_apply z
  have hef : ∀ z, ((ef z : ↥(HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))) : B (i₀ + v)) = ιv z :=
    fun z => coe_equivOfRange _ hinj _ hrange z
  obtain ⟨f, hfN', hf⟩ := h4 (WithConv.toConv (γ.comp es))
  obtain ⟨f', hf'N', hf'⟩ := h4 (WithConv.toConv (γ'.comp es))
  obtain ⟨g, hg⟩ := (mem_mrange_convComp_iff' (π (i₀ + v)) f).1 hfN'
  obtain ⟨g', hg'⟩ := (mem_mrange_convComp_iff' (π (i₀ + v)) f').1 hf'N'

  have hrec : ∀ (δ : Lv →ₐ[R] Ω) (g₀ : B (i₀ + v) →ₐ[R] Ω),
      δ.comp es = g₀.comp (HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v)).val →
      ∀ z, δ z = g₀ (ιv z) := by
    intro δ g₀ hδ z
    have hz := DFunLike.congr_fun hδ (ef z)
    rw [AlgHom.comp_apply, hes] at hz
    rw [hz, AlgHom.comp_apply, Subalgebra.coe_val, hef]
  have hγg := hrec γ g (by have h0 := h1 f hfN' g hg; rw [hf] at h0; exact h0)
  have hγ'g := hrec γ' g' (by have h0 := h1 f' hf'N' g' hg'; rw [hf'] at h0; exact h0)

  have hval : ∀ (δ : Lv →ₐ[R] Ω) (f₀ : WithConv (G.level (i₀ + v) →ₐ[R] Ω)) (g₀ : B (i₀ + v) →ₐ[R] Ω),
      g₀.comp (π (i₀ + v) : G.level (i₀ + v) →ₐ[R] B (i₀ + v)) = f₀.ofConv → (∀ z, δ z = g₀ (ιv z)) →
      ∀ a' : G.level (i₀ + v),
        PDivisibleGroup.Point.toAlgHom ((PDivisibleGroup.Point.ofConv f₀ : G.Point Ω (i₀ + v)) ^ (p ^ i₀)) a' =
          δ (φv (PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) a')) := by
    intro δ f₀ g₀ hg₀ hδ a'
    rw [PDivisibleGroup.Point.toAlgHom_pow, AlgHom.comp_apply, hδ, hdef]
    change f₀.ofConv _ = _
    rw [← hg₀]
    rfl
  have hpow : (PDivisibleGroup.Point.ofConv f : G.Point Ω (i₀ + v)) ^ (p ^ i₀) =
      (PDivisibleGroup.Point.ofConv f' : G.Point Ω (i₀ + v)) ^ (p ^ i₀) := by
    apply PDivisibleGroup.Point.ext
    intro a'
    rw [hval γ f g hg hγg a', hval γ' f' g' hg' hγ'g a']
    exact DFunLike.congr_fun hγ _

  have hupow : ((PDivisibleGroup.Point.ofConv f : G.Point Ω (i₀ + v)) *
      (PDivisibleGroup.Point.ofConv f' : G.Point Ω (i₀ + v))⁻¹) ^ (p ^ i₀) = 1 := by
    rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  have hinvN' := toConv_inv_mem_mrange G Ω (π (i₀ + v)) (PDivisibleGroup.Point.ofConv f' : G.Point Ω (i₀ + v)) hf'N'
  have huN' : PDivisibleGroup.Point.toConv ((PDivisibleGroup.Point.ofConv f : G.Point Ω (i₀ + v)) *
      (PDivisibleGroup.Point.ofConv f' : G.Point Ω (i₀ + v))⁻¹) ∈
      MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω (π (i₀ + v))) := by
    rw [PDivisibleGroup.Point.toConv_mul]
    exact Submonoid.mul_mem _ hfN' hinvN'
  have huN : PDivisibleGroup.Point.toConv ((PDivisibleGroup.Point.ofConv f : G.Point Ω (i₀ + v)) *
      (PDivisibleGroup.Point.ofConv f' : G.Point Ω (i₀ + v))⁻¹) ∈
      MonoidHom.mrange (PDivisibleGroup.Hopf.convCompMonoidHom Ω
        ((PDivisibleGroup.Tower.transitionLE t i₀ v).comp (π (i₀ + v)))) := by
    rw [mem_mrange_convComp_iff']
    exact exists_factor_of_pow_eq_one G Ω M hMsat B π t hπt hpts i₀ v _
      ((mem_mrange_convComp_iff' _ _).1 huN') hupow
  have hru := (h3 _ huN').2 huN
  have hrf : r f = r f' := by
    have hmul := h2 _ huN' f' hf'N'
    rw [hru, one_mul] at hmul
    rw [← hmul]
    congr 1
    rw [PDivisibleGroup.Point.toConv_mul, mul_assoc]
    change f = PDivisibleGroup.Point.toConv (PDivisibleGroup.Point.ofConv f : G.Point Ω (i₀ + v)) *
      PDivisibleGroup.Point.toConv ((PDivisibleGroup.Point.ofConv f' : G.Point Ω (i₀ + v))⁻¹ *
        (PDivisibleGroup.Point.ofConv f' : G.Point Ω (i₀ + v)))
    rw [inv_mul_cancel, PDivisibleGroup.Point.toConv_one, mul_one]
    rfl
  rw [hf, hf'] at hrf
  have hcomp : γ.comp es = γ'.comp es := WithConv.toConv_injective hrf
  ext z
  have hz := DFunLike.congr_fun hcomp (ef z)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, hes] at hz
  exact hz

end PTS

theorem injective_of_hdef
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v)
    (m : ∀ j, B j →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p)
    (i₀ : ℕ)
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (L v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (L v)]
    (t' : ∀ v, L (v + 1) →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v) (ι : ∀ v, L v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v))
    (hιinj : ∀ v, Function.Injective (ι v))
    (hιrange : ∀ v, (ι v : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (hιt : ∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1)))
    (φ : ∀ v, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v)
    (hdef : ∀ (v : ℕ) (a' : G.level (i₀ + v)),
        ι v ((φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) ((PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀)) a')) = π (i₀ + v) ((PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀)) a')) :
    ∀ v, ∀ γ γ' : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p,
        γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) = γ'.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) → γ = γ' := fun v γ γ' hγ =>
  injective_core (R := (PadicAlgCl.ringOfIntegers p K)) G (PadicAlgCl p) Subtype.val_injective M hMsat B π t hπ ht hπt hpts i₀ v (L v)
    (ι v) (hιinj v) (hιrange v) (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) (hdef v) γ γ' hγ

theorem image_iff_of_hdef
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v)
    (m : ∀ j, B j →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p)
    (i₀ : ℕ)
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (L v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (L v)]
    (t' : ∀ v, L (v + 1) →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v) (ι : ∀ v, L v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v))
    (hιinj : ∀ v, Function.Injective (ι v))
    (hιrange : ∀ v, (ι v : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (hιt : ∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1)))
    (φ : ∀ v, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v)
    (hdef : ∀ (v : ℕ) (a' : G.level (i₀ + v)),
        ι v ((φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) ((PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀)) a')) = π (i₀ + v) ((PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀)) a')) :
    (∀ (v : ℕ) (y : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p),
        (∃ γ : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p, γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) = y) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom y)) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) := by
  classical
  intro v y

  have hTs : Function.Surjective (transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀)) :=
    transitionOfLE_surjective G.transition G.transition_surjective v (i₀ + v) _
  let Kv : Subalgebra (PadicAlgCl.ringOfIntegers p K) (B (i₀ + v)) := hopfKer (transitionLE t i₀ v)
  let e : L v ≃ₐ[PadicAlgCl.ringOfIntegers p K] ↥Kv :=
    equivOfRange (ι v : L v →ₐ[PadicAlgCl.ringOfIntegers p K] B (i₀ + v)) (hιinj v) Kv (hιrange v)
  have hkey := fun (g : B (i₀ + v) →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p) (a' : G.level (i₀ + v)) =>
    key_apply G B π t (L v) (ι v) (hιinj v) (hιrange v) (φ v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] L v)
      (hdef v) g a'
  constructor
  · rintro ⟨γ, hγ⟩

    obtain ⟨g, hg⟩ := Subalgebra.exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite Kv (PadicAlgCl p)
      (γ.comp e.symm.toAlgHom)
    let f : G.Point (PadicAlgCl p) (i₀ + v) :=
      Point.ofAlgHom (g.comp (π (i₀ + v) : G.level (i₀ + v) →ₐ[PadicAlgCl.ringOfIntegers p K] B (i₀ + v)))
    obtain ⟨x, hxM, hx⟩ := (hpts (i₀ + v) f).mp ⟨g, rfl⟩
    refine ⟨x, hxM, ?_⟩
    have hγe : ∀ l : L v, g ((e l : ↥Kv) : B (i₀ + v)) = γ l := fun l => by
      have := DFunLike.congr_fun hg (e l)
      simpa using this

    have hpow : f ^ (p ^ i₀) = G.pointInclLE (PadicAlgCl p) (Nat.le_add_left v i₀) (Point.ofAlgHom y) := by
      refine Point.ext fun a' => ?_
      rw [toAlgHom_pointInclLE, Point.toAlgHom_ofAlgHom, AlgHom.comp_apply]
      have h1 : Point.toAlgHom (f ^ (p ^ i₀)) a' =
          Point.toAlgHom f (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) a') :=
        pow_apply_eq_apply_nsmulAlgHom f (p ^ i₀) a'
      rw [h1]
      show g (π (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) a')) =
        y (transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀) a')
      rw [← hkey g a', ← hγ]
      simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Subalgebra.coe_val]
      exact hγe _
    have hc := TateModule.compat_pow x v i₀
    rw [Nat.add_comm v i₀] at hc
    calc G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (Point.ofAlgHom y))
        = G.pointsMkAdd (PadicAlgCl p) (i₀ + v)
            (Additive.ofMul (G.pointInclLE (PadicAlgCl p) (Nat.le_add_left v i₀) (Point.ofAlgHom y))) :=
          (G.pointsMkAdd_pointInclLE _ _).symm
      _ = G.pointsMkAdd (PadicAlgCl p) (i₀ + v) (Additive.ofMul (f ^ (p ^ i₀))) := by rw [hpow]
      _ = (p ^ i₀) • G.pointsMkAdd (PadicAlgCl p) (i₀ + v) (Additive.ofMul f) := by rw [ofMul_pow, map_nsmul]
      _ = (p ^ i₀) • (x : ℕ → G.Points (PadicAlgCl p)) (i₀ + v) := by rw [hx]
      _ = (x : ℕ → G.Points (PadicAlgCl p)) v := by rw [← natCast_zsmul]; exact hc
  · rintro ⟨x, hxM, hx⟩
    obtain ⟨f, hf⟩ := exists_point_rep G (PadicAlgCl p) x (i₀ + v)
    obtain ⟨g, hg⟩ := (hpts (i₀ + v) f).mpr ⟨x, hxM, hf⟩
    refine ⟨(g.comp Kv.val).comp e.toAlgHom, ?_⟩
    apply AlgHom.ext
    intro z
    obtain ⟨a', rfl⟩ := hTs z
    rw [AlgHom.comp_apply, hkey g a']
    have e1 : g (π (i₀ + v) (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) a')) =
        Point.toAlgHom f (nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀) a') :=
      DFunLike.congr_fun hg _
    rw [e1, tate_compat G (PadicAlgCl p) x i₀ v f hf (Point.ofAlgHom y) hx a', Point.toAlgHom_ofAlgHom]

theorem points_of_hdef
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v)
    (m : ∀ j, B j →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p)
    (i₀ : ℕ)
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (L v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (L v)]
    (t' : ∀ v, L (v + 1) →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v) (ι : ∀ v, L v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v))
    (hιinj : ∀ v, Function.Injective (ι v))
    (hιrange : ∀ v, (ι v : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (hιt : ∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1)))
    (φ : ∀ v, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v)
    (hdef : ∀ (v : ℕ) (a' : G.level (i₀ + v)),
        ι v ((φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) ((PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀)) a')) = π (i₀ + v) ((PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀)) a')) :
    (∀ v, ∀ γ γ' : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p,
        γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) = γ'.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) → γ = γ') ∧
    (∀ (v : ℕ) (y : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p),
        (∃ γ : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p, γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) = y) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom y)) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) :=
  ⟨fun v => (injective_of_hdef p K G M hMstab hMsat B π t hπ ht hπt hpts m hmt htm i₀ L t' ι hιinj hιrange hιt φ hdef) v,
   fun v => (image_iff_of_hdef p K G M hMstab hMsat B π t hπ ht hπt hpts m hmt htm i₀ L t' ι hιinj hιrange hιt φ hdef) v⟩

end Ws47.PHI

open Ws47.PHI in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)
    (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))
    (hMstab : ∀ (τ : PadicAlgCl p ≃ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p)
        (x : TateModule p (G.Points (PadicAlgCl p))),
      x ∈ M → G.tateModuleRep (PadicAlgCl p) τ x ∈ M)
    (hMsat : ∀ (r : ℤ_[p]) (x : TateModule p (G.Points (PadicAlgCl p))), r ≠ 0 → r • x ∈ M → x ∈ M)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (B v)]
    [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (B v)]
    (π : ∀ v, G.level v →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (t : ∀ v, B (v + 1) →ₐc[PadicAlgCl.ringOfIntegers p K] B v)
    (hπ : ∀ v, Function.Surjective (π v)) (ht : ∀ v, Function.Surjective (t v))
    (hπt : ∀ v, (π v).comp (G.transition v) = (t v).comp (π (v + 1)))
    (hpts : ∀ (v : ℕ) (g : G.Point (PadicAlgCl p) v),
        (∃ g' : B v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p,
            g'.comp (π v : G.level v →ₐ[PadicAlgCl.ringOfIntegers p K] B v) =
              PDivisibleGroup.Point.toAlgHom g) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul g) =
            (x : ℕ → G.Points (PadicAlgCl p)) v)
    (m : ∀ j, B j →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (j + 1))
    (hmt : ∀ j, (m j).comp (t j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B (j + 1)) p)
    (htm : ∀ j, (t j).comp (m j) = PDivisibleGroup.Hopf.nsmulBialgHom (PadicAlgCl.ringOfIntegers p K) (B j) p)
    (i₀ : ℕ)
    (L : ℕ → Type) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra (PadicAlgCl.ringOfIntegers p K) (L v)]
    [∀ v, Coalgebra.IsCocomm (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Free (PadicAlgCl.ringOfIntegers p K) (L v)] [∀ v, Module.Finite (PadicAlgCl.ringOfIntegers p K) (L v)]
    (t' : ∀ v, L (v + 1) →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v) (ι : ∀ v, L v →ₐc[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v))
    (hιinj : ∀ v, Function.Injective (ι v))
    (hιrange : ∀ v, (ι v : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] B (i₀ + v)).range =
        HopfAlgebra.hopfKer (PDivisibleGroup.Tower.transitionLE t i₀ v))
    (hιt : ∀ v, (ι v).comp (t' v) = (t (i₀ + v)).comp (ι (v + 1))) :
    ∃ φ : ∀ v : ℕ, G.level v →ₐc[(PadicAlgCl.ringOfIntegers p K)] L v,
      (∀ v, (φ v).comp (G.transition v) = (t' v).comp (φ (v + 1))) ∧
      (∀ v, ∀ γ γ' : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p,
        γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) = γ'.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) → γ = γ') ∧
      (∀ (v : ℕ) (y : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p),
        (∃ γ : L v →ₐ[(PadicAlgCl.ringOfIntegers p K)] PadicAlgCl p, γ.comp (φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) = y) ↔
          ∃ x ∈ M, G.pointsMkAdd (PadicAlgCl p) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom y)) =
            (x : ℕ → G.Points (PadicAlgCl p)) v) := by
  classical
  obtain ⟨φa, hdefa⟩ := exists_algHom_hdef p K G M hMstab hMsat B π t hπ ht hπt hpts m hmt htm i₀ L t' ι hιinj hιrange hιt
  obtain ⟨φ, hφ⟩ := Ws47.PHI.exists_bialgHom_coe_eq p h i₀ G B π L ι hιinj φa hdefa
  have hdef : ∀ (v : ℕ) (a' : G.level (i₀ + v)),
      ι v ((φ v : G.level v →ₐ[(PadicAlgCl.ringOfIntegers p K)] L v) ((PDivisibleGroup.Tower.transitionOfLE G.transition v (i₀ + v) (Nat.le_add_left v i₀)) a')) = π (i₀ + v) ((PDivisibleGroup.Hopf.nsmulAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level (i₀ + v)) (p ^ i₀)) a') := by
    intro v a'; rw [hφ]; exact hdefa v a'
  refine ⟨φ, comp_transition_eq_of_hdef p K G M hMstab hMsat B π t hπ ht hπt hpts m hmt htm i₀ L t' ι hιinj hιrange hιt φ hdef, ?_⟩
  exact points_of_hdef p K G M hMstab hMsat B π t hπ ht hπt hpts m hmt htm i₀ L t' ι hιinj hιrange hιt φ hdef

end S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_exists_bialgHom_comp_transition_eq_and_injective_of_hopf_quotient_system_of_tower_of_ringOfIntegers (solution)
