-- Prove2me | solution 1 for ValuationSubring.tensorProduct_exists_primitive_factor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bad8118c-e12b-5ead-a09b-838f680e6f0b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_tensorProduct_exists_primitive_factor

open IsLocalRing TensorProduct

theorem solution
    (K F K' : Type*) [Field K] [CommRing F] [Nontrivial F] [NoZeroDivisors F]
    [Field K'] [Algebra K F] [Algebra K K']
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (hker : RingHom.ker σ = maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    letI : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
    let hσAlg : A →ₐ[K] F :=
      { toRingHom := (algebraMap K F).comp σ
        commutes' := fun c ↦ congrArg (algebraMap K F) (hsec c) }
    let Ψ : TensorProduct K F A →ₐ[K] F :=
      Algebra.TensorProduct.lift (AlgHom.id K F) hσAlg (fun f a ↦ mul_comm _ _)
    ∀ z : TensorProduct K F A, z ≠ 0 →
      ∃ a : A, a ≠ 0 ∧ ∃ z' : TensorProduct K F A,
        z = ((1 : F) ⊗ₜ[K] a) * z' ∧ Ψ z' ≠ 0 := by
  classical
  letI : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
  intro hσAlg Ψ z hz
  let e := Module.Basis.ofVectorSpace K F
  let eqv : TensorProduct K F A ≃ₗ[K] _ →₀ A :=
    (LinearEquiv.rTensor A e.repr).trans (TensorProduct.finsuppScalarLeft K A _)
  have hsingle : ∀ i a, eqv.symm (Finsupp.single i a) = e i ⊗ₜ[K] a := by
    intro i a
    simp only [eqv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      TensorProduct.finsuppScalarLeft_symm_apply_single]
    change (LinearEquiv.rTensor A e.repr).symm _ = _
    rw [LinearEquiv.rTensor_symm_tmul, Module.Basis.repr_symm_single_one]
  have hMinDvd : ∀ (s : Finset (Module.Basis.ofVectorSpaceIndex K F))
      (f : Module.Basis.ofVectorSpaceIndex K F → A), s.Nonempty →
      ∃ j ∈ s, ∀ i ∈ s, f j ∣ f i := by
    intro s f hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton j => exact ⟨j, Finset.mem_singleton_self j,
        fun i hi ↦ (Finset.mem_singleton.mp hi) ▸ dvd_refl _⟩
    | cons j s hjs hs' ih =>
      obtain ⟨k, hks, hk⟩ := ih
      rcases ValuationRing.dvd_total (R := A) (f j) (f k) with hjk | hkj
      · exact ⟨j, Finset.mem_cons_self _ _, fun i hi ↦
          (Finset.mem_cons.mp hi).elim (· ▸ dvd_refl _) (fun hi' ↦ hjk.trans (hk i hi'))⟩
      · exact ⟨k, Finset.mem_cons.mpr (Or.inr hks), fun i hi ↦
          (Finset.mem_cons.mp hi).elim (· ▸ hkj) (hk i)⟩
  set g := eqv z with hg_def
  have hg0 : g ≠ 0 := fun h ↦ hz (by rw [← eqv.symm_apply_apply z, ← hg_def, h, map_zero])
  have hne := Finsupp.support_nonempty_iff.mpr hg0
  obtain ⟨j, hj, hjdvd⟩ := hMinDvd g.support g hne
  have hjdvd' : ∀ i, g j ∣ g i := fun i ↦
    if hi : i ∈ g.support then hjdvd i hi else (Finsupp.notMem_support_iff.mp hi) ▸ dvd_zero _
  have ha0 : g j ≠ 0 := Finsupp.mem_support_iff.mp hj
  choose b hb using hjdvd'
  have hbj : b j = 1 := mul_left_cancel₀ ha0 ((hb j).symm.trans (mul_one _).symm)
  let z' : TensorProduct K F A := g.support.sum fun i ↦ e i ⊗ₜ[K] b i
  have hzeq : z = ((1 : F) ⊗ₜ[K] g j) * z' := by
    have hzg : z = g.support.sum fun i ↦ e i ⊗ₜ[K] g i := by
      conv_lhs => rw [show z = eqv.symm g from (eqv.symm_apply_apply z).symm,
        show g = g.sum Finsupp.single from (Finsupp.sum_single g).symm, map_finsuppSum]
      simp only [hsingle, Finsupp.sum]
    rw [hzg]
    simp only [z', Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hb i]
  refine ⟨g j, ha0, z', hzeq, ?_⟩
  simp only [z', map_sum, Ψ, Algebra.TensorProduct.lift_tmul, hσAlg, AlgHom.coe_mk,
    RingHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
  intro hsum
  have hsum' : g.support.sum (fun i ↦ (σ (b i)) • e i) = 0 := by
    rw [← hsum]; exact Finset.sum_congr rfl fun i _ ↦ by rw [Algebra.smul_def, mul_comm]
  have hli := e.linearIndependent.comp (Subtype.val : g.support → _) Subtype.val_injective
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun i ↦ σ (b i)) (by
    simp only [Function.comp_apply]
    exact (Finset.sum_attach g.support (fun i ↦ σ (b i) • e i)).trans hsum')
  have hj0 : σ (b j) = 0 := hcoef ⟨j, hj⟩
  rw [hbj, map_one] at hj0
  exact one_ne_zero hj0

end S_ValuationSubring_tensorProduct_exists_primitive_factor
end P2MW
export P2MW.S_ValuationSubring_tensorProduct_exists_primitive_factor (solution)
