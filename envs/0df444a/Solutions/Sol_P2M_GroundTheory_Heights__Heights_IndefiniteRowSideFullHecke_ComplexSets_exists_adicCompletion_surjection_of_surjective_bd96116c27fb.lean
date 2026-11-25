-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_adicCompletion_surjection_of_surjective_bd96116c27fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:59.581106+00:00
-- url     : https://prove2.me/submissions/7d406249-86a9-4799-a3cf-625c63904e8a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibreQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormalFibreQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution
    {B A : Type} [CommRing B] [CommRing A] (f : B →+* A) (hf : Function.Surjective f)
    (hB : IsNoetherianRing B) (m : Ideal A) :
    ∃ φ : AdicCompletion (m.comap f) B →+* AdicCompletion m A, Function.Surjective φ ∧
      φ.comp (algebraMap B (AdicCompletion (m.comap f) B)) =
        (algebraMap A (AdicCompletion m A)).comp f ∧
      RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap B (AdicCompletion (m.comap f) B)) := by
  have := hB
  have : IsNoetherianRing A := isNoetherianRing_of_surjective B A f hf
  set M := m.comap f with hM
  have hpow : ∀ n : ℕ, (M ^ n).map f = m ^ n := fun n => by
    rw [Ideal.map_pow, hM, Ideal.map_comap_of_surjective f hf]
  let fam : (n : ℕ) → AdicCompletion M B →+* A ⧸ m ^ n := fun n =>
    (Ideal.quotientMap (m ^ n) f (Ideal.le_comap_pow f n)).comp
      (AdicCompletion.evalₐ M n : AdicCompletion M B →+* B ⧸ M ^ n)
  have hfam : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorPow m hle).comp (fam n) = fam k := by
    intro k n hle
    ext x
    induction x using AdicCompletion.induction_on with
    | h b =>
      simp only [fam, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk]
      change Ideal.Quotient.factorPow m hle (Ideal.Quotient.mk (m ^ n) (f (b n))) =
        Ideal.Quotient.mk (m ^ k) (f (b k))
      rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      have hb := AdicCompletion.AdicCauchySequence.mk_eq_mk hle b
      rw [Submodule.Quotient.eq] at hb
      have hb' : b n - b k ∈ M ^ k := by simpa using hb
      rw [← map_sub]
      exact Ideal.le_comap_pow f k hb'
  let φ : AdicCompletion M B →+* AdicCompletion m A := AdicCompletion.liftRingHom m fam hfam
  have hcomm : φ.comp (algebraMap B (AdicCompletion M B)) = (algebraMap A (AdicCompletion m A)).comp f := by
    refine RingHom.ext fun b => AdicCompletion.ext_evalₐ fun n => ?_
    simp only [φ, fam, RingHom.comp_apply, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_liftRingHom,
      RingHom.coe_coe, AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  refine ⟨φ, ?_, hcomm, ?_⟩
  · have fgM : M.FG := IsNoetherian.noetherian M
    have fgm : m.FG := IsNoetherian.noetherian m
    have := AdicCompletion.isAdicComplete_self M fgM
    have hmap : (M.map (algebraMap B (AdicCompletion M B))).map φ =
        m.map (algebraMap A (AdicCompletion m A)) := by
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, hM, Ideal.map_comap_of_surjective f hf]
    have : IsHausdorff ((M.map (algebraMap B (AdicCompletion M B))).map φ) (AdicCompletion m A) := by
      rw [hmap]
      exact (AdicCompletion.isAdicComplete_self m fgm).toIsHausdorff
    apply surjective_of_mk_map_comp_surjective (I := M.map (algebraMap B (AdicCompletion M B))) φ
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ m y)
    obtain ⟨b, rfl⟩ := hf a
    refine ⟨algebraMap B _ b, ?_⟩
    rw [RingHom.comp_apply, ← RingHom.comp_apply φ, hcomm, RingHom.comp_apply, Ideal.Quotient.eq, hmap,
      ← AdicCompletion.ker_evalOneₐ_eq_map m fgm, RingHom.mem_ker]
    simp [ha, AdicCompletion.algebraMap_apply]
  · intro x hx
    let _ : Algebra B A := f.toAlgebra
    let K := RingHom.ker f
    let g : B →ₗ[B] A := Algebra.linearMap B A
    have hg : Function.Surjective g := hf
    have hfg : Function.Exact K.subtype g := by
      intro y
      simp [g, K, RingHom.mem_ker, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
    have hx' : AdicCompletion.map M g x = 0 := by
      induction x using AdicCompletion.induction_on with
      | h b => ?_
      have hb := RingHom.mem_ker.mp hx
      refine AdicCompletion.ext fun n => ?_
      have h1 : f (b n) ∈ m ^ n := by
        have := congrArg (AdicCompletion.evalₐ m n) hb
        rw [map_zero] at this
        simp only [φ, AdicCompletion.evalₐ_liftRingHom, fam, RingHom.comp_apply, RingHom.coe_coe,
          AdicCompletion.evalₐ_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      have h2 : g (b n) ∈ (M ^ n • ⊤ : Submodule B A) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        change f (b n) ∈ (M ^ n).map f
        rw [hpow]
        exact h1
      simpa [AdicCompletion.map_mk] using h2
    obtain ⟨z, rfl⟩ := ((AdicCompletion.map_exact (I := M) Subtype.val_injective hfg hg) x).mp hx'
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite M K z
    have hnat := congrArg (fun F => F t) (AdicCompletion.ofTensorProduct_naturality M K.subtype)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hnat
    rw [hnat]
    clear hnat hx hx'
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r k =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq,
        Submodule.coe_subtype, AdicCompletion.ofTensorProduct_tmul]
      exact Ideal.mul_mem_left _ r (Ideal.mem_map_of_mem _ k.2)
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact add_mem h₁ h₂
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
