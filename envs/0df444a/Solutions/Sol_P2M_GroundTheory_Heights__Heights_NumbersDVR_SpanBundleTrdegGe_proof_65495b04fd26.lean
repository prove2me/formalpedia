-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_proof_65495b04fd26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:06:04.182403+00:00
-- url     : https://prove2.me/submissions/bafad0be-7fd9-474d-8ddd-fd0bd58fdc34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpanBundleTrdegGe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_algebraicIndependent_linComb_4848053020e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleTrdegGe_exists_injective_cone_3ee5f0062363

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SpanBundleTrdegGe
theorem _root_.solution : SpanBundleTrdegGe.Statement := by
  intro F _ Ω _ _ K ι y M i G hG Φ _ _ s hs
  classical
  let : Algebra F Φ := ((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra
  have : IsScalarTower F Ω Φ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set z := projCoord y (Pi.basisFun Ω (Fin i))
    (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s with hz
  change Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
    Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ pointIdeal F z)
  have hzn : ∀ m, z ⟨none, m⟩ = ∑ j, s j * algebraMap Ω Φ (G m j) := by
    intro m
    simp [hz, projCoord, Matrix.col]
    rfl
  have hzs : ∀ k (q : ι k), z ⟨some k, q⟩ = algebraMap Ω Φ (y ⟨k, q⟩) := fun _ _ => rfl

  obtain ⟨l, hl⟩ : ∃ l : Fin i → Fin M, IsUnit (Matrix.of fun r j => G (l r) j) := by
    have hrk : (Matrix.of G).rank = i := by
      rw [← Matrix.rank_transpose]
      simpa using LinearIndependent.rank_matrix (M := Matrix.transpose (Matrix.of G)) hG
    obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' Ω (Matrix.of G).row
    have : Finite κ := hli.finite
    let : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = i := by
      rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrk]
    let e : Fin i ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨a ∘ e, Matrix.linearIndependent_rows_iff_isUnit.1 ?_⟩
    exact hli.comp e e.injective
  set σ : Fin i → Φ := fun r => ∑ j, s j * algebraMap Ω Φ (G (l r) j) with hσdef
  have hσ : AlgebraicIndependent Ω σ :=
    SpanBundleTrdegGe.algebraicIndependent_linComb s hs _ hl

  have : (pointIdeal F y).IsPrime := RingHom.ker_isPrime _
  have : (pointIdeal F z).IsPrime := RingHom.ker_isPrime _
  set Ay := MRing ι F ⧸ pointIdeal F y
  set Az := MRing (bundleIdx ι M) F ⧸ pointIdeal F z
  let qy : Ay →ₐ[F] MvPolynomial K Ω := Ideal.kerLiftAlg (pointConeMap F y)
  have hqy : Function.Injective qy := Ideal.kerLiftAlg_injective _
  let qz : Az →ₐ[F] MvPolynomial (Option K) Φ := Ideal.kerLiftAlg (pointConeMap F z)
  let emb : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (R := Φ) some).toRingHom.comp (map (algebraMap Ω Φ))
  let σ' : (Σ k, ι k) → (Σ o, bundleIdx ι M o) := fun p => ⟨some p.1, p.2⟩
  have hE1 : ∀ g : MRing ι F, pointConeMap F z (rename σ' g) = emb (pointConeMap F y g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [pointConeMap, emb, MvPolynomial.algebraMap_eq, RingHom.algebraMap_toAlgebra]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      simp only [map_mul, hp, rename_X]
      simp [pointConeMap, emb, σ', hzs]
  have hle : pointIdeal F y ≤ (pointIdeal F z).comap (rename σ' : MRing ι F →ₐ[F] _) := by
    intro g hg
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker] at hg ⊢
    rw [hE1, hg, map_zero]
  let fy : Ay →ₐ[F] Az := Ideal.quotientMapₐ (pointIdeal F z) (rename σ') hle
  let Θ : MvPolynomial (Fin i) Ay →ₐ[F] Az :=
    aevalTower fy fun r => Ideal.Quotient.mk _ (X ⟨none, l r⟩)

  obtain ⟨Ψ, hΨ, hΨC, hΨX⟩ := SpanBundleTrdegGe.exists_injective_cone K σ hσ
  have key : ∀ a, qz (Θ a) = Ψ (map qy.toRingHom a) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [Θ, aevalTower_C, map_C]
      rw [hΨC]
      change qz (Ideal.Quotient.mk _ (rename σ' g)) = emb (qy (Ideal.Quotient.mk _ g))
      simp only [qz, qy]
      exact hE1 g
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p r hp =>
      simp only [map_mul, hp, map_X, hΨX]
      congr 1
      simp only [Θ, aevalTower_X]
      refine (Ideal.kerLiftAlg_mk (pointConeMap F z) _).trans ?_
      simp only [pointConeMap, aeval_X]
      exact congrArg (fun a => C a * X none) (hzn (l r))
  have hΘ : Function.Injective Θ := by
    intro a b hab
    apply map_injective qy.toRingHom hqy
    apply hΨ
    rw [← key, ← key, hab]

  have : FaithfulSMul F Ay :=
    (faithfulSMul_iff_algebraMap_injective F Ay).2 (algebraMap F Ay).injective
  have : FaithfulSMul Ay (MvPolynomial (Fin i) Ay) :=
    (faithfulSMul_iff_algebraMap_injective Ay _).2 (C_injective _ _)
  have e1 := trdeg_add_eq F Ay (A := MvPolynomial (Fin i) Ay)
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at e1
  rw [e1]
  exact trdeg_le_of_injective Θ hΘ
end SpanBundleTrdegGe
end GroundTheory.Heights₂.Heights.NumbersDVR
