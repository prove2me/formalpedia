-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_proof_3eeff9d46f10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:23.545624+00:00
-- url     : https://prove2.me/submissions/30d6bd95-1550-450e-b724-747f8b5ddde9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_expand_a34becc742ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeAlg_isAlgebraic_of_mulVec_25b1546582a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_exists_ne_zero_of_span_5f8e06e12f5c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_proof_b3053cf7626b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensSpan_proof_984f8b2ec229


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open PairConeAlg GenericProjClosureDim
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace PairConeAlg
theorem _root_.solution : PairConeAlg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
  classical

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent
  have := Module.Finite.of_basis e

  obtain ⟨l, hl⟩ : ∃ l : Fin N → Fin M, LinearIndependent Ω (φ ∘ l) := by
    obtain ⟨κ, a, ha, hsp, hind⟩ := exists_linearIndependent' Ω φ
    have : Finite κ := Finite.of_injective a ha
    haveI := Fintype.ofFinite κ
    have hcard : Fintype.card κ = N := by
      rw [← finrank_span_eq_card hind, hsp, TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc,
        finrank_top, Subspace.dual_finrank_eq, Module.finrank_eq_card_basis e, Fintype.card_fin]
    let σ := Fintype.equivFinOfCardEq hcard
    exact ⟨a ∘ σ.symm, hind.comp σ.symm σ.symm.injective⟩
  obtain ⟨m', hm'⟩ := exists_ne_zero_of_span hN e hli φ'
    (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)

  have hϖ0 : algebraMap O Ω ϖ ≠ 0 := by
    intro h0
    have hmem : ϖ ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0,
        map_zero]
    rw [hV.noTorsion] at hmem
    exact hϖ.ne_zero (Ideal.mem_bot.1 hmem)

  obtain ⟨k', f, cc, hf, hcc, hsum, hb⟩ := B.frame c hyc
  choose b hbli hbsp hiff using hb
  obtain ⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  have hsec : ∀ q, ∃ n : ℕ, f l0 ^ n • b l0 q ∈ B.lat c := fun q =>
    (hiff l0 (b l0 q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      by_cases h : q' = q
      · subst h; simp
      · simp [h]⟩, by simp [Pi.single_apply]⟩
  choose n hn using hsec
  let u := (Module.Basis.mk (hbli l0) (hbsp l0).ge).isUnitSMul (fun q => (pow_ne_zero (n q) hl0).isUnit)
  have hu : ∀ q, u q ∈ B.lat c := fun q => by
    rw [Module.Basis.isUnitSMul_apply, Module.Basis.mk_apply]
    exact hn q
  set Y : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀ k with hYdef
  set Y' : Ω := ∏ k, y ⟨k, c k⟩ ^ a₀' k with hY'def
  have hY : Y ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
  have hY' : Y' ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)

  let Gm : Matrix (Fin N) (Fin N) Ω := fun i q => φ (l i) (u q) / Y
  have hdet : Gm.det ≠ 0 := by
    intro h0
    obtain ⟨r, hr0, hr⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hr0
    have hzero : ∑ i, r i • φ (l i) = 0 := by
      refine u.ext fun q => ?_
      have hq := congrFun hr q
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, Gm] at hq
      rw [LinearMap.zero_apply, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      calc ∑ i, r i * φ (l i) (u q) = Y * ∑ i, r i * (φ (l i) (u q) / Y) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by field_simp
        _ = 0 := by rw [hq, mul_zero]
    exact funext (Fintype.linearIndependent_iff.1 hl r hzero)

  have key : ∀ A1 : Subalgebra O (MvPolynomial (Option (Option K)) Φ),
      (∀ q : Σ k, ι k, C (algebraMap Ω Φ (y q)) * X (some (some q.1)) ∈ A1) →
      (∀ i, C (pairProjCoord y e φ φ' t ⟨some none, l i⟩) * X (some none) ∈ A1) →
      C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none ∈ A1 →
      ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
        IsAlgebraic A1 (C (pairProjCoord y e φ φ' t p) * X p.1) := by
    intro A1 h1 h2 h3
    let AC := Subalgebra.algebraicClosure A1 (MvPolynomial (Option (Option K)) Φ)
    have hA : ∀ x ∈ A1, x ∈ AC := fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : A1)
    let ψ : Ω →+* MvPolynomial (Option (Option K)) Φ := (C : Φ →+* _).comp (algebraMap Ω Φ)
    have hψ : ∀ a, ψ a = C (algebraMap Ω Φ a) := fun _ => rfl

    let G : Subalgebra O Ω :=
      { carrier := {a | ψ a ∈ AC}
        mul_mem' := fun {a b} ha hb => by
          show ψ (a * b) ∈ AC
          rw [map_mul]
          exact AC.mul_mem ha hb
        add_mem' := fun {a b} ha hb => by
          show ψ (a + b) ∈ AC
          rw [map_add]
          exact AC.add_mem ha hb
        algebraMap_mem' := fun r => by
          show ψ (algebraMap O Ω r) ∈ AC
          have : ψ (algebraMap O Ω r) = algebraMap O (MvPolynomial (Option (Option K)) Φ) r := by
            rw [hψ, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]
          rw [this]
          exact hA _ (A1.algebraMap_mem r) }
    have hratio : ∀ k j, ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ AC := by
      intro k j
      have h0 : C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) ∈
          nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) :=
        mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (by rw [← hψ]; exact (map_ne_zero ψ).2 (hc k)) (X_ne_zero _))
      refine IsAlgebraic.of_mul h0 (hA _ (h1 ⟨k, c k⟩)) ?_
      have : C (algebraMap Ω Φ (y ⟨k, c k⟩)) * X (some (some k)) * ψ (y ⟨k, j⟩ / y ⟨k, c k⟩) =
          C (algebraMap Ω Φ (y ⟨k, j⟩)) * X (some (some k)) := by
        rw [hψ, mul_right_comm, ← map_mul, ← map_mul, mul_div_cancel₀ _ (hc k)]
      rw [this]
      exact hA _ (h1 ⟨k, j⟩)
    have hchart : chartRing O (segreVec y) c ≤ G := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      show ψ (segreVec y j / segreVec y c) ∈ AC
      rw [segreVec, segreVec, ← Finset.prod_div_distrib, map_prod]
      exact Subalgebra.prod_mem AC fun k _ => hratio k (j k)
    have hϖG : ψ (algebraMap O Ω ϖ) ∈ AC := G.algebraMap_mem ϖ

    have hg : ∀ l q, ψ (φ l (u q) / Y) ∈ AC := by
      intro l q
      obtain ⟨a, ha, hrep⟩ := hφ.sections c hyc l (u q) (hu q)
      have : φ l (u q) / Y = a := by rw [hrep, mul_div_cancel_right₀ _ hY]
      rw [this]
      exact hchart ha
    have hg' : ∀ l q, ψ (φ' l (u q) / Y') ∈ AC := by
      intro l q
      obtain ⟨m, hm⟩ := (hB c hyc).1 (u q) (hu q)
      obtain ⟨a, ha, hrep⟩ := hφ'.sections c hyc l _ hm
      rw [map_smul, smul_eq_mul] at hrep
      have h0 : ψ (algebraMap O Ω ϖ ^ m) ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) :=
        mem_nonZeroDivisors_of_ne_zero ((map_ne_zero ψ).2 (pow_ne_zero _ hϖ0))
      have hpow : ψ (algebraMap O Ω ϖ ^ m) ∈ AC := by
        rw [map_pow]
        exact AC.pow_mem hϖG m
      refine IsAlgebraic.of_mul h0 hpow ?_
      rw [← map_mul, mul_div_assoc', hrep, mul_div_cancel_right₀ _ hY']
      exact hchart ha

    let w : Fin N → MvPolynomial (Option (Option K)) Φ := fun q =>
      C (algebraMap Ω Φ Y * ∑ i, t i * algebraMap Ω Φ (u.repr (e i) q)) * X (some none)
    have hx : ∀ lφ, C (pairProjCoord y e φ φ' t ⟨some none, lφ⟩) * X (some none) =
        ∑ q, ψ (φ lφ (u q) / Y) * w q := by
      intro lφ
      have := expand e u t (φ lφ) Y Y (some none : Option (Option K))
      rw [div_self hY, map_one, one_mul] at this
      exact this.symm
    have hw : ∀ q, w q ∈ AC := by
      intro q
      refine isAlgebraic_of_mulVec (Gm.map ψ) w (fun i j => hg _ _) (fun i => ?_) ?_ q
      · have : ((Gm.map ψ).mulVec w) i = ∑ q, ψ (φ (l i) (u q) / Y) * w q := rfl
        rw [this, ← hx (l i)]
        exact hA _ (h2 i)
      · show (ψ.mapMatrix Gm).det ≠ 0
        rw [← RingHom.map_det]
        exact (map_ne_zero ψ).2 hdet
    rintro ⟨(_ | _ | k), j⟩
    ·
      let P : Fin M' → MvPolynomial (Option (Option K)) Φ := fun l' => ∑ q, ψ (φ' l' (u q) / Y') * w q
      have hP : ∀ l', P l' = C (algebraMap Ω Φ (Y / Y') * pairProjCoord y e φ φ' t ⟨none, l'⟩) * X (some none) :=
        fun l' => expand e u t (φ' l') Y Y' (some none : Option (Option K))
      have hPA : ∀ l', P l' ∈ AC := fun l' => Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg' l' q) (hw q)
      have hP0 : P m' ∈ nonZeroDivisors (MvPolynomial (Option (Option K)) Φ) := by
        rw [hP]
        refine mem_nonZeroDivisors_of_ne_zero (mul_ne_zero ?_ (X_ne_zero _))
        rw [Ne, C_eq_zero]
        exact mul_ne_zero ((map_ne_zero _).2 (div_ne_zero hY hY')) hm'
      refine IsAlgebraic.of_mul hP0 (hPA m') ?_
      have : P m' * (C (pairProjCoord y e φ φ' t ⟨none, j⟩) * X none) =
          P j * (C (pairProjCoord y e φ φ' t ⟨none, m'⟩) * X none) := by
        rw [hP m', hP j]
        simp only [map_mul]
        ring
      rw [this]
      exact AC.mul_mem (hPA j) (hA _ h3)
    ·
      show C (pairProjCoord y e φ φ' t ⟨some none, j⟩) * X (some none) ∈ AC
      rw [hx]
      exact Subalgebra.sum_mem AC fun q _ => AC.mul_mem (hg j q) (hw q)
    ·
      exact hA _ (h1 ⟨k, j⟩)
  exact ⟨l, m', hl, hm', key _ (fun q => Algebra.subset_adjoin (Or.inl ⟨q, rfl⟩))
    (fun i => Algebra.subset_adjoin (Or.inr ⟨Sum.inl i, rfl⟩))
    (Algebra.subset_adjoin (Or.inr ⟨Sum.inr (), rfl⟩))⟩
end PairConeAlg
end GroundTheory.Heights₂.Heights.NumbersDVR
