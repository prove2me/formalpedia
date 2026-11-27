-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteModuloGeneralEquation_proof_664effa2a22a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:58:22.174808+00:00
-- url     : https://prove2.me/submissions/65806682-1706-42ec-ab7a-34e6257f5f40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteModuloGeneralEquation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_DetEqZeroOfMulVecEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteModuloGeneralEquation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtComp_apply_7f605f1103e2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtEval_apply_40b5f84f59da
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtGerm_eq_iff_d718501e394b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtGerm_surjective_5cdac204dd5e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_det_eq_zero_of_mulVec_eq_zero_6bd628e3069c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_analyticAtSubring_5d2b91f5e5b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroCoordinate_apply_d48952ae67a2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtComp_apply_7f605f1103e2
attribute [local simp] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtEval_apply_40b5f84f59da



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FiniteModuloGeneralEquation
theorem _root_.solution : FiniteModuloGeneralEquation.Statement := by
  intro σ τ _ _ _ x k f L c hf ⟨n, e, he, hfin⟩ ⟨r, h, h', hh, hh', hpow⟩
  classical
  have hproj : ∀ c', AnalyticAt ℂ (fun y : τ → ℂ => y c') (L x) := fun c' =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c').analyticAt _

  let fs : Fin k → analyticAtSubring x := fun i => ⟨f i, hf i⟩
  let es : Fin n → analyticAtSubring x := fun m => ⟨e m, he m⟩
  let hs : Fin k → analyticAtSubring x := fun i => ⟨h i, hh i⟩
  let hs' : τ → analyticAtSubring x := fun c' => ⟨h' c', hh' c'⟩
  let T : analyticAtSubring (L x) := ⟨fun y => (y c - L x c) ^ r, mem_analyticAtSubring.2 (((hproj c).sub analyticAt_const).pow r)⟩
  let D : τ → analyticAtSubring (L x) := fun c' =>
    ⟨fun y => zeroCoordinate c y c' - zeroCoordinate c (L x) c', mem_analyticAtSubring.2 (by
      simp only [zeroCoordinate_apply]
      split_ifs
      · exact analyticAt_const
      · exact (hproj c').sub analyticAt_const)⟩

  choose b kk hb hkk hbk using fun (i : Fin n) (c' : τ) => hfin _ ((hh' c').mul (he i))
  obtain ⟨b1, k1, hb1, hk1, h1eq⟩ := hfin (fun _ => 1) analyticAt_const
  let bs : Fin n → τ → Fin n → analyticAtSubring (L x) := fun i c' j => ⟨b i c' j, hb i c' j⟩
  let b1s : Fin n → analyticAtSubring (L x) := fun m => ⟨b1 m, hb1 m⟩
  let M : Matrix (Fin n) (Fin n) (analyticAtSubring (L x)) :=
    Matrix.of fun i j => (if i = j then T else 0) - ∑ c', bs i c' j * D c'
  refine ⟨r * n, ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ), ?_⟩

  let J : Ideal (holGerms x) := Ideal.span (Set.range fun i => analyticAtGerm x (fs i))
  let ψ : analyticAtSubring x →+* holGerms x ⧸ J := (Ideal.Quotient.mk J).comp (analyticAtGerm x)
  let ψ' : analyticAtSubring (L x) →+* holGerms x ⧸ J := ψ.comp (analyticAtComp x L)
  have hψf : ∀ i, ψ (fs i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  have hψeq : ∀ a b : analyticAtSubring x, (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 x] b → ψ a = ψ b := fun a b hab => by
    simp only [ψ, RingHom.comp_apply, (analyticAtGerm_eq_iff a b).2 hab]
  have R1 : ψ' T = ∑ c', ψ (hs' c') * ψ' (D c') := by
    have := hψeq (analyticAtComp x L T) (∑ i, hs i * fs i + ∑ c', hs' c' * analyticAtComp x L (D c')) (by
      filter_upwards [hpow] with z hz
      simpa [T, D, hs, hs', fs] using hz)
    simpa [ψ', map_add, map_sum, map_mul, hψf] using this
  have R2 : ∀ i c', ψ (hs' c') * ψ (es i) = ∑ j, ψ' (bs i c' j) * ψ (es j) := fun i c' => by
    have := hψeq (hs' c' * es i) (∑ j, analyticAtComp x L (bs i c' j) * es j +
      ∑ a, (⟨kk i c' a, hkk i c' a⟩ : analyticAtSubring x) * fs a) (by
      filter_upwards [hbk i c'] with z hz
      simpa [bs, es, hs', fs] using hz)
    simpa [ψ', map_add, map_sum, map_mul, hψf] using this
  have R3 : ∑ m, ψ' (b1s m) * ψ (es m) = 1 := by
    have := hψeq 1 (∑ m, analyticAtComp x L (b1s m) * es m +
      ∑ a, (⟨k1 a, hk1 a⟩ : analyticAtSubring x) * fs a) (by
      filter_upwards [h1eq] with z hz
      simpa [b1s, es, fs] using hz)
    simpa [ψ', map_add, map_sum, map_mul, hψf] using this.symm

  have hMe : (ψ'.mapMatrix M) *ᵥ (fun j => ψ (es j)) = 0 := by
    funext i
    have hdiag : ∑ j, ψ' (if i = j then T else 0) * ψ (es j) = ψ' T * ψ (es i) := by
      simp [apply_ite ψ']
    have key : ∀ c', ψ (hs' c') * ψ' (D c') * ψ (es i) = ∑ j, ψ' (bs i c' j) * ψ' (D c') * ψ (es j) := by
      intro c'
      rw [mul_right_comm, R2, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sub,
      map_sum, map_mul, sub_mul, Finset.sum_sub_distrib, Pi.zero_apply, hdiag, R1, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun c' _ => key c', Finset.sum_comm, sub_eq_zero]
  have hdet : ψ' M.det = 0 := by
    rw [RingHom.map_det]
    exact det_eq_zero_of_mulVec_eq_zero _ _ (fun m => ψ' (b1s m)) hMe R3

  have hmem : analyticAtGerm x (analyticAtComp x L M.det) ∈ J := Ideal.Quotient.eq_zero_iff_mem.1 hdet
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  choose q hq using fun i => analyticAtGerm_surjective x (a i)
  refine ⟨fun i => q i, (M.det).2, fun i => (q i).2, ?_, ?_⟩
  · have hgerm : analyticAtGerm x (∑ i, q i * fs i) = analyticAtGerm x (analyticAtComp x L M.det) := by
      rw [← ha]
      simp [map_sum, map_mul, hq]
    filter_upwards [(analyticAtGerm_eq_iff _ _).1 hgerm] with z hz
    simpa [fs] using hz.symm

  · have hev : ∀ s : ℂ, ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s) = s ^ (r * n) := by
      intro s
      rw [← analyticAtEval_apply, RingHom.map_det]
      have hdg : (analyticAtEval (L x) (L x + Pi.single c s)).mapMatrix M = Matrix.diagonal fun _ => s ^ r := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, M, Matrix.of_apply, map_sub, map_sum, map_mul,
          apply_ite (analyticAtEval (L x) (L x + Pi.single c s)), map_zero, analyticAtEval_apply, Matrix.diagonal_apply]
        have hD : ∀ c', ((D c' : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s) = 0 := by
          intro c'
          simp only [D, zeroCoordinate_apply]
          split_ifs with hc
          · simp
          · simp [hc]
        simp [hD, T]
      rw [hdg, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [show (fun s : ℂ => ((M.det : analyticAtSubring (L x)) : (τ → ℂ) → ℂ) (L x + Pi.single c s)) =
      fun s : ℂ => s ^ (r * n) from funext hev]
    exact ((analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).pow _).analyticOrderAt_eq_natCast.2
      ⟨fun _ => 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun s => by simp⟩
end FiniteModuloGeneralEquation
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
