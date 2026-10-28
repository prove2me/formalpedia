-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.corollary_3_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:47:25.490279+00:00
-- url     : https://prove2.me/submissions/dad79e6e-3a92-4f6c-895a-6619ad487dea

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]


section S169I
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma S169I_aeval_mem (A : Alg I) (S : Mat I) (hS : S ∈ A) (p : Polynomial ℝ) :
    Polynomial.aeval S p ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact A.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, IsScalarTower.algebraMap_apply ℝ ℂ (Mat I)]
    exact A.mul_mem (A.algebraMap_mem _) (A.pow_mem hS n)

lemma S169I_cfc_mem (A : Alg I) (S : Mat I) (hS : S ∈ A) (hSa : IsSelfAdjoint S) (f : ℝ → ℝ) :
    cfc f S ∈ A := by
  have hfin := Matrix.finite_real_spectrum (A := S)
  set T := hfin.toFinset
  let p : Polynomial ℝ := Lagrange.interpolate T id f
  have hp : ∀ x ∈ spectrum ℝ S, p.eval x = f x := by
    intro x hx
    exact Lagrange.eval_interpolate_at_node (s := T) (v := id) (r := f) (i := x)
      (Set.injOn_id _) (hfin.mem_toFinset.mpr hx)
  have h1 : cfc f S = cfc p.eval S := cfc_congr fun x hx => (hp x hx).symm
  rw [h1, cfc_polynomial p S]
  exact S169I_aeval_mem A S hS p

lemma S169I_supp_eq (S : Mat I) :
    supp S = cfc (fun x : ℝ => if x = 0 then (0:ℝ) else 1) S := by
  unfold supp supportPower
  congr 1; funext x; split_ifs <;> simp [Real.rpow_zero]

lemma S169I_P_props (S : Mat I) (hS : S.PosSemidef) :
    IsSelfAdjoint (supp S) ∧ supp S * supp S = supp S ∧ S * supp S = S ∧
      ∃ lam : ℝ, 0 ≤ lam ∧ supp S ≤ (lam : ℂ) • S := by
  have hSa : IsSelfAdjoint S := hS.1
  have hfin := Matrix.finite_real_spectrum (A := S)
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ S) := fun f => hfin.continuousOn f
  set g : ℝ → ℝ := fun x => if x = 0 then (0:ℝ) else 1
  rw [S169I_supp_eq]
  refine ⟨cfc_predicate _ _, ?_, ?_, ?_⟩
  · rw [← cfc_mul g g S (hc g) (hc g)]
    exact cfc_congr fun x _ => by simp only [g, Pi.mul_apply]; split_ifs <;> simp
  · have hm := cfc_mul (fun x : ℝ => x) g S (hc _) (hc g)
    rw [cfc_id' (R := ℝ) (a := S)] at hm
    rw [← hm]
    conv_rhs => rw [← cfc_id' (R := ℝ) (a := S)]
    exact cfc_congr fun x _ => by simp only [g]; split_ifs with h <;> simp [h]
  · have hnn : ∀ x ∈ spectrum ℝ S, 0 ≤ x := fun x hx =>
      spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hS) hx
    set lam : ℝ := ∑ x ∈ hfin.toFinset, x⁻¹
    have hlam : ∀ x ∈ spectrum ℝ S, x⁻¹ ≤ lam := fun x hx =>
      Finset.single_le_sum (f := fun x => x⁻¹) (fun y hy => inv_nonneg.mpr
        (hnn y (hfin.mem_toFinset.mp hy))) (hfin.mem_toFinset.mpr hx)
    have hlam0 : 0 ≤ lam := Finset.sum_nonneg fun y hy => inv_nonneg.mpr (hnn y (hfin.mem_toFinset.mp hy))
    refine ⟨lam, hlam0, ?_⟩
    have e : ((lam : ℂ)) • S = cfc (fun x => lam * x) S := by
      rw [cfc_const_mul_id lam S, ← Complex.coe_smul]
    rw [e]
    apply cfc_mono (hf := hc g) (hg := hc _)
    intro x hx
    simp only [g]
    split_ifs with h0
    · rw [h0, mul_zero]
    · have hxpos : 0 < x := lt_of_le_of_ne (hnn x hx) (Ne.symm h0)
      have := hlam x hx
      rw [inv_le_iff_one_le_mul₀ hxpos] at this
      linarith [mul_comm x lam]

end S169I

section S169I2
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma S169I_decomp (A : Alg I) (X : Mat I) (hX : X ∈ A) :
    ∃ H1 H2 : Mat I, H1 ∈ A ∧ H2 ∈ A ∧ H1.IsHermitian ∧ H2.IsHermitian ∧
      X = H1 + Complex.I • H2 := by
  have hXs : Xᴴ ∈ A := by rw [← Matrix.star_eq_conjTranspose]; exact star_mem hX
  refine ⟨(1/2 : ℂ) • (X + Xᴴ), (-Complex.I/2) • (X - Xᴴ), A.smul_mem (A.add_mem hX hXs) _,
    A.smul_mem (A.sub_mem hX hXs) _, ?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp
  · unfold Matrix.IsHermitian
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    rw [show (Xᴴ - X) = -(X - Xᴴ) by abel, smul_neg, ← neg_smul]
    congr 1; simp [Complex.star_def, Complex.conj_I]; ring
  · simp only [smul_sub, smul_add, smul_smul]
    ext i j; simp; ring_nf; rw [Complex.I_sq]; ring

theorem S169I_main [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi)
    (ht : AlgebraTraceNonincreasing A Phi)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) :
    CornerTP A Phi (supp (X + Y)) ↔ tr (Phi X) = tr X ∧ tr (Phi Y) = tr Y := by
  have hS : (X + Y).PosSemidef := hXp.add hYp
  have hSA : X + Y ∈ A := A.add_mem hX hY
  obtain ⟨hPsa, hPP, hSP, lam, hlam0, hPle⟩ := S169I_P_props (X + Y) hS
  have hPA : supp (X + Y) ∈ A := by
    rw [S169I_supp_eq]; exact S169I_cfc_mem A _ hSA hS.1 _
  set S := X + Y with hSdef
  set P := supp S with hPdef
  have hPH : Pᴴ = P := hPsa
  have corner : ∀ W : Mat I, W.PosSemidef → (S - W).PosSemidef → P * W * P = W := by
    intro W hW hSW
    have hker : ∀ v, S *ᵥ v = 0 → W *ᵥ v = 0 := by
      intro v hv
      have h1 : star v ⬝ᵥ (S *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
      have h2 := hW.dotProduct_mulVec_nonneg v
      have h3 := hSW.dotProduct_mulVec_nonneg v
      rw [Matrix.sub_mulVec, dotProduct_sub, h1, zero_sub] at h3
      have : star v ⬝ᵥ (W *ᵥ v) = 0 := le_antisymm (neg_nonneg.mp h3) h2
      exact (hW.dotProduct_mulVec_zero_iff v).mp this
    have hSQ : S * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hSP, sub_self]
    have hWQ : W * (1 - P) = 0 := by
      ext i j
      have h := hker ((1 - P) *ᵥ Pi.single j 1) (by rw [Matrix.mulVec_mulVec, hSQ, Matrix.zero_mulVec])
      rw [Matrix.mulVec_mulVec] at h
      have := congrFun h i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have hWP : W * P = W := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hWQ; exact hWQ.symm
    have hPW : P * W = W := by
      have := congrArg Matrix.conjTranspose hWP
      rwa [Matrix.conjTranspose_mul, hPH, hW.1.eq] at this
    rw [hPW, hWP]
  constructor
  · intro h
    have hXc := corner X hXp (by rw [hSdef, add_sub_cancel_left]; exact hYp)
    have hYc := corner Y hYp (by rw [hSdef, add_sub_cancel_right]; exact hXp)
    have h1 := h X hX; rw [hXc] at h1
    have h2 := h Y hY; rw [hYc] at h2
    exact ⟨by simp only [tr, h1], by simp only [tr, h2]⟩
  · rintro ⟨h1, h2⟩
    let τ : Mat I →ₗ[ℂ] ℂ := Matrix.traceLinearMap I ℂ ℂ - (Matrix.traceLinearMap J ℂ ℂ).comp Phi
    have hτ : ∀ W, τ W = W.trace - (Phi W).trace := fun W => rfl
    have hτpos : ∀ W ∈ A, W.PosSemidef → 0 ≤ τ W := by
      intro W hW hWp
      rw [hτ, Complex.nonneg_iff]
      have a := Complex.nonneg_iff.mp hWp.trace_nonneg
      have b := Complex.nonneg_iff.mp (hp W hW hWp).trace_nonneg
      have c := ht W hW hWp
      simp only [tr] at c
      simp only [Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im]
      constructor
      · linarith
      · linarith [a.2, b.2]
    have hτzero : ∀ W ∈ A, W.PosSemidef → tr (Phi W) = tr W → τ W = 0 := by
      intro W hW hWp hW1
      have a := Complex.nonneg_iff.mp hWp.trace_nonneg
      have b := Complex.nonneg_iff.mp (hp W hW hWp).trace_nonneg
      simp only [tr] at hW1
      rw [hτ]; apply Complex.ext
      · simp only [Complex.sub_re, Complex.zero_re]; linarith
      · simp only [Complex.sub_im, Complex.zero_im]; linarith [a.2, b.2]
    have hτS : τ S = 0 := by
      rw [hSdef, map_add, hτzero X hX hXp h1, hτzero Y hY hYp h2, add_zero]
    have hface : ∀ W ∈ A, W.PosSemidef → ∀ t : ℝ, (((t : ℂ)) • S - W).PosSemidef → τ W = 0 := by
      intro W hW hWp t hle
      have a := hτpos W hW hWp
      have b := hτpos _ (A.sub_mem (A.smul_mem hSA _) hW) hle
      rw [map_sub, map_smul, hτS, smul_zero, zero_sub] at b
      exact le_antisymm (neg_nonneg.mp b) a
    have hPpsd : P.PosSemidef := by
      have : P = Pᴴ * P := by rw [hPH, hPP]
      rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self P
    have hlamP : (((lam : ℂ)) • S - P).PosSemidef := Matrix.le_iff.mp hPle
    have hherm : ∀ H ∈ A, H.IsHermitian → τ (P * H * P) = 0 := by
      intro H hHA hH
      set r : ℝ := ‖H‖
      have hr : 0 ≤ r := norm_nonneg _
      have halg : algebraMap ℝ (Mat I) r = ((r : ℂ)) • (1 : Mat I) := by
        rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
      have hlo : -(algebraMap ℝ (Mat I) r) ≤ H := IsSelfAdjoint.neg_algebraMap_norm_le_self hH
      have hhi : H ≤ algebraMap ℝ (Mat I) r := IsSelfAdjoint.le_algebraMap_norm_self hH
      have hPs : star P = P := hPsa
      have c1 := star_left_conjugate_le_conjugate hlo P
      have c2 := star_left_conjugate_le_conjugate hhi P
      rw [hPs, halg] at c1 c2
      have e1 : P * ((r : ℂ) • (1 : Mat I)) * P = ((r : ℂ)) • P := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
      have e2 : P * -((r : ℂ) • (1 : Mat I)) * P = -(((r : ℂ)) • P) := by
        rw [Matrix.mul_neg, Matrix.neg_mul, e1]
      rw [e2] at c1; rw [e1] at c2
      have hW1 : (P * H * P + ((r : ℂ)) • P).PosSemidef := by
        have := Matrix.le_iff.mp c1; rwa [sub_neg_eq_add] at this
      have hc2 : (((r : ℂ)) • P - P * H * P).PosSemidef := Matrix.le_iff.mp c2
      have hrc : (0 : ℂ) ≤ (r : ℂ) := by exact_mod_cast hr
      have hW1A : P * H * P + ((r : ℂ)) • P ∈ A :=
        A.add_mem (A.mul_mem (A.mul_mem hPA hHA) hPA) (A.smul_mem hPA _)
      have hτ1 : τ (P * H * P + ((r : ℂ)) • P) = 0 := by
        apply hface _ hW1A hW1 (2 * r * lam)
        have : (((2 * r * lam : ℝ) : ℂ)) • S - (P * H * P + ((r : ℂ)) • P) =
            (((r : ℂ)) • P - P * H * P) + ((2 * r : ℝ) : ℂ) • (((lam : ℂ)) • S - P) := by
          push_cast
          rw [smul_sub, smul_smul]; module
        rw [this]
        exact hc2.add (hlamP.smul (by exact_mod_cast (by linarith : (0:ℝ) ≤ 2 * r)))
      have hτ2 : τ (((r : ℂ)) • P) = 0 := by
        apply hface _ (A.smul_mem hPA _) (hPpsd.smul hrc) (r * lam)
        have : (((r * lam : ℝ) : ℂ)) • S - ((r : ℂ)) • P = ((r : ℂ)) • (((lam : ℂ)) • S - P) := by
          push_cast; rw [smul_sub, smul_smul]
        rw [this]; exact hlamP.smul hrc
      rw [map_add] at hτ1
      rw [hτ2, add_zero] at hτ1
      exact hτ1
    intro Z hZ
    obtain ⟨H1, H2, hH1A, hH2A, hH1, hH2, rfl⟩ := S169I_decomp A Z hZ
    have e : P * (H1 + Complex.I • H2) * P = P * H1 * P + Complex.I • (P * H2 * P) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have := hherm H1 hH1A hH1
    have h' := hherm H2 hH2A hH2
    have hz : τ (P * (H1 + Complex.I • H2) * P) = 0 := by
      rw [e, map_add, map_smul, this, h', smul_zero, add_zero]
    rw [hτ] at hz
    exact sub_eq_zero.mp hz |>.symm

end S169I2

end QAlgorithms.Papers.Independent.Support50.P12

end

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr)

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi) (ht : AlgebraTraceNonincreasing A Phi)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) :
    CornerTP A Phi (supp (X + Y)) ↔ tr (Phi X) = tr X ∧ tr (Phi Y) = tr Y :=
  S169I_main A B Phi hc hp ht X Y hX hY hXp hYp
