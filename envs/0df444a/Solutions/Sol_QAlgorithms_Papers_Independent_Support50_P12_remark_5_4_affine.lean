-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.remark_5_4_affine
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:53:36.969062+00:00
-- url     : https://prove2.me/submissions/def5ce8b-57cf-46c0-99b7-998256f73a22

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

section R54I
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma R54_aeval_mem (A : Alg I) (S : Mat I) (hS : S ∈ A) (p : Polynomial ℝ) :
    Polynomial.aeval S p ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact A.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, IsScalarTower.algebraMap_apply ℝ ℂ (Mat I)]
    exact A.mul_mem (A.algebraMap_mem _) (A.pow_mem hS n)

lemma R54_cfc_mem (A : Alg I) (S : Mat I) (hS : S ∈ A) (hSa : IsSelfAdjoint S) (f : ℝ → ℝ) :
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
  exact R54_aeval_mem A S hS p

lemma R54_supp_eq (S : Mat I) :
    supp S = cfc (fun x : ℝ => if x = 0 then (0:ℝ) else 1) S := by
  unfold supp supportPower
  congr 1; funext x; split_ifs <;> simp [Real.rpow_zero]

lemma R54_P_props (S : Mat I) (hS : S.PosSemidef) :
    IsSelfAdjoint (supp S) ∧ supp S * supp S = supp S ∧ S * supp S = S ∧
      ∃ lam : ℝ, 0 ≤ lam ∧ supp S ≤ (lam : ℂ) • S := by
  have hSa : IsSelfAdjoint S := hS.1
  have hfin := Matrix.finite_real_spectrum (A := S)
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ S) := fun f => hfin.continuousOn f
  set g : ℝ → ℝ := fun x => if x = 0 then (0:ℝ) else 1
  rw [R54_supp_eq]
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

end R54I

lemma R54_expand (Phi : MatrixMap I J) (X : Mat I) :
    Phi X = ∑ i, ∑ j, X i j • Phi (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

lemma R54_dual (Phi : MatrixMap I J) (X : Mat I) (Z : Mat J) :
    (Zᴴ * Phi X).trace = ((channelAdjoint Phi Z)ᴴ * X).trace := by
  rw [R54_expand Phi X]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, channelAdjoint,
    star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]
  ring

section R54M
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma R54_core {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace ∧ ((P * Q).trace.re = 0 → P * Q = 0) := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP.nonneg
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  simp only [Matrix.star_eq_conjTranspose] at hC hD
  set E := C * Dᴴ
  have htE : (P * Q).trace = (Eᴴ * E).trace := by
    rw [hC, hD]
    simp only [E, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show Cᴴ * C * (Dᴴ * D) = (Cᴴ * C * Dᴴ) * D by noncomm_ring, Matrix.trace_mul_comm]
    congr 1; noncomm_ring
  have hnn := (Matrix.posSemidef_conjTranspose_mul_self E).trace_nonneg
  refine ⟨by rw [htE]; exact hnn, fun h0 => ?_⟩
  have hz : (Eᴴ * E).trace = 0 := by
    apply Complex.ext
    · rw [← htE]; simpa using h0
    · simpa using (Complex.nonneg_iff.mp hnn).2.symm
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff] at hz
  rw [hC, hD, show Cᴴ * C * (Dᴴ * D) = Cᴴ * (C * Dᴴ) * D by noncomm_ring]
  change Cᴴ * E * D = 0
  rw [hz]; simp

lemma R54_psd (B : Alg J) (K : Mat J) (hKB : K ∈ B)
    (htr : ∀ Z ∈ B, Z.PosSemidef → 0 ≤ (Z * K).trace) : K.PosSemidef := by
  have hmemS : ∀ x ∈ B, xᴴ ∈ B := fun x hx => by
    rw [← Matrix.star_eq_conjTranspose]; exact star_mem hx
  -- Hermitian Z ∈ B gives real trace
  have hreal : ∀ Z ∈ B, Z.IsHermitian → (Z * K).trace.im = 0 := by
    intro Z hZB hZ
    set r : ℝ := ‖Z‖
    have h0 : 0 ≤ Z + algebraMap ℝ (Mat J) r := by
      have := IsSelfAdjoint.neg_algebraMap_norm_le_self (a := Z) hZ
      rw [← sub_nonneg] at this; simpa [sub_neg_eq_add] using this
    have halg : algebraMap ℝ (Mat J) r = ((r : ℂ)) • (1 : Mat J) := by
      rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
    rw [halg] at h0
    have a1 := Complex.nonneg_iff.mp (htr _ (B.add_mem hZB (B.smul_mem B.one_mem _))
      (Matrix.nonneg_iff_posSemidef.mp h0))
    have a2 := Complex.nonneg_iff.mp (htr _ B.one_mem Matrix.PosSemidef.one)
    rw [Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, Matrix.one_mul] at a1
    rw [Matrix.one_mul] at a2
    simp only [Complex.add_im, smul_eq_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at a1
    rw [← a2.2, mul_zero, add_zero] at a1
    exact a1.2.symm
  set a := (K * K).trace
  set b := (Kᴴ * K).trace
  have hb := Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self K).trace_nonneg
  have h1 := hreal (K + Kᴴ) (B.add_mem hKB (hmemS K hKB)) (by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm])
  have h2 := hreal (Complex.I • (K - Kᴴ)) (B.smul_mem (B.sub_mem hKB (hmemS K hKB)) _) (by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      Complex.star_def, Complex.conj_I, show Kᴴ - K = -(K - Kᴴ) by abel, smul_neg, neg_smul, neg_neg])
  rw [Matrix.add_mul, Matrix.trace_add] at h1
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_smul, Matrix.trace_sub] at h2
  simp only [Complex.add_im, smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_add, Complex.sub_re] at h1 h2
  have hH : K.IsHermitian := by
    have hE : ((K - Kᴴ)ᴴ * (K - Kᴴ)).trace = 0 := by
      have e : ((K - Kᴴ)ᴴ * (K - Kᴴ)).trace = b - (Kᴴ * Kᴴ).trace - a + (K * Kᴴ).trace := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, a, b]; ring
      have e2 : (Kᴴ * Kᴴ).trace = star a := by
        rw [← Matrix.conjTranspose_mul, Matrix.trace_conjTranspose]
      have e3 : (K * Kᴴ).trace = b := Matrix.trace_mul_comm _ _
      rw [e, e2, e3]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re, Complex.zero_re]
        linarith
      · simp only [Complex.add_im, Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im]
        linarith [hb.2]
    rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero] at hE
    exact hE.symm
  have hsa : IsSelfAdjoint K := hH
  have hfin := Matrix.finite_real_spectrum (A := K)
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ K) := fun f => hfin.continuousOn f
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) K hsa]
  intro l hl
  set f : ℝ → ℝ := fun x => if x = l then 1 else 0
  set P := cfc f K
  have hPB : P ∈ B := R54_cfc_mem B K hKB hsa f
  have hPsa : IsSelfAdjoint P := cfc_predicate _ _
  have hPP : P * P = P := by
    rw [← cfc_mul f f K (hc f) (hc f)]
    exact cfc_congr fun x _ => by simp only [f]; split_ifs <;> simp
  have hPpsd : P.PosSemidef := by
    have hPH : Pᴴ = P := hPsa
    have : P = Pᴴ * P := by rw [hPH, hPP]
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hPK : P * K = ((l : ℂ)) • P := by
    have hm := cfc_mul f (fun x : ℝ => x) K (hc f) (hc _)
    rw [cfc_id' (R := ℝ) (a := K)] at hm
    rw [← hm, Complex.coe_smul, ← cfc_const_mul l f K (hc f)]
    exact cfc_congr fun x _ => by simp only [f]; split_ifs with h <;> simp [h]
  have hP0 : P ≠ 0 := by
    intro h0
    have := eqOn_of_cfc_eq_cfc (a := K) (f := f) (g := 0) (by rw [cfc_zero]; exact h0)
      (hf := hc f) (hg := hc 0) (ha := hsa) hl
    simp [f] at this
  have htP : 0 < P.trace.re := by
    have hPH : Pᴴ = P := hPsa
    have e : P.trace = (Pᴴ * P).trace := by rw [hPH, hPP]
    have hn := Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self P).trace_nonneg
    rcases eq_or_lt_of_le hn.1 with h | h
    · exfalso; apply hP0
      have : (Pᴴ * P).trace = 0 := Complex.ext (by simpa using h.symm) (by simpa using hn.2.symm)
      exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp this
    · rw [e]; exact h
  have := Complex.nonneg_iff.mp (htr P hPB hPpsd)
  rw [hPK, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at this
  by_contra hneg
  push Not at hneg
  nlinarith [this.1]

end R54M

section R54M3
open scoped MatrixOrder

lemma R54_sp_mul (M : Mat I) (hM : M.PosSemidef) (s t : ℝ) :
    supportPower M s * supportPower M t = supportPower M (s + t) := by
  have hfin := Matrix.finite_real_spectrum (A := M)
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ M) := fun f => hfin.continuousOn f
  have hnn : ∀ x ∈ spectrum ℝ M, 0 ≤ x := fun x hx =>
    spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hM) hx
  unfold supportPower
  rw [← cfc_mul _ _ M (hc _) (hc _)]
  apply cfc_congr
  intro x hx
  simp only
  split_ifs with h
  · simp
  · have hx0 : 0 < x := lt_of_le_of_ne (hnn x hx) (Ne.symm h)
    exact (Real.rpow_add hx0 s t).symm

lemma R54_sp_one (M : Mat I) (hM : M.PosSemidef) : supportPower M 1 = M := by
  unfold supportPower
  conv_rhs => rw [← cfc_id' (R := ℝ) (a := M) hM.1]
  apply cfc_congr
  intro x _
  simp only
  split_ifs with h <;> simp [h]

end R54M3

section R54A
open scoped MatrixOrder

lemma R54_proj (H : Mat I) (hH : H.IsHermitian) (α : ℝ) :
    spectralProjector H α = cfc (fun x : ℝ => if x = α then (1:ℝ) else 0) H := by
  have hsa : IsSelfAdjoint H := hH
  have hfin := Matrix.finite_real_spectrum (A := H)
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ H) := fun f => hfin.continuousOn f
  set g : ℝ → ℝ := fun x => if x = α then (1:ℝ) else 0
  set P := cfc g H
  have hPsa : Pᴴ = P := (cfc_predicate g H : IsSelfAdjoint P)
  have hPP : P * P = P := by
    rw [← cfc_mul g g H (hc g) (hc g)]
    exact cfc_congr fun x _ => by simp only [g]; split_ifs <;> simp
  have hHP : H * P = ((α : ℂ)) • P := by
    have hm := cfc_mul (fun x : ℝ => x) g H (hc _) (hc g)
    rw [cfc_id' (R := ℝ) (a := H)] at hm
    rw [← hm, Complex.coe_smul, ← cfc_const_mul α g H (hc g)]
    exact cfc_congr fun x _ => by simp only [g]; split_ifs with h <;> simp [h]
  set h : ℝ → ℝ := fun x => if x = α then 0 else (x - α)⁻¹
  set R := cfc h H
  have hR : 1 - P = R * H - ((α : ℂ)) • R := by
    have e1 : R * H = cfc (fun x => h x * x) H := by
      rw [cfc_mul h (fun x : ℝ => x) H (hc h) (hc _), cfc_id' (R := ℝ) (a := H)]
    have e2 : cfc (fun x => h x * x) H = cfc (fun x => (1 - g x) + α * h x) H :=
      cfc_congr fun x _ => by
        simp only [g, h]
        split_ifs with hx
        · simp
        · have : x - α ≠ 0 := sub_ne_zero.mpr hx
          field_simp; ring
    rw [e1, e2, cfc_add (hf := hc _) (hg := hc _), cfc_sub (hf := hc _) (hg := hc _), cfc_const_one ℝ H,
      cfc_const_mul α h H (hc h), Complex.coe_smul]
    abel
  have hfix : ∀ v, H *ᵥ v = ((α : ℂ)) • v → P *ᵥ v = v := by
    intro v hv
    have : (1 - P) *ᵥ v = 0 := by
      rw [hR, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.smul_mulVec, Matrix.mulVec_smul,
        sub_self]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this.symm
  unfold spectralProjector QAlgorithms.eigenProjection
  apply Matrix.toEuclideanLin.injective
  rw [LinearEquiv.apply_symm_apply]
  ext1 u
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [iSup_singleton, Module.End.mem_eigenspace_iff]
    change WithLp.toLp 2 (H *ᵥ (P *ᵥ WithLp.ofLp u)) = (α : ℂ) • WithLp.toLp 2 (P *ᵥ WithLp.ofLp u)
    rw [Matrix.mulVec_mulVec, hHP]
    ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro w hw
    rw [iSup_singleton, Module.End.mem_eigenspace_iff] at hw
    have hw' : H *ᵥ WithLp.ofLp w = ((α : ℂ)) • WithLp.ofLp w := by
      have := congrArg WithLp.ofLp hw
      exact this
    have hPw := hfix _ hw'
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change WithLp.ofLp w ⬝ᵥ star (WithLp.ofLp u - P *ᵥ WithLp.ofLp u) = 0
    rw [star_sub, Matrix.star_mulVec, hPsa, dotProduct_sub,
      dotProduct_comm (WithLp.ofLp w) (star (WithLp.ofLp u) ᵥ* P),
      ← Matrix.dotProduct_mulVec, hPw, dotProduct_comm, sub_self]

end R54A

section R54B
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma R54_sum (H : Mat I) (hH : H.IsHermitian) (g : ℝ → ℝ) :
    ∑ α ∈ spec H, ((g α : ℝ) : ℂ) • spectralProjector H α = cfc g H := by
  have hfin := Matrix.finite_real_spectrum (A := H)
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ H) := fun f => hfin.continuousOn f
  unfold spec
  rw [dif_pos hH]
  have e : ∀ α, ((g α : ℝ) : ℂ) • spectralProjector H α =
      cfc (fun x : ℝ => g α * (if x = α then (1:ℝ) else 0)) H := by
    intro α
    rw [R54_proj H hH α, cfc_const_mul (g α) _ H (hc _), Complex.coe_smul]
  simp only [e]
  rw [← cfc_sum (hf := fun i _ => hc _)]
  apply cfc_congr
  intro x hx
  rw [hH.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  simp only [Finset.sum_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

lemma R54_sum_one (H : Mat I) (hH : H.IsHermitian) :
    ∑ α ∈ spec H, spectralProjector H α = 1 := by
  have := R54_sum H hH (fun _ => 1)
  simpa [cfc_const_one ℝ H] using this

lemma R54_sum_id (H : Mat I) (hH : H.IsHermitian) :
    ∑ α ∈ spec H, (α : ℂ) • spectralProjector H α = H := by
  have := R54_sum H hH (fun x => x)
  rwa [cfc_id' ℝ H] at this

lemma R54_hs (A B : Mat I) : hs A B = (Aᴴ * B).trace := by
  unfold hs QAlgorithms.Papers.Independent.Frontier18.P17.res
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma R54_inv (Y : Mat I) : cfc (fun x : ℝ => x⁻¹) Y = supportPower Y (-1) := by
  unfold supportPower
  apply cfc_congr
  intro x _
  simp only
  split_ifs with h
  · simp [h]
  · rw [Real.rpow_eq_pow, Real.rpow_neg_one]

lemma R54_XP (X Y : Mat I) (hY : Y.PosSemidef) (hs : Supports X Y) : X * supp Y = X := by
  obtain ⟨-, -, hYP, -⟩ := R54_P_props Y hY
  have key : ∀ v, (X - X * supp Y) *ᵥ v = 0 := by
    intro v
    have h1 : Y *ᵥ ((1 - supp Y) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hYP, sub_self, Matrix.zero_mulVec]
    have h2 := hs _ h1
    rwa [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one] at h2
  have h0 : X - X * supp Y = 0 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  exact (sub_eq_zero.mp h0).symm

lemma R54_PX (X Y : Mat I) (hX : X.IsHermitian) (hY : Y.PosSemidef) (hs : Supports X Y) :
    supp Y * X = X := by
  obtain ⟨hPsa, -, -, -⟩ := R54_P_props Y hY
  have := congrArg Matrix.conjTranspose (R54_XP X Y hY hs)
  rwa [Matrix.conjTranspose_mul, show (supp Y)ᴴ = supp Y from hPsa, hX.eq] at this

lemma R54_quasi (X Y : Mat I) (hX : X.IsHermitian) (hY : Y.PosSemidef) (hs : Supports X Y)
    (a b : ℝ) : quasi (fun x => b + a * x) X Y = b * tr Y + a * tr X := by
  have hYh : Y.IsHermitian := hY.1
  set Z := supportPower Y (1 / 2) with hZ
  set W := supportPower Y (-1) with hW
  have hmod : modular (fun x => b + a * x) X Y Z = (b : ℂ) • Z + (a : ℂ) • (X * Z * W) := by
    unfold modular
    have hterm : ∀ α β : ℝ, (((b + a * (α / β) : ℝ)) : ℂ) •
        (spectralProjector X α * Z * spectralProjector Y β) =
        (b : ℂ) • (spectralProjector X α * Z * spectralProjector Y β) +
        (a : ℂ) • (((α : ℂ) • spectralProjector X α) * Z *
          (((β⁻¹ : ℝ) : ℂ) • spectralProjector Y β)) := by
      intro α β
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, ← add_smul]
      congr 1; push_cast; ring
    simp only [hterm, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [R54_sum_one X hX, R54_sum_one Y hYh, R54_sum_id X hX, R54_sum Y hYh (fun x => x⁻¹),
      R54_inv, Matrix.one_mul, Matrix.mul_one]
  have hZH : Zᴴ = Z := (cfc_predicate _ _ : IsSelfAdjoint Z)
  have hZZ : Z * Z = Y := by
    rw [hZ, R54_sp_mul Y hY]; norm_num; exact R54_sp_one Y hY
  have hZWZ : Z * W * Z = supp Y := by
    rw [hZ, hW, R54_sp_mul Y hY, R54_sp_mul Y hY]; norm_num; rfl
  have htr2 : (Z * (X * Z * W)).trace = X.trace := by
    rw [Matrix.trace_mul_comm, show X * Z * W * Z = X * (Z * W * Z) by noncomm_ring, hZWZ,
      R54_XP X Y hY hs]
  unfold quasi
  rw [hmod, R54_hs, hZH, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, hZZ, htr2]
  simp [tr]

lemma R54_div (X Y : Mat I) (hX : X.IsHermitian) (hY : Y.PosSemidef) (hs : Supports X Y)
    (a b : ℝ) : div (fun x => b + a * x) X Y = ((b * tr Y + a * tr X : ℝ) : EReal) := by
  unfold div
  rw [if_pos hs, R54_quasi X Y hX hY hs]

lemma R54_pos (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) (hp : Substochastic A B Phi)
    (X : Mat I) (hXp : X.PosSemidef) : (Phi X).PosSemidef := by
  obtain ⟨⟨hΦB, -⟩, hsch⟩ := hp
  have hpos := hsch.2.1
  apply R54_psd B (Phi X) (hΦB X)
  intro Z hZ hZp
  have e := R54_dual Phi X Z
  rw [hZp.1.eq, (hpos Z hZ hZp).1.eq] at e
  rw [e]; exact (R54_core _ _ (hpos Z hZ hZp) hXp).1

lemma R54_dom (X Y : Mat I) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (hs : Supports X Y) :
    ∃ c : ℝ, 0 ≤ c ∧ X ≤ (c : ℂ) • Y := by
  obtain ⟨hPsa, hPP, -, lam, hlam0, hPle⟩ := R54_P_props Y hYp
  set r : ℝ := ‖X‖
  refine ⟨r * lam, mul_nonneg (norm_nonneg _) hlam0, ?_⟩
  have hhi : X ≤ algebraMap ℝ (Mat I) r := IsSelfAdjoint.le_algebraMap_norm_self hXp.1
  have halg : algebraMap ℝ (Mat I) r = ((r : ℂ)) • (1 : Mat I) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [halg] at hhi
  have c2 := star_left_conjugate_le_conjugate hhi (supp Y)
  have hPs : star (supp Y) = supp Y := hPsa
  rw [hPs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP] at c2
  rw [R54_PX X Y hXp.1 hYp hs, R54_XP X Y hYp hs] at c2
  calc X ≤ ((r : ℂ)) • supp Y := c2
    _ ≤ ((r : ℂ)) • (((lam : ℂ)) • Y) := by
        rw [Matrix.le_iff, ← smul_sub]
        exact (Matrix.le_iff.mp hPle).smul (by exact_mod_cast norm_nonneg X)
    _ = (((r * lam : ℝ)) : ℂ) • Y := by rw [smul_smul]; push_cast; rfl

lemma R54_supp_map (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) (hp : Substochastic A B Phi)
    (X Y : Mat I) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (hs : Supports X Y) :
    Supports (Phi X) (Phi Y) := by
  intro v hv
  obtain ⟨c, hc, hle⟩ := R54_dom X Y hXp hYp hs
  have hpsd := R54_pos A B Phi hp _ (Matrix.le_iff.mp hle)
  have h1 := hpsd.dotProduct_mulVec_nonneg v
  rw [map_sub, map_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, dotProduct_sub,
    dotProduct_zero, zero_sub] at h1
  have hXp' := R54_pos A B Phi hp X hXp
  exact (hXp'.dotProduct_mulVec_zero_iff v).mp
    (le_antisymm (neg_nonneg.mp h1) (hXp'.dotProduct_mulVec_nonneg v))

lemma R54_trace (A : Alg I) (B : Alg J) (Phi : MatrixMap I J) (hp : Substochastic A B Phi)
    (X Y : Mat I) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (htr : tr (Phi Y) = tr Y)
    (hs : Supports X Y) : tr (Phi X) = tr X := by
  obtain ⟨⟨hΦB, -⟩, hsch⟩ := hp
  set T := channelAdjoint Phi 1
  have hTp : T.PosSemidef := hsch.2.1 1 B.one_mem Matrix.PosSemidef.one
  have hTH : Tᴴ = T := hTp.1.eq
  have hsch2 : (T - T * T).PosSemidef := by
    have := hsch.2.2 1 B.one_mem
    simp only [QAlgorithms.Papers.Independent.Dependency50.P28.LE, Matrix.conjTranspose_one,
      Matrix.one_mul, Complex.ofReal_one, one_smul] at this
    rwa [hTH] at this
  have h1T : (1 - T).PosSemidef := by
    have e : 1 - T = (1 - T)ᴴ * (1 - T) + (T - T * T) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hTH]; noncomm_ring
    rw [e]; exact (Matrix.posSemidef_conjTranspose_mul_self _).add hsch2
  have hdual : ∀ M : Mat I, (Phi M).trace = (T * M).trace := by
    intro M
    have e := R54_dual Phi M 1
    rwa [Matrix.conjTranspose_one, Matrix.one_mul, hTH] at e
  have hz : ((1 - T) * Y).trace.re = 0 := by
    simp only [tr] at htr
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, ← hdual, htr, sub_self]
  have h0 := (R54_core _ _ h1T hYp).2 hz
  have hP' : Y * supportPower Y (-1) = supp Y := by
    have := R54_sp_mul Y hYp 1 (-1)
    rw [R54_sp_one Y hYp, show (1:ℝ) + -1 = 0 by norm_num] at this
    exact this
  have hPX := R54_PX X Y hXp.1 hYp hs
  have hTX : (1 - T) * X = 0 := by
    rw [← hPX, ← hP', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul, Matrix.zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hTX
  simp only [tr]
  rw [hdual, ← hTX]

end R54B

end QAlgorithms.Papers.Independent.Support50.P12

end

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

open QAlgorithms.Papers.Independent.Support50.P12 in
/-- Remark 5.4 (affine case), PDF p.25: affine equality is automatic on a supported
pair, including the displayed trace formula. No reversibility conclusion is imposed. -/
theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A)
    (hXp : X.PosSemidef) (hYp : Y.PosSemidef) (htr : tr (Phi Y) = tr Y)
    (hs : Supports X Y) (a b : ℝ) :
    tr (Phi X) = tr X ∧
    div (fun x => b + a * x) (Phi X) (Phi Y) = ((b * tr (Phi Y) + a * tr (Phi X) : ℝ) : EReal) ∧
    div (fun x => b + a * x) (Phi X) (Phi Y) = div (fun x => b + a * x) X Y ∧
    div (fun x => b + a * x) X Y = ((b * tr Y + a * tr X : ℝ) : EReal) := by
  have h1 := R54_trace A B Phi hp X Y hXp hYp htr hs
  have hΦX := R54_pos A B Phi hp X hXp
  have hΦY := R54_pos A B Phi hp Y hYp
  have hsΦ := R54_supp_map A B Phi hp X Y hXp hYp hs
  refine ⟨h1, R54_div _ _ hΦX.1 hΦY hsΦ a b, ?_, R54_div X Y hXp.1 hYp hs a b⟩
  rw [R54_div _ _ hΦX.1 hΦY hsΦ a b, R54_div X Y hXp.1 hYp hs a b, h1, htr]

