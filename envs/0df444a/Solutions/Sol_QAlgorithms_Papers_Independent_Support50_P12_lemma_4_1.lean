-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:11:52.951454+00:00
-- url     : https://prove2.me/submissions/1b50c672-312f-43f4-9dc3-8a173a5c18d0

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

lemma S169M_expand (Phi : MatrixMap I J) (X : Mat I) :
    Phi X = ∑ i, ∑ j, X i j • Phi (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

lemma S169M_dual (Phi : MatrixMap I J) (X : Mat I) (Z : Mat J) :
    (Zᴴ * Phi X).trace = ((channelAdjoint Phi Z)ᴴ * X).trace := by
  rw [S169M_expand Phi X]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, channelAdjoint,
    star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]
  ring

section S169M
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma S169M_core {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q : Matrix ι ι ℂ)
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

lemma S169M_psd (B : Alg J) (K : Mat J) (hKB : K ∈ B)
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
  have hPB : P ∈ B := S169I_cfc_mem B K hKB hsa f
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

end S169M

section S169M3
open scoped MatrixOrder

lemma S169M_sp_mul (M : Mat I) (hM : M.PosSemidef) (s t : ℝ) :
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

lemma S169M_sp_one (M : Mat I) (hM : M.PosSemidef) : supportPower M 1 = M := by
  unfold supportPower
  conv_rhs => rw [← cfc_id' (R := ℝ) (a := M) hM.1]
  apply cfc_congr
  intro x _
  simp only
  split_ifs with h <;> simp [h]

theorem S169M_main [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (Y : Mat I) (hY : Y ∈ A) (hYp : Y.PosSemidef) :
    modularContraction Phi Y (supportPower (Phi Y) (1 / 2)) = supportPower Y (1 / 2) ↔
      tr (Phi Y) = tr Y := by
  obtain ⟨⟨hΦB, -⟩, hsch⟩ := hp
  have hpos := hsch.2.1
  set K := Phi Y with hKdef
  have hKB : K ∈ B := hΦB Y
  have hKp : K.PosSemidef := by
    apply S169M_psd B K hKB
    intro Z hZ hZp
    have e := S169M_dual Phi Y Z
    rw [hZp.1.eq, (hpos Z hZ hZp).1.eq] at e
    rw [e]; exact (S169M_core _ _ (hpos Z hZ hZp) hYp).1
  obtain ⟨hQsa, hQQ, hKQ, -⟩ := S169I_P_props K hKp
  have hQA : supp K ∈ B := by rw [S169I_supp_eq]; exact S169I_cfc_mem B _ hKB hKp.1 _
  set Q := supp K
  have hQH : Qᴴ = Q := hQsa
  have hQp : Q.PosSemidef := by
    have : Q = Qᴴ * Q := by rw [hQH, hQQ]
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  set S := channelAdjoint Phi Q
  have hSp : S.PosSemidef := hpos Q hQA hQp
  have hSH : Sᴴ = S := hSp.1.eq
  have hsch2 : (S - S * S).PosSemidef := by
    have := hsch.2.2 Q hQA
    simp only [QAlgorithms.Papers.Independent.Dependency50.P28.LE, hQH, hQQ, Complex.ofReal_one,
      one_smul] at this
    rwa [hSH] at this
  have h1S : (1 - S).PosSemidef := by
    have e : 1 - S = (1 - S)ᴴ * (1 - S) + (S - S * S) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hSH]; noncomm_ring
    rw [e]; exact (Matrix.posSemidef_conjTranspose_mul_self _).add hsch2
  have hlhs : modularContraction Phi Y (supportPower K (1 / 2)) = S * supportPower Y (1 / 2) := by
    unfold modularContraction
    rw [S169M_sp_mul K hKp]; norm_num
    rfl
  have htrK : K.trace = (S * Y).trace := by
    have e := S169M_dual Phi Y Q
    rw [hQH, hSH, Matrix.trace_mul_comm, hKQ] at e
    exact e
  have hYhalf : supportPower Y (1 / 2) * supportPower Y (1 / 2) = Y := by
    rw [S169M_sp_mul Y hYp]; norm_num; exact S169M_sp_one Y hYp
  have hYmh : Y * supportPower Y (-(1 / 2)) = supportPower Y (1 / 2) := by
    have := S169M_sp_mul Y hYp 1 (-(1 / 2))
    rw [S169M_sp_one Y hYp] at this
    rw [this]; norm_num
  rw [hlhs]
  constructor
  · intro h
    have : S * Y = Y := by
      rw [← hYhalf, ← Matrix.mul_assoc, h]
    simp only [tr]; rw [htrK, this]
  · intro h
    simp only [tr] at h
    rw [htrK] at h
    have hz : ((1 - S) * Y).trace.re = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, h, sub_self]
    have h0 := (S169M_core _ _ h1S hYp).2 hz
    have : (1 - S) * supportPower Y (1 / 2) = 0 := by
      rw [← hYmh, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    exact this.symm

end S169M3

end QAlgorithms.Papers.Independent.Support50.P12

end

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J) (Phi : MatrixMap I J)
    (hp : Substochastic A B Phi) (Y : Mat I) (hY : Y ∈ A) (hYp : Y.PosSemidef) :
    modularContraction Phi Y (supportPower (Phi Y) (1 / 2)) = supportPower Y (1 / 2) ↔
      tr (Phi Y) = tr Y :=
  S169M_main A B Phi hp Y hY hYp
