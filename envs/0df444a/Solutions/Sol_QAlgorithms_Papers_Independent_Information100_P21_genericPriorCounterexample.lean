-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.genericPriorCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T12:58:31.664185+00:00
-- url     : https://prove2.me/submissions/1f696db3-0adb-4dd9-9597-6bcf3b1fe6a7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace X7A18
open QAlgorithms.Papers.Independent.Information100.P21 Matrix

@[simp] lemma xs_00 (a b c d w z : ℝ) : xstate a b c d w z (0,0) (0,0) = ((a:ℝ):ℂ) := rfl
@[simp] lemma xs_01 (a b c d w z : ℝ) : xstate a b c d w z (0,0) (0,1) = 0 := rfl
@[simp] lemma xs_02 (a b c d w z : ℝ) : xstate a b c d w z (0,0) (1,0) = 0 := rfl
@[simp] lemma xs_03 (a b c d w z : ℝ) : xstate a b c d w z (0,0) (1,1) = ((w:ℝ):ℂ) := rfl
@[simp] lemma xs_10 (a b c d w z : ℝ) : xstate a b c d w z (0,1) (0,0) = 0 := rfl
@[simp] lemma xs_11 (a b c d w z : ℝ) : xstate a b c d w z (0,1) (0,1) = ((b:ℝ):ℂ) := rfl
@[simp] lemma xs_12 (a b c d w z : ℝ) : xstate a b c d w z (0,1) (1,0) = ((z:ℝ):ℂ) := rfl
@[simp] lemma xs_13 (a b c d w z : ℝ) : xstate a b c d w z (0,1) (1,1) = 0 := rfl
@[simp] lemma xs_20 (a b c d w z : ℝ) : xstate a b c d w z (1,0) (0,0) = 0 := rfl
@[simp] lemma xs_21 (a b c d w z : ℝ) : xstate a b c d w z (1,0) (0,1) = ((z:ℝ):ℂ) := rfl
@[simp] lemma xs_22 (a b c d w z : ℝ) : xstate a b c d w z (1,0) (1,0) = ((c:ℝ):ℂ) := rfl
@[simp] lemma xs_23 (a b c d w z : ℝ) : xstate a b c d w z (1,0) (1,1) = 0 := rfl
@[simp] lemma xs_30 (a b c d w z : ℝ) : xstate a b c d w z (1,1) (0,0) = ((w:ℝ):ℂ) := rfl
@[simp] lemma xs_31 (a b c d w z : ℝ) : xstate a b c d w z (1,1) (0,1) = 0 := rfl
@[simp] lemma xs_32 (a b c d w z : ℝ) : xstate a b c d w z (1,1) (1,0) = 0 := rfl
@[simp] lemma xs_33 (a b c d w z : ℝ) : xstate a b c d w z (1,1) (1,1) = ((d:ℝ):ℂ) := rfl


lemma sa_00 : (Fin.succAbove (0:Fin 4) (0:Fin 3)) = (1:Fin 4) := rfl
lemma sa_01 : (Fin.succAbove (0:Fin 4) (1:Fin 3)) = (2:Fin 4) := rfl
lemma sa_02 : (Fin.succAbove (0:Fin 4) (2:Fin 3)) = (3:Fin 4) := rfl
lemma sa_10 : (Fin.succAbove (1:Fin 4) (0:Fin 3)) = (0:Fin 4) := rfl
lemma sa_11 : (Fin.succAbove (1:Fin 4) (1:Fin 3)) = (2:Fin 4) := rfl
lemma sa_12 : (Fin.succAbove (1:Fin 4) (2:Fin 3)) = (3:Fin 4) := rfl
lemma sa_20 : (Fin.succAbove (2:Fin 4) (0:Fin 3)) = (0:Fin 4) := rfl
lemma sa_21 : (Fin.succAbove (2:Fin 4) (1:Fin 3)) = (1:Fin 4) := rfl
lemma sa_22 : (Fin.succAbove (2:Fin 4) (2:Fin 3)) = (3:Fin 4) := rfl
lemma sa_30 : (Fin.succAbove (3:Fin 4) (0:Fin 3)) = (0:Fin 4) := rfl
lemma sa_31 : (Fin.succAbove (3:Fin 4) (1:Fin 3)) = (1:Fin 4) := rfl
lemma sa_32 : (Fin.succAbove (3:Fin 4) (2:Fin 3)) = (2:Fin 4) := rfl

lemma det_X (a b c d w z : ℝ) (r : ℂ) :
    (scalar QQ r - xstate a b c d w z).det = ((r-a)*(r-d) - (w:ℂ)^2) * ((r-b)*(r-c) - (z:ℂ)^2) := by
  rw [← Matrix.det_reindex_self (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4)]
  have : reindex finProdFinEquiv finProdFinEquiv (scalar QQ r - xstate a b c d w z) =
      !![r-a, 0, 0, -w; 0, r-b, -z, 0; 0, -z, r-c, 0; -w, 0, 0, r-d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> rfl
  rw [this]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, sa_10, sa_11, sa_12, sa_20, sa_21, sa_22, sa_30, sa_31, sa_32]
  ring

lemma pt_xstate (a b c d w z : ℝ) : pt (xstate a b c d w z) = xstate a b c d z w := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [pt]

lemma xstate_add (a b c d w z a' b' c' d' w' z' : ℝ) :
    xstate a b c d w z + xstate a' b' c' d' w' z' = xstate (a+a') (b+b') (c+c') (d+d') (w+w') (z+z') := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp

lemma xstate_smul (t a b c d w z : ℝ) :
    (t:ℂ) • xstate a b c d w z = xstate (t*a) (t*b) (t*c) (t*d) (t*w) (t*z) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp

lemma xstate_trace (a b c d w z : ℝ) : (xstate a b c d w z).trace = ((a+b+c+d : ℝ) : ℂ) := by
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]; ring

lemma xstate_trace_mul (a b c d w z a' b' c' d' w' z' : ℝ) :
    (xstate a b c d w z * xstate a' b' c' d' w' z').trace =
      ((a*a'+b*b'+c*c'+d*d'+2*w*w'+2*z*z' : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]; ring

def e1 : QQ → ℂ := fun p => ![![1,0],![0,1]] p.1 p.2
def e2 : QQ → ℂ := fun p => ![![0,1],![1,0]] p.1 p.2

lemma xstate_decomp (a b c d w z : ℝ) : xstate a b c d w z =
    (w:ℂ) • vecMulVec e1 (star e1) + (z:ℂ) • vecMulVec e2 (star e2) +
    diagonal (fun p => ![![((a - w : ℝ) : ℂ), ((b-z:ℝ):ℂ)],![((c-z:ℝ):ℂ), ((d-w:ℝ):ℂ)]] p.1 p.2) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [e1, e2, vecMulVec, diagonal]

lemma xstate_psd {a b c d w z : ℝ} (hw : 0 ≤ w) (hz : 0 ≤ z) (ha : w ≤ a) (hd : w ≤ d)
    (hb : z ≤ b) (hc : z ≤ c) : (xstate a b c d w z).PosSemidef := by
  rw [xstate_decomp]
  refine ((PosSemidef.smul (posSemidef_vecMulVec_self_star e1) ?_).add
    (PosSemidef.smul (posSemidef_vecMulVec_self_star e2) ?_)).add (PosSemidef.diagonal ?_)
  · exact_mod_cast hw
  · exact_mod_cast hz
  · intro ⟨p1, p2⟩
    fin_cases p1 <;> fin_cases p2 <;> simp <;> linarith

lemma rhoEx_eq : rhoEx = xstate (3/8) (1/5) (1/20) (3/8) (1/4) (1/100) := rfl

lemma rhoEx_density : QAlgorithms.IsDensityMatrix rhoEx := by
  refine ⟨xstate_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), ?_⟩
  rw [rhoEx_eq, xstate_trace]; norm_num

lemma rhoEx_posDef : rhoEx.PosDef := by
  have h : rhoEx = ((1/25 : ℝ) : ℂ) • (1 : Op QQ) +
      xstate (3/8-1/25) (1/5-1/25) (1/20-1/25) (3/8-1/25) (1/4) (1/100) := by
    rw [rhoEx_eq]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [Matrix.one_apply] <;> norm_num
  rw [h]
  refine PosDef.add_posSemidef (PosDef.one.smul (by norm_num)) ?_
  exact xstate_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

lemma rhoEx_charpoly : rhoEx.charpoly =
    (Polynomial.X - Polynomial.C (5/8 : ℂ)) *
    (Polynomial.X - Polynomial.C (1/8 : ℂ)) *
    (Polynomial.X - Polynomial.C ((1/8 + Real.sqrt 229/200 : ℝ) : ℂ)) *
    (Polynomial.X - Polynomial.C ((1/8 - Real.sqrt 229/200 : ℝ) : ℂ)) := by
  apply Polynomial.funext
  intro r
  rw [Matrix.eval_charpoly, rhoEx_eq, det_X]
  have h : ((Real.sqrt 229 : ℝ) : ℂ)^2 = 229 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  push_cast
  linear_combination ((r-5/8)*(r-1/8)/40000) * h

def Lw (X : Op QQ) : ℝ := (X (0,1) (0,1) + X (1,0) (1,0) - X (0,0) (1,1) - X (1,1) (0,0)).re

def xw : QQ → ℂ := fun p => ![![0,1],![-1,0]] p.1 p.2

lemma Lw_kron {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Lw (Matrix.kronecker A B) := by
  have h : 0 ≤ star xw ⬝ᵥ (Matrix.kronecker A Bᵀ *ᵥ xw) :=
    (posSemidef_iff_dotProduct_mulVec.mp (hA.kronecker hB.transpose)).2 xw
  have e : star xw ⬝ᵥ (Matrix.kronecker A Bᵀ *ᵥ xw) =
      A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 0 1 - A 1 0 * B 1 0 := by
    simp [dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, xw, kronecker]
    ring
  rw [e] at h
  have h2 := (Complex.nonneg_iff.mp h).1
  simp only [Lw, kronecker, kroneckerMap_apply]
  convert h2 using 2

lemma Lw_sep {X : Op QQ} (h : QAlgorithms.Entanglement.IsSeparablePositive X) : 0 ≤ Lw X := by
  obtain ⟨q, w, A, B, hw, hAB, rfl⟩ := h
  have : Lw (∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)) =
      ∑ j, w j * Lw (Matrix.kronecker (A j) (B j)) := by
    simp only [Lw, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, Complex.re_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [← mul_add, ← mul_sub, Complex.re_ofReal_mul]
  rw [this]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (Lw_kron (hAB j).1.1 (hAB j).2.1))

lemma Lw_density {ω : Op QQ} (h : QAlgorithms.IsDensityMatrix ω) : Lw ω ≤ 1 := by
  have h1 := (posSemidef_iff_dotProduct_mulVec.mp h.1).2 e1
  have e : star e1 ⬝ᵥ (ω *ᵥ e1) = ω (0,0) (0,0) + ω (0,0) (1,1) + ω (1,1) (0,0) + ω (1,1) (1,1) := by
    simp [dotProduct, mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, e1]
    ring
  rw [e] at h1
  have h2 := (Complex.nonneg_iff.mp h1).1
  have ht := congrArg Complex.re h.2
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] at ht h2
  simp only [Lw, Complex.sub_re, Complex.add_re]
  linarith

lemma Lw_mix (ρ ω : Op QQ) (s : ℝ) : Lw (mix ρ ω s) = (1+s)⁻¹ * (Lw ρ + s * Lw ω) := by
  simp only [Lw, mix, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  simp only [← mul_add, ← mul_sub, Complex.re_ofReal_mul, Complex.add_re, Complex.sub_re]
  ring

lemma Lw_rhoEx : Lw rhoEx = -1/4 := by
  simp [rhoEx_eq, Lw]; norm_num

lemma rob_lb (std : Bool) (s : ℝ) (hs : s ∈ {s : ℝ | 0 ≤ s ∧ ∃ omega : Op QQ, QAlgorithms.IsDensityMatrix omega ∧
    (std = true → omega ∈ {X : Op QQ | sep X}) ∧ mix rhoEx omega s ∈ {X : Op QQ | sep X}}) : 1/4 ≤ s := by
  obtain ⟨hs0, ω, hω, -, hm⟩ := hs
  have h1 := Lw_sep hm.1
  rw [Lw_mix, Lw_rhoEx] at h1
  have h2 := Lw_density hω
  have hpos : 0 < (1+s)⁻¹ := by positivity
  have h3 : 0 ≤ -1/4 + s * Lw ω := by
    by_contra hc; push_neg at hc; nlinarith
  nlinarith

def D0 : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1,0]
def D1 : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![0,1]

lemma D0_dens : QAlgorithms.IsDensityMatrix D0 :=
  ⟨PosSemidef.diagonal (by intro i; fin_cases i <;> simp), by simp [D0, Matrix.trace]⟩
lemma D1_dens : QAlgorithms.IsDensityMatrix D1 :=
  ⟨PosSemidef.diagonal (by intro i; fin_cases i <;> simp), by simp [D1, Matrix.trace]⟩

def Pm (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • vecMulVec ![1,u] (star ![1,u])

lemma Pm_dens (u : ℂ) (hu : u * star u = 1) : QAlgorithms.IsDensityMatrix (Pm u) := by
  refine ⟨PosSemidef.smul (posSemidef_vecMulVec_self_star _)
    (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩), ?_⟩
  simp [Pm, Matrix.trace, vecMulVec, Fin.sum_univ_two]
  have : u * (starRingEnd ℂ) u = 1 := hu
  rw [this]; norm_num

def omega0 : Op QQ := xstate 0 (1/5) (4/5) 0 0 0

lemma omega0_dens : QAlgorithms.IsDensityMatrix omega0 :=
  ⟨xstate_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    by rw [omega0, xstate_trace]; norm_num⟩

lemma omega0_sep : sep omega0 := by
  refine ⟨⟨2, ![1/5, 4/5], ![D0, D1], ![D1, D0], ?_, ?_, ?_⟩, ?_⟩
  · intro j; fin_cases j <;> norm_num
  · intro j; fin_cases j
    · exact ⟨D0_dens, D1_dens⟩
    · exact ⟨D1_dens, D0_dens⟩
  · ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [omega0, Fin.sum_univ_two, kronecker, D0, D1]
  · rw [omega0, xstate_trace]; norm_num

lemma mix_eq : mix rhoEx omega0 (1/4) = xstate (3/10) (1/5) (1/5) (3/10) (1/5) (1/125) := by
  rw [mix, rhoEx_eq, omega0]
  have : ((1/4 : ℝ) : ℂ) = ((1/4:ℝ):ℂ) := rfl
  rw [xstate_smul, xstate_add, xstate_smul]
  congr 1 <;> norm_num

lemma mix_sep : sep (mix rhoEx omega0 (1/4)) := by
  refine ⟨⟨8, ![24/125, 24/125, 24/125, 24/125, 2/125, 2/125, 1/10, 1/10],
    ![Pm 1, Pm Complex.I, Pm (-1), Pm (-Complex.I), Pm 1, Pm (-1), D0, D1],
    ![Pm 1, Pm (-Complex.I), Pm (-1), Pm Complex.I, Pm 1, Pm (-1), D0, D1], ?_, ?_, ?_⟩, ?_⟩
  · intro j; fin_cases j <;> norm_num
  · have h1 : (1:ℂ) * star 1 = 1 := by simp
    have h2 : Complex.I * star Complex.I = 1 := by simp [Complex.ext_iff]
    have h3 : (-1:ℂ) * star (-1) = 1 := by simp
    have h4 : (-Complex.I) * star (-Complex.I) = 1 := by simp [Complex.ext_iff]
    intro j; fin_cases j
    · exact ⟨Pm_dens _ h1, Pm_dens _ h1⟩
    · exact ⟨Pm_dens _ h2, Pm_dens _ h4⟩
    · exact ⟨Pm_dens _ h3, Pm_dens _ h3⟩
    · exact ⟨Pm_dens _ h4, Pm_dens _ h2⟩
    · exact ⟨Pm_dens _ h1, Pm_dens _ h1⟩
    · exact ⟨Pm_dens _ h3, Pm_dens _ h3⟩
    · exact ⟨D0_dens, D0_dens⟩
    · exact ⟨D1_dens, D1_dens⟩
  · rw [mix_eq]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [Fin.sum_univ_succ, kronecker, D0, D1, Pm, vecMulVec] <;> ring_nf <;>
      simp [Complex.ext_iff] <;> norm_num
  · rw [mix_eq, xstate_trace]; norm_num

lemma rob_set (std : Bool) : IsLeast {s : ℝ | 0 ≤ s ∧ ∃ omega : Op QQ, QAlgorithms.IsDensityMatrix omega ∧
    (std = true → omega ∈ {X : Op QQ | sep X}) ∧ mix rhoEx omega s ∈ {X : Op QQ | sep X}} (1/4) :=
  ⟨⟨by norm_num, omega0, omega0_dens, fun _ => omega0_sep, mix_sep⟩, fun s hs => rob_lb std s hs⟩

lemma rs_rhoEx : rs rhoEx = 1/4 := (rob_set true).csInf_eq
lemma rg_rhoEx : rg rhoEx = 1/4 := (rob_set false).csInf_eq

def mk4 (a b c d : ℂ) : Vec QQ := WithLp.toLp 2 (fun p => ![![a,b],![c,d]] p.1 p.2)

@[simp] lemma mk4_00 (a b c d : ℂ) : mk4 a b c d (0,0) = a := rfl
@[simp] lemma mk4_01 (a b c d : ℂ) : mk4 a b c d (0,1) = b := rfl
@[simp] lemma mk4_10 (a b c d : ℂ) : mk4 a b c d (1,0) = c := rfl
@[simp] lemma mk4_11 (a b c d : ℂ) : mk4 a b c d (1,1) = d := rfl

lemma mk4_norm_sq (a b c d : ℂ) : ‖mk4 a b c d‖^2 = ‖a‖^2 + ‖b‖^2 + ‖c‖^2 + ‖d‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

lemma mk4_inner (a b c d a' b' c' d' : ℂ) : inner ℂ (mk4 a b c d) (mk4 a' b' c' d') =
    conj a * a' + conj b * b' + conj c * c' + conj d * d' := by
  simp [PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

lemma spinFlip_mk4 (a b c d : ℂ) : spinFlip (mk4 a b c d) = mk4 (-conj d) (conj c) (conj b) (-conj a) := by
  ext ⟨i1, i2⟩
  fin_cases i1 <;> fin_cases i2 <;> simp [spinFlip]

lemma proj_mk4 (a b c d : ℂ) (i j : QQ) : proj (mk4 a b c d) i j = mk4 a b c d i * conj (mk4 a b c d j) := rfl

lemma conc_lb (k : ℕ) (w : Fin k → ℝ) (v : Fin k → Vec QQ) (hw : ∀ i, 0 ≤ w i ∧ ‖v i‖ = 1)
    (hr : rhoEx = ∑ i, (w i : ℂ) • proj (v i)) : 3/10 ≤ ∑ i, w i * pureConcurrence (v i) := by
  have ent : ∀ p q : QQ, rhoEx p q = ∑ i, (w i : ℂ) * (v i p * conj (v i q)) := by
    intro p q
    conv_lhs => rw [hr]
    simp [Matrix.sum_apply, QAlgorithms.pureDensity]
  have e1 := ent (0,0) (1,1)
  have e2 := ent (0,1) (0,1)
  have e3 := ent (1,0) (1,0)
  simp only [rhoEx_eq, xs_03, xs_11, xs_22] at e1 e2 e3
  have hA : 1/4 ≤ ∑ i, w i * (‖v i (0,0)‖ * ‖v i (1,1)‖) := by
    have h := norm_sum_le Finset.univ (fun i => (w i : ℂ) * (v i (0,0) * conj (v i (1,1))))
    rw [← e1] at h
    have h' : ‖(((1/4:ℝ)):ℂ)‖ = 1/4 := by rw [Complex.norm_real]; norm_num
    rw [h'] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_)))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg (hw i).1]
  have nsq : ∀ z : ℂ, z * conj z = ((‖z‖^2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hB : ∑ i, w i * ‖v i (0,1)‖^2 = 1/5 := by
    have := congrArg Complex.re e2
    simp only [nsq, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re] at this
    linarith
  have hC : ∑ i, w i * ‖v i (1,0)‖^2 = 1/20 := by
    have := congrArg Complex.re e3
    simp only [nsq, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re] at this
    linarith
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i) * ‖v i (0,1)‖) (fun i => Real.sqrt (w i) * ‖v i (1,0)‖)
  have hsq : ∀ i, Real.sqrt (w i) * Real.sqrt (w i) = w i := fun i => Real.mul_self_sqrt (hw i).1
  have r1 : ∑ i, (Real.sqrt (w i) * ‖v i (0,1)‖) * (Real.sqrt (w i) * ‖v i (1,0)‖) =
      ∑ i, w i * (‖v i (0,1)‖ * ‖v i (1,0)‖) :=
    Finset.sum_congr rfl (fun i _ => by linear_combination (‖v i (0,1)‖ * ‖v i (1,0)‖) * hsq i)
  have r2 : ∑ i, (Real.sqrt (w i) * ‖v i (0,1)‖)^2 = ∑ i, w i * ‖v i (0,1)‖^2 :=
    Finset.sum_congr rfl (fun i _ => by linear_combination (‖v i (0,1)‖^2) * hsq i)
  have r3 : ∑ i, (Real.sqrt (w i) * ‖v i (1,0)‖)^2 = ∑ i, w i * ‖v i (1,0)‖^2 :=
    Finset.sum_congr rfl (fun i _ => by linear_combination (‖v i (1,0)‖^2) * hsq i)
  rw [r1, r2, r3, hB, hC] at hCS
  have hS0 : 0 ≤ ∑ i, w i * (‖v i (0,1)‖ * ‖v i (1,0)‖) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).1 (by positivity))
  have hS : ∑ i, w i * (‖v i (0,1)‖ * ‖v i (1,0)‖) ≤ 1/10 := by nlinarith
  have hpt : ∀ i, w i * (2 * (‖v i (0,0)‖ * ‖v i (1,1)‖) - 2 * (‖v i (0,1)‖ * ‖v i (1,0)‖)) ≤
      w i * pureConcurrence (v i) := by
    intro i
    apply mul_le_mul_of_nonneg_left _ (hw i).1
    unfold pureConcurrence
    have := norm_sub_norm_le (v i (0,0) * v i (1,1)) (v i (0,1) * v i (1,0))
    rw [norm_mul, norm_mul] at this
    linarith
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  have e : ∑ i, w i * (2 * (‖v i (0,0)‖ * ‖v i (1,1)‖) - 2 * (‖v i (0,1)‖ * ‖v i (1,0)‖)) =
      2 * ∑ i, w i * (‖v i (0,0)‖ * ‖v i (1,1)‖) - 2 * ∑ i, w i * (‖v i (0,1)‖ * ‖v i (1,0)‖) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  linarith

lemma conc_mem (p r : ℝ) (hp : p^2 = 1/3) (hr : r^2 = 1/15) (hp0 : 0 < p) (hr0 : 0 < r) :
    (3/10 : ℝ) ∈ {c : ℝ | ∃ k : ℕ, ∃ w : Fin k → ℝ, ∃ v : Fin k → Vec QQ,
    (∀ i, 0 ≤ w i ∧ ‖v i‖=1) ∧ (∑ i,w i)=1 ∧
    rhoEx = ∑ i, (w i:ℂ) • proj (v i) ∧ c = ∑ i,w i * pureConcurrence (v i)} := by
  have nrm : ∀ x y : ℂ, ‖x‖ = 2*r → ‖y‖ = r → ‖mk4 p x y p‖ = 1 := by
    intro x y hx hy
    have h := mk4_norm_sq p x y p
    rw [hx, hy, Complex.norm_real, Real.norm_of_nonneg hp0.le] at h
    have : ‖mk4 (p:ℂ) x y p‖^2 = 1 := by rw [h]; nlinarith
    have h0 : 0 ≤ ‖mk4 (p:ℂ) x y p‖ := norm_nonneg _
    nlinarith
  have hI : ‖Complex.I‖ = 1 := by simp
  refine ⟨6, ![33/160, 27/160, 33/160, 27/160, 1/8, 1/8],
    ![mk4 p (2*r) r p, mk4 p (Complex.I*(2*r)) (-Complex.I*r) p, mk4 p (-(2*r)) (-r) p,
      mk4 p (-Complex.I*(2*r)) (Complex.I*r) p, mk4 1 0 0 0, mk4 0 0 0 1], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · refine ⟨by norm_num, nrm _ _ ?_ ?_⟩
      · rw [show (2*(r:ℂ)) = ((2*r:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      · rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]
    · refine ⟨by norm_num, nrm _ _ ?_ ?_⟩
      · rw [norm_mul, hI, show (2*(r:ℂ)) = ((2*r:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; ring
      · rw [norm_mul, norm_neg, hI, Complex.norm_real, Real.norm_of_nonneg hr0.le]; ring
    · refine ⟨by norm_num, nrm _ _ ?_ ?_⟩
      · rw [norm_neg, show (2*(r:ℂ)) = ((2*r:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      · rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    · refine ⟨by norm_num, nrm _ _ ?_ ?_⟩
      · rw [norm_mul, norm_neg, hI, show (2*(r:ℂ)) = ((2*r:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; ring
      · rw [norm_mul, hI, Complex.norm_real, Real.norm_of_nonneg hr0.le]; ring
    · refine ⟨by norm_num, ?_⟩
      show ‖mk4 (1:ℂ) 0 0 0‖ = 1
      have h := mk4_norm_sq 1 0 0 0
      have h0 : 0 ≤ ‖mk4 (1:ℂ) 0 0 0‖ := norm_nonneg _
      simp at h
      rcases h with h | h
      · exact h
      · linarith
    · refine ⟨by norm_num, ?_⟩
      show ‖mk4 (0:ℂ) 0 0 1‖ = 1
      have h := mk4_norm_sq 0 0 0 1
      have h0 : 0 ≤ ‖mk4 (0:ℂ) 0 0 1‖ := norm_nonneg _
      simp at h
      rcases h with h | h
      · exact h
      · linarith
  · simp [Fin.sum_univ_succ]; norm_num
  · rw [rhoEx_eq]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [Fin.sum_univ_succ, proj_mk4, Complex.ext_iff] <;> ring_nf <;> simp [hp, hr] <;> norm_num
  · have c1 : pureConcurrence (mk4 p (2*r) r p) = 2/5 := by
      unfold pureConcurrence
      simp only [mk4_00, mk4_01, mk4_10, mk4_11]
      rw [show (p:ℂ)*p - 2*r*r = ((1/5:ℝ):ℂ) by
        rw [show (p:ℂ)*p - 2*r*r = ((p^2 - 2*r^2 : ℝ) : ℂ) by push_cast; ring, hp, hr]; norm_num]
      rw [Complex.norm_real]; norm_num
    have c2 : pureConcurrence (mk4 p (Complex.I*(2*r)) (-Complex.I*r) p) = 2/5 := by
      unfold pureConcurrence
      simp only [mk4_00, mk4_01, mk4_10, mk4_11]
      rw [show (p:ℂ)*p - Complex.I*(2*r)*(-Complex.I*r) = ((1/5:ℝ):ℂ) by
        rw [show (p:ℂ)*p - Complex.I*(2*r)*(-Complex.I*r) = ((p^2 - 2*r^2 : ℝ) : ℂ) by
          push_cast; ring_nf; rw [Complex.I_sq]; ring, hp, hr]; norm_num]
      rw [Complex.norm_real]; norm_num
    have c3 : pureConcurrence (mk4 p (-(2*r)) (-r) p) = 2/5 := by
      unfold pureConcurrence
      simp only [mk4_00, mk4_01, mk4_10, mk4_11]
      rw [show (p:ℂ)*p - (-(2*r))*(-r) = ((1/5:ℝ):ℂ) by
        rw [show (p:ℂ)*p - (-(2*r))*(-r) = ((p^2 - 2*r^2 : ℝ) : ℂ) by push_cast; ring, hp, hr]; norm_num]
      rw [Complex.norm_real]; norm_num
    have c4 : pureConcurrence (mk4 p (-Complex.I*(2*r)) (Complex.I*r) p) = 2/5 := by
      unfold pureConcurrence
      simp only [mk4_00, mk4_01, mk4_10, mk4_11]
      rw [show (p:ℂ)*p - (-Complex.I*(2*r))*(Complex.I*r) = ((1/5:ℝ):ℂ) by
        rw [show (p:ℂ)*p - (-Complex.I*(2*r))*(Complex.I*r) = ((p^2 - 2*r^2 : ℝ) : ℂ) by
          push_cast; ring_nf; rw [Complex.I_sq]; ring, hp, hr]; norm_num]
      rw [Complex.norm_real]; norm_num
    have c5 : pureConcurrence (mk4 1 0 0 0) = 0 := by simp [pureConcurrence]
    have c6 : pureConcurrence (mk4 0 0 0 1) = 0 := by simp [pureConcurrence]
    simp only [neg_mul] at c2 c4
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    simp [c1, c2, c3, c4, c5, c6]
    norm_num

lemma concurrence_rhoEx : concurrence rhoEx = 3/10 := by
  have hp0 : 0 < Real.sqrt 3 / 3 := by positivity
  have hr0 : 0 < Real.sqrt 15 / 15 := by positivity
  have hp : (Real.sqrt 3 / 3)^2 = 1/3 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hr : (Real.sqrt 15 / 15)^2 = 1/15 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine IsLeast.csInf_eq ⟨conc_mem _ _ hp hr hp0 hr0, ?_⟩
  rintro c ⟨k, w, v, hw, -, hr', rfl⟩
  exact conc_lb k w v hw hr'

lemma frame_ok (x0 x3 : ℝ) (h5 : x0^2 = 5/16) (h11 : x3^2 = 11/400) (h5' : 0 < x0) (h11' : 0 < x3) :
    let lam : Fin 4 → ℝ := ![5/8,1/8,11/100,9/100]
    let K : Fin 4 → ℝ := ![1,1,5/4,5/4]
    ∃ v : Fin 4 → Vec QQ, woottersFrame rhoEx lam v ∧ ∀ i,frameNorm lam v i=K i := by
  intro lam K
  obtain ⟨x1, hx1⟩ : ∃ x : ℝ, x = 1/4 := ⟨_, rfl⟩
  obtain ⟨y2, hy2⟩ : ∃ x : ℝ, x = 3/10 := ⟨_, rfl⟩
  obtain ⟨y3, hy3⟩ : ∃ x : ℝ, x = 3/20 := ⟨_, rfl⟩
  refine ⟨![mk4 (Complex.I*x0) 0 0 (Complex.I*x0), mk4 x1 0 0 (-x1),
    mk4 0 (2*x3) x3 0, mk4 0 (Complex.I*y2) (-Complex.I*y3) 0], ⟨?_, ?_⟩, ?_⟩
  · rw [rhoEx_eq]
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
      simp [Fin.sum_univ_succ, proj_mk4, Complex.ext_iff] <;> subst hx1 hy2 hy3 <;>
      (try refine ⟨?_, ?_⟩) <;> ring_nf <;> nlinarith [h5, h11]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [lam, spinFlip_mk4, mk4_inner, Complex.ext_iff, -inner_self_eq_norm_sq_to_K] <;> subst hx1 hy2 hy3 <;>
      (try refine ⟨?_, ?_⟩) <;> ring_nf <;> nlinarith [h5, h11]
  · intro i
    fin_cases i <;> simp only [frameNorm, lam, K] <;> simp [mk4_norm_sq, abs_of_pos h5', abs_of_pos h11'] <;>
      subst hx1 hy2 hy3 <;> ring_nf <;> nlinarith [h5, h11]

lemma noiseEx_eq : noiseEx = xstate 0 (1/20) (1/5) 0 0 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [noiseEx, compressed, QAlgorithms.ket, QAlgorithms.pureDensity, EuclideanSpace.single_apply]

lemma beta_proj : proj (((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket ((0:Fin 2),(1:Fin 2))-QAlgorithms.ket ((1:Fin 2),(0:Fin 2))) : Vec QQ)
    = xstate 0 (1/2) (1/2) 0 0 (-1/2) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [QAlgorithms.ket, QAlgorithms.pureDensity, EuclideanSpace.single_apply, h2] <;> norm_num

lemma proj_psd (v : Vec QQ) : (proj v).PosSemidef := by
  have : proj v = vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)) := by
    ext i j; simp [QAlgorithms.pureDensity, vecMulVec]
  rw [this]; exact posSemidef_vecMulVec_self_star _

lemma one_sub_x : (1 : Op QQ) - xstate 0 1 1 0 (-1) 0 = xstate 1 0 0 1 1 0 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;> simp [Matrix.one_apply]

end X7A18

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 X7A18 in
theorem solution  :
  let lam : Fin 4 → ℝ := ![5/8,1/8,11/100,9/100]
  let K : Fin 4 → ℝ := ![1,1,5/4,5/4]
  let beta : Vec QQ := ((Real.sqrt 2)⁻¹:ℂ) • (QAlgorithms.ket (0,1)-QAlgorithms.ket (1,0))
  QAlgorithms.IsDensityMatrix rhoEx ∧ rhoEx.PosDef ∧
  rhoEx.charpoly =
    (Polynomial.X - Polynomial.C (5/8 : ℂ)) *
    (Polynomial.X - Polynomial.C (1/8 : ℂ)) *
    (Polynomial.X - Polynomial.C ((1/8 + Real.sqrt 229/200 : ℝ) : ℂ)) *
    (Polynomial.X - Polynomial.C ((1/8 - Real.sqrt 229/200 : ℝ) : ℂ)) ∧
  (∀ i,0<lam i) ∧ Function.Injective lam ∧ Antitone lam ∧
  (∃ v : Fin 4 → Vec QQ, woottersFrame rhoEx lam v ∧ ∀ i,frameNorm lam v i=K i) ∧
  concurrence rhoEx=3/10 ∧ oldCandidate lam K=27/80 ∧
  optS rhoEx noiseEx ∧ optG rhoEx noiseEx ∧
  dualG (2 • proj beta) ∧ (-((2 • proj beta) * pt rhoEx).trace.re)=1/4 ∧
  noiseEx.trace.re=1/4 ∧ rs rhoEx=1/4 ∧ rg rhoEx=1/4 ∧ 1/4<(27/80:ℝ) := by
  intro lam K beta
  have hb : proj beta = xstate 0 (1/2) (1/2) 0 0 (-1/2) := beta_proj
  have h2b : 2 • proj beta = xstate 0 1 1 0 0 (-1) := by
    rw [two_smul, hb, xstate_add]; congr 1 <;> norm_num
  have hnoise : noiseEx.PosSemidef := by
    rw [noiseEx_eq]
    exact xstate_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hptn : (pt noiseEx).PosSemidef := by
    rw [noiseEx_eq, pt_xstate]
    exact xstate_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsum : (pt rhoEx + pt noiseEx).PosSemidef := by
    rw [noiseEx_eq, rhoEx_eq, pt_xstate, pt_xstate, xstate_add]
    exact xstate_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htr : noiseEx.trace.re = 1/4 := by
    rw [noiseEx_eq, xstate_trace, Complex.ofReal_re]; norm_num
  refine ⟨rhoEx_density, rhoEx_posDef, rhoEx_charpoly, ?_, ?_, ?_,
    frame_ok (Real.sqrt 5 / 4) (Real.sqrt 11 / 20)
      (by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num)
      (by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num) (by positivity) (by positivity), concurrence_rhoEx, ?_,
    ⟨⟨⟨hnoise, hsum⟩, hptn⟩, by rw [htr, rs_rhoEx]⟩, ⟨⟨hnoise, hsum⟩, by rw [htr, rg_rhoEx]⟩,
    ⟨?_, ?_⟩, ?_, htr, rs_rhoEx, rg_rhoEx, by norm_num⟩
  · intro i; fin_cases i <;> simp [lam] <;> norm_num
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp [lam] at h ⊢ <;> norm_num at h
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [lam] at hij ⊢ <;> norm_num <;> revert hij <;> decide
  · simp [oldCandidate, lam, K]; norm_num
  · rw [two_smul]; exact (proj_psd _).add (proj_psd _)
  · rw [h2b, pt_xstate, one_sub_x]
    exact xstate_psd (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h2b, rhoEx_eq, pt_xstate, xstate_trace_mul, Complex.ofReal_re]; norm_num
