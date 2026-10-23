-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P07.idealCapacity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:58:13.446325+00:00
-- url     : https://prove2.me/submissions/877e7ce6-bd64-4a41-84c4-3f27a84c209d

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07
noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Gap20.P07
open QAlgorithms
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)
open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)
open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)
open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion IsDensity)

theorem g79e_coef_hasSum {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) (i j : I) :
    HasSum (fun n => e.left n i * star (e.right n j)) (X i j) := by
  have hb : ∀ n, ‖e.left n i * star (e.right n j)‖ ≤ ‖e.left n‖ * ‖e.right n‖ := by
    intro n
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
      (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
  have hs : Summable (fun n => e.left n i * star (e.right n j)) :=
    Summable.of_norm_bounded e.summable hb
  rw [e.coefficients i j]
  exact hs.hasSum

def g79e_expAdd {I : Type} {X Y : Matrix I I ℂ} (eX : NuclearExpansion X)
    (eY : NuclearExpansion Y) : NuclearExpansion (X + Y) where
  left n := if n % 2 = 0 then eX.left (n / 2) else eY.left (n / 2)
  right n := if n % 2 = 0 then eX.right (n / 2) else eY.right (n / 2)
  summable := by
    apply Summable.even_add_odd
    · refine eX.summable.congr (fun k => ?_)
      have h1 : (2 * k) % 2 = 0 := by omega
      have h2 : 2 * k / 2 = k := by omega
      simp [h1, h2]
    · refine eY.summable.congr (fun k => ?_)
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1) / 2 = k := by omega
      simp [h1, h2]
  coefficients i j := by
    rw [Matrix.add_apply]
    symm
    apply HasSum.tsum_eq
    apply HasSum.even_add_odd
    · refine (g79e_coef_hasSum eX i j).congr_fun (fun k => ?_)
      have h1 : (2 * k) % 2 = 0 := by omega
      have h2 : 2 * k / 2 = k := by omega
      simp [h1, h2]
    · refine (g79e_coef_hasSum eY i j).congr_fun (fun k => ?_)
      have h1 : (2 * k + 1) % 2 = 1 := by omega
      have h2 : (2 * k + 1) / 2 = k := by omega
      simp [h1, h2]

theorem g79e_expAdd_sum {I : Type} {X Y : Matrix I I ℂ} (eX : NuclearExpansion X)
    (eY : NuclearExpansion Y) :
    ∑' n, ‖(g79e_expAdd eX eY).left n‖ * ‖(g79e_expAdd eX eY).right n‖ =
      ∑' n, ‖eX.left n‖ * ‖eX.right n‖ + ∑' n, ‖eY.left n‖ * ‖eY.right n‖ := by
  apply HasSum.tsum_eq
  apply HasSum.even_add_odd
  · refine eX.summable.hasSum.congr_fun (fun k => ?_)
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    simp [g79e_expAdd, h1, h2]
  · refine eY.summable.hasSum.congr_fun (fun k => ?_)
    have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    simp [g79e_expAdd, h1, h2]

def g79e_expSmul {I : Type} {X : Matrix I I ℂ} (c : ℂ) (e : NuclearExpansion X) :
    NuclearExpansion (c • X) where
  left n := c • e.left n
  right n := e.right n
  summable := by
    simp only [norm_smul, mul_assoc]
    exact e.summable.mul_left _
  coefficients i j := by
    rw [Matrix.smul_apply, e.coefficients i j, smul_eq_mul, ← tsum_mul_left]
    congr 1; funext n
    simp [mul_assoc]

theorem g79e_expSmul_sum {I : Type} {X : Matrix I I ℂ} (c : ℂ) (e : NuclearExpansion X) :
    ∑' n, ‖(g79e_expSmul c e).left n‖ * ‖(g79e_expSmul c e).right n‖ =
      ‖c‖ * ∑' n, ‖e.left n‖ * ‖e.right n‖ := by
  simp only [g79e_expSmul, norm_smul, mul_assoc]
  exact tsum_mul_left

def g79e_expCast {I : Type} {X Y : Matrix I I ℂ} (h : X = Y) (e : NuclearExpansion X) :
    NuclearExpansion Y where
  left := e.left
  right := e.right
  summable := e.summable
  coefficients i j := by rw [← h]; exact e.coefficients i j

theorem g79e_ts_le {I : Type} {X : Matrix I I ℂ} (e : NuclearExpansion X) :
    traceSize X ≤ ENNReal.ofReal (∑' n, ‖e.left n‖ * ‖e.right n‖) := iInf_le _ e

theorem g79e_ts_add {I : Type} (X Y : Matrix I I ℂ) :
    traceSize (X + Y) ≤ traceSize X + traceSize Y := by
  unfold traceSize
  rw [ENNReal.iInf_add]
  refine le_iInf fun eX => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun eY => ?_
  refine (iInf_le _ (g79e_expAdd eX eY)).trans (le_of_eq ?_)
  rw [g79e_expAdd_sum, ENNReal.ofReal_add (tsum_nonneg fun _ => by positivity)
    (tsum_nonneg fun _ => by positivity)]

theorem g79e_coef_le {I : Type} (X : Matrix I I ℂ) (i j : I) :
    ENNReal.ofReal ‖X i j‖ ≤ traceSize X := by
  unfold traceSize
  refine le_iInf fun e => ENNReal.ofReal_le_ofReal ?_
  rw [e.coefficients i j]
  have hb : ∀ n, ‖e.left n i * star (e.right n j)‖ ≤ ‖e.left n‖ * ‖e.right n‖ := by
    intro n
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
      (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
  have hs : Summable (fun n => ‖e.left n i * star (e.right n j)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb e.summable
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb e.summable)

theorem g79e_traceSize_zero {I : Type} : traceSize (0 : Matrix I I ℂ) = 0 := by
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le (⟨fun _ => 0, fun _ => 0, by simp, by intro i j; simp⟩ :
    NuclearExpansion (0 : Matrix I I ℂ)) ?_
  simp

def g79e_e {I : Type} (i : I) : Hilbert I := lp.single 2 i (1 : ℂ)

theorem g79e_e_apply {I : Type} (i a : I) : g79e_e i a = if a = i then 1 else 0 := by
  simp [g79e_e, lp.single_apply, Pi.single_apply]

theorem g79e_e_norm {I : Type} (i : I) : ‖g79e_e i‖ = 1 := by
  simp [g79e_e, lp.norm_single (p := 2) (by norm_num)]

def g79e_exp2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) : NuclearExpansion X where
  left n := if n = 0 then u else if n = 1 then u' else 0
  right n := if n = 0 then v else if n = 1 then v' else 0
  summable := by
    apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [h0, h1]
  coefficients i j := by
    rw [hX, tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      simp [h0, h1]

theorem g79e_ts2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) :
    traceSize X ≤ ENNReal.ofReal (‖u‖ * ‖v‖ + ‖u'‖ * ‖v'‖) := by
  refine (iInf_le _ (g79e_exp2 X u v u' v' hX)).trans (le_of_eq ?_)
  congr 1
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [g79e_exp2, Finset.sum_range_succ]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [g79e_exp2, h0, h1]


theorem g79e_tc_single {I : Type} (i j : I) (c : ℂ) : IsTraceClass (Matrix.single i j c) :=
  ⟨g79e_exp2 _ (c • g79e_e i) (g79e_e j) 0 0 (fun a b => by
    by_cases ha : i = a <;> by_cases hb : j = b <;>
      simp [Matrix.single_apply, g79e_e_apply, ha, hb, eq_comm])⟩

theorem g79e_tc_add {I : Type} {X Y : Matrix I I ℂ} (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    IsTraceClass (X + Y) := ⟨g79e_expAdd hX.some hY.some⟩

theorem g79e_tc {A : Type} [Fintype A] (X : Matrix A A ℂ) : IsTraceClass X := by
  rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_induction _ IsTraceClass (fun _ _ => g79e_tc_add) ?_ ?_
  · exact ⟨⟨fun _ => 0, fun _ => 0, by simp, by intro i j; simp⟩⟩
  · intro i _
    refine Finset.sum_induction _ IsTraceClass (fun _ _ => g79e_tc_add) ?_ ?_
    · exact ⟨⟨fun _ => 0, fun _ => 0, by simp, by intro i j; simp⟩⟩
    · intro j _; exact g79e_tc_single _ _ _

theorem g79e_quad {A : Type} [Fintype A] {ρ : Matrix A A ℂ} (h : IsDensity ρ) (w : A → ℂ) :
    (star w ⬝ᵥ (ρ *ᵥ w)).im = 0 ∧ 0 ≤ (star w ⬝ᵥ (ρ *ᵥ w)).re := by
  have := h.2.1 Finset.univ w
  have e : star w ⬝ᵥ (ρ *ᵥ w) = ∑ i, ∑ j, star (w i) * ρ i j * w j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  rw [e]; exact this

theorem g79e_trace {A : Type} [Fintype A] {ρ : Matrix A A ℂ} (h : IsDensity ρ) :
    ∑ i, (ρ i i).re = 1 := by
  rw [← h.2.2.2, tsum_fintype]

theorem g79e_psd {A : Type} [Fintype A] {ρ : Matrix A A ℂ} (h : IsDensity ρ) : ρ.PosSemidef := by
  have hH : ρ.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymmetric, LinearMap.isSymmetric_iff_inner_map_self_real]
    intro v
    have hq := (g79e_quad h (WithLp.ofLp v)).1
    rw [Matrix.toEuclideanLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    have e : WithLp.ofLp v ⬝ᵥ star (WithLp.ofLp (WithLp.toLp 2 (ρ *ᵥ WithLp.ofLp v) : EuclideanSpace ℂ A))
        = star (star (WithLp.ofLp v) ⬝ᵥ ρ *ᵥ WithLp.ofLp v) := by
      simp only [WithLp.ofLp_toLp, dotProduct, star_sum, Pi.star_apply, star_mul, star_star]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [e]
    apply Complex.ext <;> simp [hq]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => ?_)
  have hq := g79e_quad h x
  exact Complex.nonneg_iff.mpr ⟨hq.2, hq.1.symm⟩

def g79e_kmap {A B R : Type} [Fintype A] [Fintype R] (K : R → Matrix B A ℂ) :
    Matrix A A ℂ → Matrix B B ℂ := fun X => ∑ r, K r * X * (K r)ᴴ

def g79e_M {A B : Type} (k : ℕ) (K : Matrix B A ℂ) : Matrix (B × Fin k) (A × Fin k) ℂ :=
  fun p q => if p.2 = q.2 then K p.1 q.1 else 0

theorem g79e_kNK {A B : Type} [Fintype A] (K : Matrix B A ℂ) (N : Matrix A A ℂ) (b b' : B) :
    (K * N * Kᴴ) b b' = ∑ j, ∑ i, K b i * N i j * star (K b' j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]

theorem g79e_tensor_kmap {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (K : R → Matrix B A ℂ) (k : ℕ) (X : Matrix (A × Fin k) (A × Fin k) ℂ) :
    tensorApply (g79e_kmap K) X = ∑ r, g79e_M k (K r) * X * (g79e_M k (K r))ᴴ := by
  ext p q
  simp only [tensorApply, g79e_kmap, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  refine Eq.trans (g79e_kNK (K r) (fun i j => X (i, p.2) (j, q.2) : Matrix A A ℂ) p.1 q.1) ?_
  refine Eq.trans ?_ (g79e_kNK _ _ p q).symm
  simp only [g79e_M, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single q.2]
  · rw [Finset.sum_comm]
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem g79e_MM {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (K : R → Matrix B A ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1) (k : ℕ) :
    ∑ r, (g79e_M k (K r))ᴴ * g79e_M k (K r) = 1 := by
  ext x y
  have := congrFun (congrFun hK x.1) y.1
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, g79e_M,
    Fintype.sum_prod_type] at this ⊢
  by_cases hxy : x = y
  · subst hxy
    rw [Matrix.one_apply_eq] at this ⊢
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Finset.sum_eq_single x.2]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  · rw [Matrix.one_apply_ne hxy]
    by_cases h2 : x.2 = y.2
    · have h1 : x.1 ≠ y.1 := fun h => hxy (Prod.ext h h2)
      rw [Matrix.one_apply_ne h1] at this
      refine Eq.trans ?_ this
      refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Finset.sum_eq_single x.2]
      · simp [h2]
      · intro c _ hc; simp [hc]
      · simp
    · refine Finset.sum_eq_zero (fun r _ => Finset.sum_eq_zero (fun b _ =>
        Finset.sum_eq_zero (fun c _ => ?_)))
      by_cases hc : c = x.2
      · subst hc; simp [h2]
      · simp [hc]

theorem g79e_kraus {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (K : R → Matrix B A ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1) :
    IsTraceClassChannel (g79e_kmap K) := by
  refine ⟨fun X _ => g79e_tc _, fun X Y _ _ => ?_, fun c X _ => ?_, fun k ρ => ?_⟩
  · simp [g79e_kmap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · simp [g79e_kmap, Finset.smul_sum]
  · have hρ := ρ.density
    rw [g79e_tensor_kmap]
    set Y := ∑ r, g79e_M k (K r) * ρ.coefficients * (g79e_M k (K r))ᴴ with hY
    refine ⟨g79e_tc _, fun s z => ?_, Summable.of_finite, ?_⟩
    · set v : B × Fin k → ℂ := fun p => if p ∈ s then z p else 0
      have e1 : (∑ i ∈ s, ∑ j ∈ s, star (z i) * Y i j * z j) = star v ⬝ᵥ (Y *ᵥ v) := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, v]
        rw [← Finset.sum_subset (Finset.subset_univ s)]
        · refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [if_pos hi, Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ s)]
          · refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [if_pos hj]; ring
          · intro j _ hj; simp [hj]
        · intro i _ hi; simp [hi]
      have e2 : star v ⬝ᵥ (Y *ᵥ v) = ∑ r, star ((g79e_M k (K r))ᴴ *ᵥ v) ⬝ᵥ
          (ρ.coefficients *ᵥ ((g79e_M k (K r))ᴴ *ᵥ v)) := by
        rw [hY, Matrix.sum_mulVec, dotProduct_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      rw [e1, e2, Complex.im_sum, Complex.re_sum]
      exact ⟨Finset.sum_eq_zero (fun r _ => (g79e_quad hρ _).1),
        Finset.sum_nonneg (fun r _ => (g79e_quad hρ _).2)⟩
    · rw [tsum_fintype, ← g79e_trace hρ, ← Complex.re_sum, ← Complex.re_sum]
      congr 1
      have : ∑ i, Y i i = Y.trace := rfl
      rw [this, hY, Matrix.trace_sum]
      simp_rw [Matrix.trace_mul_cycle (g79e_M k _)]
      rw [← Matrix.trace_sum, ← Finset.sum_mul, g79e_MM K hK, Matrix.one_mul]
      rfl
open scoped MatrixOrder in
theorem g79e_le_trace {n : Type*} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ}
    (hS : S.PosSemidef) : (((S.trace.re : ℝ) : ℂ) • (1 : Matrix n n ℂ) - S).PosSemidef := by
  have hsa : IsSelfAdjoint S := hS.1.isSelfAdjoint
  have key : S ≤ algebraMap ℝ (Matrix n n ℂ) S.trace.re := by
    rw [le_algebraMap_iff_spectrum_le]
    intro x hx
    rw [hS.1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hS.1.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hS.eigenvalues_nonneg j) (Finset.mem_univ i)
  rw [← sub_nonneg, Matrix.nonneg_iff_posSemidef, Algebra.algebraMap_eq_smul_one] at key
  rw [show ((S.trace.re:ℂ) • (1:Matrix n n ℂ)) = S.trace.re • (1 : Matrix n n ℂ) from by
    ext i j; simp [Complex.real_smul]]
  exact key

def g79e_L {B : Type} (M : Matrix B B ℂ) : Matrix (B × Fin 1) (B × Fin 1) ℂ := fun p q => M p.1 q.1

def g79e_U (B : Type) : Matrix (B × Fin 1) B ℂ := fun p b => if p.1 = b then 1 else 0

theorem g79e_L_eq {B : Type} [Fintype B] (M : Matrix B B ℂ) :
    g79e_L M = (g79e_U B) * M * (g79e_U B)ᴴ := by
  ext p q
  rw [g79e_kNK]
  simp [g79e_U, g79e_L]

theorem g79e_L_back {B : Type} [Fintype B] (M : Matrix B B ℂ) :
    (g79e_U B)ᴴ * g79e_L M * g79e_U B = M := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g79e_U, g79e_L, Fintype.sum_prod_type,
    Fin.sum_univ_one]
  simp

theorem g79e_L_psd {B : Type} [Fintype B] {M : Matrix B B ℂ} (h : M.PosSemidef) :
    (g79e_L M).PosSemidef := by
  rw [g79e_L_eq]
  have := h.conjTranspose_mul_mul_same (g79e_U B)ᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at this

theorem g79e_L_trace {B : Type} [Fintype B] (M : Matrix B B ℂ) :
    (g79e_L M).trace = M.trace := by
  simp [Matrix.trace, g79e_L, Fintype.sum_prod_type]

theorem g79e_fin_dot {P : Type} [Fintype P] (M : Matrix P P ℂ) (s : Finset P) (z : P → ℂ) :
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * M i j * z j) =
      star (fun p => if p ∈ s then z p else 0) ⬝ᵥ (M *ᵥ (fun p => if p ∈ s then z p else 0)) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [← Finset.sum_subset (Finset.subset_univ s)]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [if_pos hi, Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ s)]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [if_pos hj]; ring
    · intro j _ hj; simp [hj]
  · intro i _ hi; simp [hi]

theorem g79e_density_of_psd {P : Type} [Fintype P] {M : Matrix P P ℂ} (h : M.PosSemidef)
    (ht : M.trace.re = 1) : IsDensity M := by
  refine ⟨g79e_tc _, fun s z => ?_, Summable.of_finite, ?_⟩
  · rw [g79e_fin_dot]
    have := Complex.nonneg_iff.mp (h.dotProduct_mulVec_nonneg (fun p => if p ∈ s then z p else 0))
    exact ⟨this.2.symm, this.1⟩
  · rw [tsum_fintype, ← ht, Matrix.trace, Complex.re_sum]; rfl

theorem g79e_chan_dens {A B : Type} [Fintype A] [Fintype B] {Φ : Operation B A}
    (hΦ : IsTraceClassChannel Φ) {M : Matrix B B ℂ} (h : M.PosSemidef) (ht : M.trace.re = 1) :
    (Φ M).PosSemidef ∧ (Φ M).trace.re = 1 := by
  have hd : IsDensity (g79e_L M) := g79e_density_of_psd (g79e_L_psd h) (by rw [g79e_L_trace, ht])
  have h2 : IsDensity (g79e_L (Φ M)) := hΦ.2.2.2 1 ⟨g79e_L M, hd⟩
  have hp := g79e_psd h2
  refine ⟨?_, ?_⟩
  · rw [← g79e_L_back (Φ M)]
    exact hp.conjTranspose_mul_mul_same _
  · rw [← g79e_L_trace, Matrix.trace, Complex.re_sum]
    simpa [Matrix.diag] using g79e_trace h2

theorem g79e_chan_add {A B : Type} [Fintype B] {Φ : Operation B A}
    (hΦ : IsTraceClassChannel Φ) (X Y : Matrix B B ℂ) : Φ (X + Y) = Φ X + Φ Y :=
  hΦ.2.1 X Y (g79e_tc _) (g79e_tc _)

theorem g79e_chan_smul {A B : Type} [Fintype B] {Φ : Operation B A}
    (hΦ : IsTraceClassChannel Φ) (c : ℂ) (X : Matrix B B ℂ) : Φ (c • X) = c • Φ X :=
  hΦ.2.2.1 c X (g79e_tc _)

theorem g79e_chan_pos {A B : Type} [Fintype A] [Fintype B] [Nonempty B] {Φ : Operation B A}
    (hΦ : IsTraceClassChannel Φ) {M : Matrix B B ℂ} (h : M.PosSemidef) (a : A) :
    0 ≤ (Φ M a a).re := by
  have hnB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have key : ∀ ε : ℝ, 0 < ε → 0 ≤ (Φ M a a).re + ε * (Φ 1 a a).re := by
    intro ε hε
    have htr : 0 ≤ M.trace.re := by
      have := h.trace_nonneg
      exact (Complex.nonneg_iff.mp this).1
    set t : ℝ := M.trace.re + ε * Fintype.card B with ht
    have htpos : 0 < t := by positivity
    set M' : Matrix B B ℂ := ((t⁻¹ : ℝ) : ℂ) • (M + (ε : ℂ) • 1) with hM'
    have hpsd : M'.PosSemidef := by
      refine Matrix.PosSemidef.smul ?_ ?_
      · refine h.add (Matrix.PosSemidef.smul Matrix.PosSemidef.one ?_)
        exact_mod_cast hε.le
      · exact_mod_cast (inv_pos.mpr htpos).le
    have htr' : M'.trace.re = 1 := by
      rw [hM', Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
      simp only [smul_eq_mul, Complex.re_ofReal_mul, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
      field_simp
      simp [ht]
    have hd := (g79e_chan_dens hΦ hpsd htr').1
    have hdiag : 0 ≤ (Φ M' a a).re := (Complex.nonneg_iff.mp (hd.diag_nonneg (i := a))).1
    rw [hM', g79e_chan_smul hΦ, g79e_chan_add hΦ, g79e_chan_smul hΦ] at hdiag
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.re_ofReal_mul,
      Complex.add_re] at hdiag
    have := (mul_nonneg_iff_of_pos_left (inv_pos.mpr htpos)).mp hdiag
    simpa using this
  by_contra hneg
  push_neg at hneg
  set x := (Φ M a a).re
  set y := (Φ 1 a a).re
  by_cases hy : y ≤ 0
  · have := key 1 one_pos; nlinarith
  · push_neg at hy
    have := key (-x / (2 * y)) (div_pos (by linarith) (by linarith))
    have e : -x / (2 * y) * y = -x / 2 := by field_simp
    nlinarith

def g79e_u {A : Type} (a : A) : Matrix Unit A ℂ := Matrix.of fun _ j => if j = a then (1 : ℂ) else 0

def g79e_Pa {A : Type} (a : A) : Matrix A A ℂ := (g79e_u a)ᴴ * g79e_u a

theorem g79e_Pa_apply {A : Type} (a i j : A) : g79e_Pa a i j = if i = a ∧ j = a then 1 else 0 := by
  simp only [g79e_Pa, g79e_u, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.univ_unique,
    Finset.sum_singleton]
  by_cases hi : i = a <;> by_cases hj : j = a <;> simp [hi, hj]

theorem g79e_Pa_psd {A : Type} [Fintype A] (a : A) : (g79e_Pa a).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem g79e_Pa_trace {A : Type} [Fintype A] (a : A) : (g79e_Pa a).trace.re = 1 := by
  simp [Matrix.trace, g79e_Pa_apply]

theorem g79e_pow_id {A : Type} (N : ℕ) :
    traceClassChannelPower (id : Operation A A) N = id := by
  induction N with
  | zero =>
    funext X a b
    simp only [traceClassChannelPower, id]
    congr 1 <;> exact Subsingleton.elim _ _
  | succ N ih =>
    funext X a b
    simp only [traceClassChannelPower, ih, id]
    rw [Fin.cons_self_tail, Fin.cons_self_tail]

theorem g79e_stab_zero {A B : Type} (C : Operation A B) (hC : ∀ X, C X = 0) :
    stabilizedTraceClassNorm C = 0 := by
  refine le_antisymm (iSup_le fun n => iSup_le fun X => ?_) bot_le
  have : tensorApply C X.val = 0 := by
    funext p q
    have h := hC (fun i j => X.val (i, p.2) (j, q.2) : Matrix A A ℂ)
    exact congrFun (congrFun h p.1) q.1
  rw [this, g79e_traceSize_zero]

/-- exact code when the target embeds into the middle system -/
theorem g79e_dist_zero {A B : Type} [Fintype A] [Fintype B] [Nonempty A] (f : A → B)
    (hf : Function.Injective f) :
    codingSimulationDistance (id : Operation B B) (id : Operation A A) = 0 := by
  obtain ⟨a0⟩ := ‹Nonempty A›
  obtain ⟨V, hV⟩ : ∃ V : Matrix B A ℂ, ∀ b a, V b a = if b = f a then 1 else 0 :=
    ⟨Matrix.of fun b a => if b = f a then 1 else 0, fun _ _ => rfl⟩
  have hVV : Vᴴ * V = 1 := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hV]
    by_cases h : a = a'
    · subst h; simp [Matrix.one_apply]
    · rw [Matrix.one_apply_ne h]
      refine Finset.sum_eq_zero (fun b _ => ?_)
      by_cases h1 : b = f a
      · have : b ≠ f a' := fun h2 => h (hf (h1.symm.trans h2))
        simp [h1, this, hf.ne h]
      · simp [h1]
  obtain ⟨Kd, hKd0, hKds⟩ : ∃ Kd : Option B → Matrix A B ℂ, Kd none = Vᴴ ∧
      ∀ b, Kd (some b) = if ∃ a, f a = b then 0 else Matrix.single a0 b 1 :=
    ⟨fun o => match o with
      | none => Vᴴ
      | some b => if ∃ a, f a = b then 0 else Matrix.single a0 b 1, rfl, fun _ => rfl⟩
  have hKdV : ∀ b, Kd (some b) * V = 0 := by
    intro b
    rw [hKds]
    split_ifs with h
    · simp
    · ext a a'
      simp only [Matrix.mul_apply, Matrix.single_apply, hV, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun b' _ => ?_)
      by_cases hb : b = b'
      · subst hb
        have : b ≠ f a' := fun h' => h ⟨a', h'.symm⟩
        simp [this]
      · simp [hb]
  have hVVt : V * Vᴴ = Matrix.diagonal (fun b => if ∃ a, f a = b then 1 else 0) := by
    ext b b'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hV, Matrix.diagonal_apply]
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [Finset.sum_eq_single a]
      · by_cases h' : f a = b'
        · subst h'; simp <;> exact ⟨a, rfl⟩
        · simp [h', Ne.symm h']
      · intro a' _ ha; simp [hf.ne (Ne.symm ha)]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hb]
      · intro a _
        have : b ≠ f a := fun h => hb ⟨a, h.symm⟩
        simp [this]
  have hS : ∀ b, (Kd (some b))ᴴ * Kd (some b) =
      if ∃ a, f a = b then 0 else Matrix.single b b 1 := by
    intro b
    rw [hKds]
    split_ifs with h
    · simp
    · ext x y
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply]
      rw [Finset.sum_eq_single a0]
      · by_cases hx : b = x <;> by_cases hy : b = y <;> simp [hx, hy]
      · intro a' _ ha; simp [Ne.symm ha]
      · simp
  have hKd1 : ∑ o, (Kd o)ᴴ * Kd o = 1 := by
    rw [Fintype.sum_option]
    simp only [hS]
    have h0 : (Kd none)ᴴ * Kd none = V * Vᴴ := by
      rw [hKd0, Matrix.conjTranspose_conjTranspose]
    rw [h0, hVVt]
    ext b b'
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases hbb : b = b'
    · subst hbb
      rw [Matrix.one_apply_eq, if_pos rfl]
      by_cases hr : ∃ a, f a = b
      · rw [if_pos hr, Finset.sum_eq_zero]
        · simp
        · intro c _
          split_ifs with hc
          · simp
          · simp only [Matrix.single_apply]
            split_ifs with h3
            · exact absurd (h3.1 ▸ hr) hc
            · rfl
      · rw [if_neg hr, Finset.sum_eq_single b]
        · simp [hr]
        · intro c _ hc
          split_ifs <;> simp [Matrix.single_apply, hc]
        · simp
    · rw [Matrix.one_apply_ne hbb, if_neg hbb, zero_add]
      refine Finset.sum_eq_zero (fun c _ => ?_)
      split_ifs <;> simp [Matrix.single_apply]
      exact fun h3 h4 => hbb (h3.symm.trans h4)
  have hE : IsTraceClassChannel (g79e_kmap (fun _ : Unit => V)) :=
    g79e_kraus _ (by simpa using hVV)
  have hD : IsTraceClassChannel (g79e_kmap Kd) := g79e_kraus _ hKd1
  refine le_antisymm (iInf_le_of_le ⟨_, hE⟩ (iInf_le_of_le ⟨_, hD⟩ ?_)) bot_le
  rw [g79e_stab_zero]
  intro X
  simp only [id, g79e_kmap, Finset.univ_unique, Finset.sum_singleton, Fintype.sum_option]
  rw [sub_eq_zero]
  have h1 : Vᴴ * (V * X * Vᴴ) * Vᴴᴴ = X := by
    rw [Matrix.conjTranspose_conjTranspose]
    simp only [← Matrix.mul_assoc]
    rw [hVV, Matrix.one_mul, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have h2 : ∀ b, Kd (some b) * (V * X * Vᴴ) * (Kd (some b))ᴴ = 0 := by
    intro b
    simp only [← Matrix.mul_assoc]
    rw [hKdV b]
    simp
  rw [hKd0]
  rw [Finset.sum_eq_zero (fun b _ => h2 b), add_zero]
  exact h1

theorem g79e_lower {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (E : TCChannel A B) (D : TCChannel B A) :
    ENNReal.ofReal (1 - (Fintype.card B : ℝ) / Fintype.card A) ≤
      stabilizedTraceClassNorm (fun X => D.val (id (E.val X)) - id X) := by
  have hnA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hnB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  set g : A → ℝ := fun a => (D.val (E.val (g79e_Pa a)) a a).re with hg
  have hτ : ∀ a, (E.val (g79e_Pa a)).PosSemidef ∧ (E.val (g79e_Pa a)).trace.re = 1 :=
    fun a => g79e_chan_dens E.2 (g79e_Pa_psd a) (g79e_Pa_trace a)
  have hle : ∀ a, g a ≤ (D.val 1 a a).re := by
    intro a
    have hp := g79e_le_trace (hτ a).1
    rw [(hτ a).2] at hp
    have h0 := g79e_chan_pos D.2 hp a
    have e : ((((1:ℝ) : ℂ) • (1 : Matrix B B ℂ)) - E.val (g79e_Pa a)) + E.val (g79e_Pa a) = 1 := by
      simp
    have h1 : (D.val ((((1:ℝ) : ℂ) • (1 : Matrix B B ℂ)) - E.val (g79e_Pa a) + E.val (g79e_Pa a)) a a).re
        = (D.val 1 a a).re := by rw [e]
    rw [g79e_chan_add D.2] at h1
    simp only [Matrix.add_apply, Complex.add_re] at h1
    simp only [hg]
    linarith
  have hsumJ : ∑ a, (D.val 1 a a).re = Fintype.card B := by
    have hJ : (((Fintype.card B : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix B B ℂ) = ((Fintype.card B : ℝ)⁻¹ : ℝ) • (1 : Matrix B B ℂ) := rfl
    have hpsd : ((((Fintype.card B : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix B B ℂ)).PosSemidef :=
      Matrix.PosSemidef.smul Matrix.PosSemidef.one (by exact_mod_cast (inv_pos.mpr hnB).le)
    have htr : ((((Fintype.card B : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix B B ℂ)).trace.re = 1 := by
      rw [Matrix.trace_smul, Matrix.trace_one]
      simp only [smul_eq_mul, Complex.re_ofReal_mul, Complex.natCast_re]
      field_simp
    have h2 := (g79e_chan_dens D.2 hpsd htr).2
    rw [g79e_chan_smul D.2, Matrix.trace_smul] at h2
    simp only [smul_eq_mul, Complex.re_ofReal_mul] at h2
    rw [Matrix.trace, Complex.re_sum] at h2
    field_simp at h2
    simpa using h2
  have hsum : ∑ a, g a ≤ ∑ _a : A, (Fintype.card B : ℝ) / Fintype.card A := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    rw [← hsumJ]
    exact Finset.sum_le_sum (fun a _ => hle a)
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  -- test input
  have hts : traceSize (g79e_L (g79e_Pa a)) ≤ 1 := by
    have := g79e_ts2 (g79e_L (g79e_Pa a)) (g79e_e (a, 0)) (g79e_e (a, 0)) 0 0 (fun p q => by
      simp only [g79e_L, g79e_Pa_apply, g79e_e_apply]
      have hp : (p = (a, 0)) ↔ p.1 = a := by
        constructor
        · rintro rfl; rfl
        · intro h; exact Prod.ext h (Subsingleton.elim _ _)
      have hq : (q = (a, 0)) ↔ q.1 = a := by
        constructor
        · rintro rfl; rfl
        · intro h; exact Prod.ext h (Subsingleton.elim _ _)
      by_cases h1 : p.1 = a <;> by_cases h2 : q.1 = a <;> simp [h1, h2, hp, hq])
    simpa [g79e_e_norm] using this
  refine le_trans ?_ (le_iSup_of_le 1 (le_iSup_of_le ⟨g79e_L (g79e_Pa a), g79e_tc _, hts⟩ le_rfl))
  refine le_trans ?_ (g79e_coef_le _ (a, 0) (a, 0))
  apply ENNReal.ofReal_le_ofReal
  show 1 - (Fintype.card B : ℝ) / Fintype.card A ≤
    ‖D.val (E.val (g79e_Pa a)) a a - g79e_Pa a a a‖
  rw [g79e_Pa_apply, if_pos ⟨rfl, rfl⟩]
  refine le_trans ?_ (Complex.abs_re_le_norm _)
  rw [Complex.sub_re, Complex.one_re]
  have : g a ≤ _ := ha
  simp only [hg] at this
  rw [abs_sub_comm]
  exact le_trans (by linarith) (le_abs_self _)

theorem g79e_block_id (n m : ℕ) (N M : ℕ+) :
    blockError (id : Operation (Fin n) (Fin n)) (id : Operation (Fin m) (Fin m)) N M =
      codingSimulationDistance (id : Operation (Fin (N : ℕ) → Fin n) (Fin (N : ℕ) → Fin n))
        (id : Operation (Fin (M : ℕ) → Fin m) (Fin (M : ℕ) → Fin m)) := by
  simp only [blockError, g79e_pow_id]

theorem g79e_ratio (M N : ℕ+) : ((M : ℝ≥0∞) / (N : ℝ≥0∞)) = ENNReal.ofReal ((M : ℝ) / (N : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  simp

/-- The ideal-channel capacity. -/
theorem g79e_idealCap (n m : ℕ) (hn : 0 < n) (hm : 2 ≤ m) :
    relativeCapacity (id : Operation (Fin n) (Fin n)) (id : Operation (Fin m) (Fin m)) =
      ENNReal.ofReal (Real.log n / Real.log m) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  set c := Real.log n / Real.log m with hc
  have hc0 : 0 ≤ c := div_nonneg hlogn hlogm.le
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  apply le_antisymm
  · refine iSup_le fun R => ?_
    obtain ⟨R, hR0, hR⟩ := R
    apply ENNReal.ofReal_le_ofReal
    by_contra hlt
    push_neg at hlt
    obtain ⟨r, hcr, hrR⟩ := exists_rat_btwn hlt
    have hr0 : (0 : ℝ) < r := lt_of_le_of_lt hc0 hcr
    have hr0' : (0 : ℚ) < r := by exact_mod_cast hr0
    set p : ℕ := r.num.toNat with hp
    set q : ℕ := r.den with hq
    have hpq : (r : ℝ) = (p : ℝ) / q := by
      have h1 : (0 : ℤ) < r.num := Rat.num_pos.mpr hr0'
      have h2 : ((r.num.toNat : ℤ)) = r.num := Int.toNat_of_nonneg h1.le
      rw [hp, hq]
      have : ((r.num.toNat : ℕ) : ℝ) = ((r.num : ℤ) : ℝ) := by exact_mod_cast h2
      rw [this]
      exact_mod_cast (Rat.num_div_den r).symm
    have hp0 : 0 < p := by
      have : (0 : ℝ) < p / q := hpq ▸ hr0
      have hq0 : (0 : ℝ) < q := by exact_mod_cast r.pos
      have := (div_pos_iff_of_pos_right hq0).mp this
      exact_mod_cast this
    have hq0 : 0 < q := r.pos
    let Nf : ℕ → ℕ+ := fun a => ⟨q * (a + 1), by positivity⟩
    let Mf : ℕ → ℕ+ := fun a => ⟨p * (a + 1), by positivity⟩
    have hrat : ∀ a, ((Mf a : ℕ+) : ℝ) / ((Nf a : ℕ+) : ℝ) = r := by
      intro a
      rw [hpq]
      simp only [Nf, Mf, PNat.mk_coe]
      push_cast
      field_simp
    have hT := hR Nf Mf ?_ ?_
    rotate_left
    · simp only [Nf, PNat.mk_coe]
      refine Filter.tendsto_atTop_mono (fun a => ?_) (tendsto_add_atTop_nat 1)
      nlinarith
    · refine Filter.limsup_le_of_le (by isBoundedDefault) (Filter.Eventually.of_forall fun a => ?_)
      simp only [rateRatio]
      rw [g79e_ratio, hrat]
      exact ENNReal.ofReal_le_ofReal hrR.le
    -- error stays large
    have hq1 : (n : ℝ) ^ q < (m : ℝ) ^ p := by
      have h1 : (q : ℝ) * Real.log n < p * Real.log m := by
        have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
        have := hcr
        rw [hpq, hc, div_lt_div_iff₀ hlogm hq0'] at this
        linarith
      rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      exact h1
    set t : ℝ := (n : ℝ) ^ q / (m : ℝ) ^ p with ht
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t < 1 := (div_lt_one (by positivity)).mpr hq1
    have hlim : Tendsto (fun a : ℕ => t ^ (a + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).comp (tendsto_add_atTop_nat 1)
    have hev : ∀ᶠ a in atTop, t ^ (a + 1) < 1 / 2 := hlim.eventually (gt_mem_nhds (by norm_num))
    have hbig : ∀ᶠ a in atTop, ENNReal.ofReal (1 / 2) ≤
        blockError (id : Operation (Fin n) (Fin n)) (id : Operation (Fin m) (Fin m)) (Nf a) (Mf a) := by
      filter_upwards [hev] with a ha
      rw [g79e_block_id]
      refine le_iInf fun E => le_iInf fun D => le_trans ?_ (g79e_lower E D)
      apply ENNReal.ofReal_le_ofReal
      rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        Fintype.card_fin, Fintype.card_fin]
      simp only [Nf, Mf, PNat.mk_coe]
      have : ((n ^ (q * (a + 1)) : ℕ) : ℝ) / ((m ^ (p * (a + 1)) : ℕ) : ℝ) = t ^ (a + 1) := by
        rw [ht, div_pow]; push_cast; rw [pow_mul, pow_mul]
      rw [this]; linarith
    have hsmall := hT.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) by simp))
    obtain ⟨a, h1, h2⟩ := (hbig.and hsmall).exists
    exact absurd h1 (not_le.mpr h2)
  · rcases hc0.eq_or_lt with h0 | hcpos
    · rw [← h0]; simp
    refine le_of_forall_lt (fun x hx => ?_)
    have hxt : x ≠ ⊤ := ne_top_of_lt hx
    have hx' : x.toReal < c := by
      rw [← ENNReal.ofReal_toReal hxt] at hx
      exact (ENNReal.ofReal_lt_ofReal_iff hcpos).mp hx
    set R := (max x.toReal 0 + c) / 2 with hRdef
    have hR0 : 0 < R := by rw [hRdef]; have := le_max_right x.toReal 0; linarith
    have hRc : R < c := by rw [hRdef]; have := max_lt hx' hcpos; linarith
    have hxR : x < ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_toReal hxt]
      refine (ENNReal.ofReal_lt_ofReal_iff hR0).mpr ?_
      rw [hRdef]; have := le_max_left x.toReal 0; linarith
    refine lt_of_lt_of_le hxR (le_iSup_of_le ⟨R, hR0, ?_⟩ le_rfl)
    intro Nf Mf _ hlim
    set R' := (R + c) / 2 with hR'
    have hlt : Filter.limsup (rateRatio Nf Mf) atTop < ENNReal.ofReal R' :=
      lt_of_le_of_lt hlim ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
    have hev := Filter.eventually_lt_of_limsup_lt hlt
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with a ha
    simp only [rateRatio] at ha
    rw [g79e_ratio, ENNReal.ofReal_lt_ofReal_iff (by linarith)] at ha
    have hN0 : (0 : ℝ) < (Nf a : ℝ) := by positivity
    have hMN : ((Mf a : ℕ) : ℝ) * Real.log m < (Nf a : ℕ) * Real.log n := by
      have h1 : ((Mf a : ℕ) : ℝ) < R' * (Nf a : ℕ) := by
        have := (div_lt_iff₀ hN0).mp ha
        exact_mod_cast this
      have h2 : R' * Real.log m < Real.log n := by
        have : R' < Real.log n / Real.log m := by rw [← hc]; linarith
        exact (lt_div_iff₀ hlogm).mp this
      have hN0' : (0 : ℝ) < ((Nf a : ℕ) : ℝ) := by exact_mod_cast hN0
      nlinarith
    have hcard : (m : ℝ) ^ (Mf a : ℕ) < (n : ℝ) ^ (Nf a : ℕ) := by
      rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      exact hMN
    have hcard' : Fintype.card (Fin (Mf a : ℕ) → Fin m) ≤ Fintype.card (Fin (Nf a : ℕ) → Fin n) := by
      simp only [Fintype.card_fun, Fintype.card_fin]
      have : ((m ^ (Mf a : ℕ) : ℕ) : ℝ) < ((n ^ (Nf a : ℕ) : ℕ) : ℝ) := by push_cast; exact hcard
      exact_mod_cast this.le
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard'
    rw [g79e_block_id, g79e_dist_zero f f.injective]

theorem solution (n m : ℕ) (hn : 0 < n) (hm : 2 ≤ m) :
    relativeCapacity (id : Operation (Fin n) (Fin n)) (id : Operation (Fin m) (Fin m)) =
      ENNReal.ofReal (Real.logb 2 n / Real.logb 2 m) := by
  rw [g79e_idealCap n m hn hm]
  congr 1
  rw [Real.logb, Real.logb, div_div_div_cancel_right₀ (Real.log_pos one_lt_two).ne']
