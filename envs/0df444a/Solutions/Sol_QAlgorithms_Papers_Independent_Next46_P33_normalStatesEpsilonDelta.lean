-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P33.normalStatesEpsilonDelta
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T01:28:31.361368+00:00
-- url     : https://prove2.me/submissions/f8573107-cc37-482e-87d2-2557943ed8d5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexOrder InnerProductSpace

namespace P33Aux

open QAlgorithms.Papers.Independent.Next46.P33

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma le_iff_inner (a b : H →L[ℂ] H) : a ≤ b ↔ ∀ x, 0 ≤ ⟪(b - a) x, x⟫_ℂ := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex]
  refine forall_congr' fun x => ?_
  generalize ⟪(b - a) x, x⟫_ℂ = z
  rw [Complex.nonneg_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have := congrArg Complex.im h1
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    apply Complex.ext <;> simp [h2]

lemma norm_sq_le_inner (T : H →L[ℂ] H) (h0 : 0 ≤ T) (h1 : T ≤ 1) (u : H) :
    ‖T u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_ℂ := by
  set s := CFC.sqrt T with hs
  have hsT : s * s = T := CFC.sqrt_mul_sqrt_self T h0
  have hsa : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
  have hnT : ‖T‖ ≤ 1 := by
    have := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 h1
    exact this.trans ContinuousLinearMap.norm_id_le
  have hns : ‖s‖ * ‖s‖ ≤ 1 := by
    have : ‖star s * s‖ = ‖s‖ * ‖s‖ := CStarRing.norm_star_mul_self
    rw [hsa.star_eq, hsT] at this
    linarith
  have hns1 : ‖s‖ ≤ 1 := by nlinarith [norm_nonneg s]
  have h1' : ‖T u‖ ≤ ‖s u‖ := by
    rw [← hsT, ContinuousLinearMap.mul_apply]
    calc ‖s (s u)‖ ≤ ‖s‖ * ‖s u‖ := s.le_opNorm _
      _ ≤ 1 * ‖s u‖ := by gcongr
      _ = ‖s u‖ := one_mul _
  have h2 : RCLike.re ⟪T u, u⟫_ℂ = ‖s u‖ ^ 2 := by
    rw [← hsT, ContinuousLinearMap.mul_apply]
    have := hsa.isSymmetric (s u) u
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    exact inner_self_eq_norm_sq (s u)
  rw [h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h1' 2

lemma exists_lim (x : ℕ → H →L[ℂ] H) (hx : Monotone x) (h0 : 0 ≤ x 0) (h1 : ∀ n, x n ≤ 1) :
    ∃ y : H →L[ℂ] H, ∀ u, Tendsto (fun n => x n u) atTop (𝓝 (y u)) := by
  have hcau : ∀ u, CauchySeq (fun n => x n u) := by
    intro u
    set f : ℕ → ℝ := fun n => RCLike.re ⟪x n u, u⟫_ℂ with hfdef
    have fmono : Monotone f := by
      intro m n hmn
      have := (le_iff_inner _ _).1 (hx hmn) u
      have h' := (Complex.nonneg_iff.1 this).1
      simp only [hfdef, ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re] at h' ⊢
      simp only [RCLike.re_to_complex]
      linarith
    have fbdd : BddAbove (Set.range f) := by
      refine ⟨RCLike.re ⟪u, u⟫_ℂ, ?_⟩
      rintro _ ⟨n, rfl⟩
      have := (le_iff_inner _ _).1 (h1 n) u
      have h' := (Complex.nonneg_iff.1 this).1
      simp only [hfdef, ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re,
        ContinuousLinearMap.one_apply] at h' ⊢
      simp only [RCLike.re_to_complex]
      linarith
    have hf : CauchySeq f := (tendsto_atTop_ciSup fmono fbdd).cauchySeq
    rw [Metric.cauchySeq_iff'] at hf ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hf (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hT0 : 0 ≤ x n - x N := sub_nonneg.2 (hx hn)
    have hT1 : x n - x N ≤ 1 :=
      calc x n - x N ≤ x n := sub_le_self _ (h0.trans (hx (Nat.zero_le N)))
        _ ≤ 1 := h1 n
    have key := norm_sq_le_inner (x n - x N) hT0 hT1 u
    have hfN := hN n hn
    rw [Real.dist_eq] at hfN
    rw [dist_eq_norm]
    have hre : RCLike.re ⟪(x n - x N) u, u⟫_ℂ = f n - f N := by
      simp [hfdef, inner_sub_left]
    rw [ContinuousLinearMap.sub_apply] at key
    have hlt : ‖x n u - x N u‖ ^ 2 < ε ^ 2 := by
      calc ‖x n u - x N u‖ ^ 2 ≤ _ := key
        _ = f n - f N := by rw [← hre, ContinuousLinearMap.sub_apply]
        _ ≤ |f n - f N| := le_abs_self _
        _ < ε ^ 2 := hfN
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  choose g hg using fun u => cauchySeq_tendsto_of_complete (hcau u)
  have ht : Tendsto (fun n u => x n u) atTop (𝓝 g) := tendsto_pi_nhds.2 hg
  exact ⟨continuousLinearMapOfTendsto x ht, fun u => hg u⟩

lemma inner_lim (x : ℕ → H →L[ℂ] H) (y : H →L[ℂ] H)
    (hy : ∀ u, Tendsto (fun n => x n u) atTop (𝓝 (y u))) (u v : H) :
    Tendsto (fun n => ⟪x n u, v⟫_ℂ) atTop (𝓝 ⟪y u, v⟫_ℂ) :=
  (hy u).inner tendsto_const_nhds

lemma le_lim (x : ℕ → H →L[ℂ] H) (hx : Monotone x) (y : H →L[ℂ] H)
    (hy : ∀ u, Tendsto (fun n => x n u) atTop (𝓝 (y u))) (n : ℕ) : x n ≤ y := by
  rw [le_iff_inner]
  intro u
  have ht : Tendsto (fun m => ⟪x m u, u⟫_ℂ - ⟪x n u, u⟫_ℂ) atTop
      (𝓝 (⟪y u, u⟫_ℂ - ⟪x n u, u⟫_ℂ)) := (inner_lim x y hy u u).sub tendsto_const_nhds
  rw [ContinuousLinearMap.sub_apply, inner_sub_left]
  refine ge_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  have := (le_iff_inner _ _).1 (hx hm) u
  rwa [ContinuousLinearMap.sub_apply, inner_sub_left] at this

lemma lim_le (x : ℕ → H →L[ℂ] H) (y : H →L[ℂ] H)
    (hy : ∀ u, Tendsto (fun n => x n u) atTop (𝓝 (y u))) (b : H →L[ℂ] H)
    (hb : ∀ n, x n ≤ b) : y ≤ b := by
  rw [le_iff_inner]
  intro u
  have ht : Tendsto (fun m => ⟪b u, u⟫_ℂ - ⟪x m u, u⟫_ℂ) atTop
      (𝓝 (⟪b u, u⟫_ℂ - ⟪y u, u⟫_ℂ)) := tendsto_const_nhds.sub (inner_lim x y hy u u)
  rw [ContinuousLinearMap.sub_apply, inner_sub_left]
  refine ge_of_tendsto ht (Eventually.of_forall fun m => ?_)
  have := (le_iff_inner _ _).1 (hb m) u
  rwa [ContinuousLinearMap.sub_apply, inner_sub_left] at this

lemma lim_mem (M : VonNeumannAlgebra H) (x : ℕ → H →L[ℂ] H) (y : H →L[ℂ] H)
    (hy : ∀ u, Tendsto (fun n => x n u) atTop (𝓝 (y u))) (hxM : ∀ n, x n ∈ M) : y ∈ M := by
  rw [← SetLike.mem_coe, ← M.centralizer_centralizer, Set.mem_centralizer_iff]
  intro T hT
  rw [Set.mem_centralizer_iff] at hT
  ext u
  simp only [ContinuousLinearMap.mul_apply]
  have h1 : Tendsto (fun n => T (x n u)) atTop (𝓝 (T (y u))) :=
    (T.continuous.tendsto _).comp (hy u)
  have h2 : Tendsto (fun n => x n (T u)) atTop (𝓝 (y (T u))) := hy (T u)
  have heq : ∀ n, T (x n u) = x n (T u) := by
    intro n
    have := congrArg (fun F : H →L[ℂ] H => F u) (hT (x n) (hxM n))
    simpa using this.symm
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

lemma exists_lub (M : VonNeumannAlgebra H) (x : ℕ → H →L[ℂ] H) (hx : Monotone x)
    (hxM : ∀ n, x n ∈ M) (h0 : ∀ n, 0 ≤ x n) (h1 : ∀ n, x n ≤ 1) :
    ∃ y : H →L[ℂ] H, y ∈ M ∧ 0 ≤ y ∧ y ≤ 1 ∧ (∀ n, x n ≤ y) ∧
      ∀ b, (∀ n, x n ≤ b) → y ≤ b := by
  obtain ⟨y, hy⟩ := exists_lim x hx (h0 0) h1
  exact ⟨y, lim_mem M x y hy hxM, (h0 0).trans (le_lim x hx y hy 0), lim_le x y hy 1 h1,
    le_lim x hx y hy, lim_le x y hy⟩

open Classical in
/-- Value of a weight on a raw operator (zero off the positive part). -/
def wv {M : VonNeumannAlgebra H} (w : Weight M) (a : H →L[ℂ] H) : ℝ≥0∞ :=
  if h : a ∈ M ∧ 0 ≤ a then w.value ⟨a, h⟩ else 0

lemma wv_eq {M : VonNeumannAlgebra H} (w : Weight M) (p : PositivePart M) :
    wv w p.val = w.value p := by
  unfold wv
  rw [dif_pos p.2]

lemma wv_add {M : VonNeumannAlgebra H} (w : Weight M) {a b : H →L[ℂ] H}
    (ha : a ∈ M ∧ 0 ≤ a) (hb : b ∈ M ∧ 0 ≤ b) :
    wv w (a + b) = wv w a + wv w b := by
  have hab : a + b ∈ M ∧ 0 ≤ a + b := ⟨add_mem ha.1 hb.1, add_nonneg ha.2 hb.2⟩
  unfold wv
  rw [dif_pos hab, dif_pos ha, dif_pos hb]
  exact w.add_value ⟨a, ha⟩ ⟨b, hb⟩ ⟨a + b, hab⟩ rfl

lemma wv_mono {M : VonNeumannAlgebra H} (w : Weight M) {a b : H →L[ℂ] H}
    (ha : a ∈ M ∧ 0 ≤ a) (hb : b ∈ M ∧ 0 ≤ b) (hab : a ≤ b) : wv w a ≤ wv w b := by
  have hc : b - a ∈ M ∧ 0 ≤ b - a := ⟨sub_mem hb.1 ha.1, sub_nonneg.2 hab⟩
  have : b = a + (b - a) := by abel
  calc wv w a ≤ wv w a + wv w (b - a) := le_self_add
    _ = wv w (a + (b - a)) := (wv_add w ha hc).symm
    _ = wv w b := by rw [← this]

lemma wv_zero {M : VonNeumannAlgebra H} (w : Weight M) : wv w 0 = 0 := by
  have h : (0 : H →L[ℂ] H) ∈ M ∧ 0 ≤ (0 : H →L[ℂ] H) := ⟨zero_mem _, le_rfl⟩
  unfold wv
  rw [dif_pos h]
  exact w.zero_value _ rfl

lemma wv_sum {M : VonNeumannAlgebra H} (w : Weight M) (f : ℕ → H →L[ℂ] H)
    (hf : ∀ k, f k ∈ M ∧ 0 ≤ f k) (N : ℕ) :
    wv w (∑ k ∈ Finset.range N, f k) = ∑ k ∈ Finset.range N, wv w (f k) := by
  induction N with
  | zero => simp [wv_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    exact wv_add w ⟨sum_mem fun k _ => (hf k).1,
      Finset.sum_nonneg fun k _ => (hf k).2⟩ (hf N)

lemma wv_smul {M : VonNeumannAlgebra H} (w : Weight M) (r : NNReal) {a : H →L[ℂ] H}
    (ha : a ∈ M ∧ 0 ≤ a) : wv w ((r : ℂ) • a) = (r : ℝ≥0∞) * wv w a := by
  have hb : (r : ℂ) • a ∈ M ∧ 0 ≤ (r : ℂ) • a := by
    refine ⟨Subalgebra.smul_mem _ ha.1 _, ?_⟩
    have : (r : ℂ) • a = r • a := rfl
    rw [this]
    exact smul_nonneg r.2 ha.2
  unfold wv
  rw [dif_pos hb, dif_pos ha]
  exact w.smul_value r ⟨a, ha⟩ ⟨_, hb⟩ rfl

lemma normal_seq {M : VonNeumannAlgebra H} (w : Weight M) (hw : IsNormalWeight w)
    (x : ℕ → H →L[ℂ] H) (hx : Monotone x) (hxP : ∀ n, x n ∈ M ∧ 0 ≤ x n)
    (y : H →L[ℂ] H) (hyP : y ∈ M ∧ 0 ≤ y)
    (hub : ∀ n, x n ≤ y) (hlub : ∀ b, (∀ n, x n ≤ b) → y ≤ b) :
    wv w y = ⨆ n, wv w (x n) := by
  let X : ℕ → PositivePart M := fun n => ⟨x n, hxP n⟩
  have hX : Monotone X := fun m n h => hx h
  have hlub' : IsLUB (Set.range X) ⟨y, hyP⟩ := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact hub n
    · intro b hb
      exact hlub b.val (fun n => hb ⟨n, rfl⟩)
  have := hw (Set.range X) (Set.range_nonempty X) (directedOn_range.2 hX.directed_le)
    ⟨y, hyP⟩ hlub'
  unfold wv
  rw [dif_pos hyP, this, iSup_range' (fun b : PositivePart M => w.value b) X]
  congr 1
  ext n
  rw [dif_pos (hxP n)]

lemma isUnit_one_add {h : H →L[ℂ] H} (hh : 0 ≤ h) : IsUnit (1 + h) :=
  (isStrictlyPositive_one.add_nonneg hh).isUnit

lemma inv_eq_unit {h : H →L[ℂ] H} (hh : 0 ≤ h) :
    Ring.inverse (1 + h) = ↑((isUnit_one_add hh).unit⁻¹) := by
  rw [← Ring.inverse_unit, IsUnit.unit_spec]

lemma inv_nonneg' {h : H →L[ℂ] H} (hh : 0 ≤ h) : 0 ≤ Ring.inverse (1 + h) := by
  rw [inv_eq_unit hh]
  exact CFC.inv_nonneg_of_nonneg _ (by rw [IsUnit.unit_spec]; exact add_nonneg zero_le_one hh)

lemma inv_antitone {a b : H →L[ℂ] H} (ha : 0 ≤ a) (hab : a ≤ b) :
    Ring.inverse (1 + b) ≤ Ring.inverse (1 + a) := by
  have hb : 0 ≤ b := ha.trans hab
  rw [inv_eq_unit ha, inv_eq_unit hb]
  exact CStarAlgebra.inv_le_inv (by rw [IsUnit.unit_spec]; exact add_nonneg zero_le_one ha)
    (by rw [IsUnit.unit_spec, IsUnit.unit_spec]; exact add_le_add le_rfl hab)

/-- The resolvent transform `h ↦ h (1 + h)⁻¹ = 1 - (1 + h)⁻¹`. -/
def res (h : H →L[ℂ] H) : H →L[ℂ] H := 1 - Ring.inverse (1 + h)

lemma res_nonneg {h : H →L[ℂ] H} (hh : 0 ≤ h) : 0 ≤ res h := by
  have := inv_antitone le_rfl hh
  rw [add_zero, Ring.inverse_one] at this
  exact sub_nonneg.2 this

lemma res_le_one {h : H →L[ℂ] H} (hh : 0 ≤ h) : res h ≤ 1 :=
  sub_le_self _ (inv_nonneg' hh)

lemma res_mono {a b : H →L[ℂ] H} (ha : 0 ≤ a) (hab : a ≤ b) : res a ≤ res b :=
  sub_le_sub_left (inv_antitone ha hab) 1

lemma res_le_self {h : H →L[ℂ] H} (hh : 0 ≤ h) : res h ≤ h := by
  set v := Ring.inverse (1 + h) with hv
  have hu := isUnit_one_add hh
  have h1 : (1 + h) * v = 1 := Ring.mul_inverse_cancel _ hu
  have h2 : v * (1 + h) = 1 := Ring.inverse_mul_cancel _ hu
  have hv1 : h * v = 1 - v := by
    rw [add_mul, one_mul] at h1
    rw [eq_sub_iff_add_eq, add_comm]
    exact h1
  have hv2 : v * h = 1 - v := by
    rw [mul_add, mul_one] at h2
    rw [eq_sub_iff_add_eq, add_comm]
    exact h2
  have key : h - res h = star h * v * h := by
    rw [(IsSelfAdjoint.of_nonneg hh).star_eq, hv1, sub_mul, one_mul, hv2, res]
  have : 0 ≤ h - res h := by
    rw [key]
    exact star_left_conjugate_nonneg (inv_nonneg' hh) h
  exact sub_nonneg.1 this

lemma res_mem (M : VonNeumannAlgebra H) {h : H →L[ℂ] H} (hh : 0 ≤ h) (hM : h ∈ M) :
    res h ∈ M := by
  have hinv : Ring.inverse (1 + h) ∈ M := by
    rw [inv_eq_unit hh, ← SetLike.mem_coe, ← M.centralizer_centralizer,
      Set.mem_centralizer_iff]
    intro T hT
    rw [Set.mem_centralizer_iff] at hT
    have hc : Commute T ↑(isUnit_one_add hh).unit := by
      rw [IsUnit.unit_spec]
      exact (hT (1 + h) (add_mem (one_mem _) hM)).symm
    exact hc.units_inv_right
  exact sub_mem (one_mem _) hinv

lemma res_proj {e : H →L[ℂ] H} (he : IsStarProjection e) :
    res e = ((2⁻¹ : NNReal) : ℂ) • e := by
  have hh : 0 ≤ e := (ContinuousLinearMap.nonneg_iff_isPositive _).2
    (ContinuousLinearMap.IsPositive.of_isStarProjection he)
  have hee : e * e = e := he.isIdempotentElem.eq
  set c : H →L[ℂ] H := 1 - ((2⁻¹ : NNReal) : ℂ) • e with hc
  have hmul : (1 + e) * c = 1 := by
    rw [hc, mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hee]
    have : ((2⁻¹ : NNReal) : ℂ) = 2⁻¹ := by simp
    rw [this]
    module
  have hu := isUnit_one_add hh
  have h2 : Ring.inverse (1 + e) * (1 + e) = 1 := Ring.inverse_mul_cancel _ hu
  have hv : Ring.inverse (1 + e) = c := by
    calc Ring.inverse (1 + e) = Ring.inverse (1 + e) * ((1 + e) * c) := by rw [hmul, mul_one]
      _ = (Ring.inverse (1 + e) * (1 + e)) * c := by rw [mul_assoc]
      _ = c := by rw [h2, one_mul]
  rw [res, hv, hc]
  abel

theorem main (M : VonNeumannAlgebra H) (phi1 phi0 : Weight M)
    (hN1 : IsNormalWeight phi1) (hF1 : IsFaithfulWeight phi1)
    (hN0 : IsNormalWeight phi0) (hS0 : IsStateWeight phi0) :
    WeightEpsilonDelta phi0 phi1 := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  choose e he1 he0 using fun k : ℕ => hcon ((2⁻¹ : ℝ) ^ k) (by positivity)
  set P : ℕ → H →L[ℂ] H := fun k => (e k).val with hPdef
  have hPP : ∀ k, P k ∈ M ∧ 0 ≤ P k := fun k => (projectionPositive (e k)).2
  have hP1 : ∀ k, wv phi1 (P k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have h := (he1 k).le
    rw [← wv_eq] at h
    refine h.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  have hP0 : ∀ k, ENNReal.ofReal ε ≤ wv phi0 (P k) := by
    intro k
    have h := he0 k
    rw [← wv_eq] at h
    exact h
  -- partial sums and their resolvents
  set hs : ℕ → ℕ → H →L[ℂ] H := fun n N => ∑ k ∈ Finset.range N, P (n + k) with hhs
  have hsP : ∀ n N, hs n N ∈ M ∧ 0 ≤ hs n N := fun n N =>
    ⟨sum_mem fun k _ => (hPP (n + k)).1,
      Finset.sum_nonneg fun k _ => (hPP (n + k)).2⟩
  have hs_succ : ∀ n N, hs n N ≤ hs n (N + 1) := by
    intro n N
    simp only [hhs, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hPP _).2
  have hs_shift : ∀ n N, hs (n + 1) N ≤ hs n (N + 1) := by
    intro n N
    simp only [hhs]
    rw [Finset.sum_range_succ']
    have : ∑ k ∈ Finset.range N, P (n + 1 + k) = ∑ k ∈ Finset.range N, P (n + (k + 1)) :=
      Finset.sum_congr rfl fun k _ => by rw [show n + 1 + k = n + (k + 1) by omega]
    rw [this]
    exact le_add_of_nonneg_right (hPP _).2
  set r : ℕ → ℕ → H →L[ℂ] H := fun n N => res (hs n N) with hr
  have rP : ∀ n N, r n N ∈ M ∧ 0 ≤ r n N := fun n N =>
    ⟨res_mem M (hsP n N).2 (hsP n N).1, res_nonneg (hsP n N).2⟩
  have r1 : ∀ n N, r n N ≤ 1 := fun n N => res_le_one (hsP n N).2
  have rmono : ∀ n, Monotone (r n) := fun n =>
    monotone_nat_of_le_succ fun N => res_mono (hsP n N).2 (hs_succ n N)
  -- first limits
  choose z hzM hz0 hz1 hzub hzlub using fun n =>
    exists_lub M (r n) (rmono n) (fun N => (rP n N).1) (fun N => (rP n N).2) (r1 n)
  have hzP : ∀ n, z n ∈ M ∧ 0 ≤ z n := fun n => ⟨hzM n, hz0 n⟩
  -- upper bound on phi1
  have hgeo : ∀ n N, wv phi1 (r n N) ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n N
    calc wv phi1 (r n N) ≤ wv phi1 (hs n N) :=
          wv_mono phi1 (rP n N) (hsP n N) (res_le_self (hsP n N).2)
      _ = ∑ k ∈ Finset.range N, wv phi1 (P (n + k)) := wv_sum phi1 _ (fun k => hPP _) N
      _ ≤ ∑ k ∈ Finset.range N, (2⁻¹ : ℝ≥0∞) ^ n * (2⁻¹ : ℝ≥0∞) ^ k :=
          Finset.sum_le_sum fun k _ => by rw [← pow_add]; exact hP1 _
      _ = (2⁻¹ : ℝ≥0∞) ^ n * ∑ k ∈ Finset.range N, (2⁻¹ : ℝ≥0∞) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ n * ∑' k, (2⁻¹ : ℝ≥0∞) ^ k := by
          gcongr
          exact ENNReal.sum_le_tsum _
      _ = 2 * (2⁻¹ : ℝ≥0∞) ^ n := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, mul_comm]
  have hz1bd : ∀ n, wv phi1 (z n) ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    rw [normal_seq phi1 hN1 (r n) (rmono n) (rP n) (z n) (hzP n) (hzub n) (hzlub n)]
    exact iSup_le fun N => hgeo n N
  -- lower bound on phi0
  have hz0bd : ∀ n, (2⁻¹ : ℝ≥0∞) * ENNReal.ofReal ε ≤ wv phi0 (z n) := by
    intro n
    have hr1 : r n 1 = ((2⁻¹ : NNReal) : ℂ) • P n := by
      simp only [hr, hhs, Finset.sum_range_one, add_zero]
      exact res_proj (e n).2.2
    calc (2⁻¹ : ℝ≥0∞) * ENNReal.ofReal ε ≤ (2⁻¹ : ℝ≥0∞) * wv phi0 (P n) := by
          gcongr
          exact hP0 n
      _ = wv phi0 (r n 1) := by
          rw [hr1, wv_smul phi0 _ (hPP n)]
          simp
      _ ≤ wv phi0 (z n) := wv_mono phi0 (rP n 1) (hzP n) (hzub n 1)
  -- z is antitone
  have hzanti : ∀ n, z (n + 1) ≤ z n := by
    intro n
    refine hzlub (n + 1) (z n) fun N => ?_
    calc r (n + 1) N ≤ r n (N + 1) := res_mono (hsP (n + 1) N).2 (hs_shift n N)
      _ ≤ z n := hzub n (N + 1)
  -- second limit
  set c : ℕ → H →L[ℂ] H := fun n => 1 - z n with hcdef
  have cmono : Monotone c :=
    monotone_nat_of_le_succ fun n => sub_le_sub_left (hzanti n) 1
  have cP : ∀ n, c n ∈ M ∧ 0 ≤ c n := fun n =>
    ⟨sub_mem (one_mem _) (hzM n), sub_nonneg.2 (hz1 n)⟩
  have c1 : ∀ n, c n ≤ 1 := fun n => sub_le_self _ (hz0 n)
  obtain ⟨y, hyM, hy0, hy1, hyub, hylub⟩ :=
    exists_lub M c cmono (fun n => (cP n).1) (fun n => (cP n).2) c1
  have hzzP : 1 - y ∈ M ∧ 0 ≤ 1 - y := ⟨sub_mem (one_mem _) hyM, sub_nonneg.2 hy1⟩
  have hzz_le : ∀ n, 1 - y ≤ z n := by
    intro n
    have := hyub n
    simp only [hcdef] at this
    rw [sub_le_comm]
    exact this
  have hzz0 : wv phi1 (1 - y) = 0 := by
    have hlim : Tendsto (fun n : ℕ => 2 * (2⁻¹ : ℝ≥0∞) ^ n) atTop (𝓝 (2 * 0)) :=
      ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)) (Or.inr (by simp))
    rw [mul_zero] at hlim
    refine le_antisymm (ge_of_tendsto' hlim fun n => ?_) bot_le
    exact (wv_mono phi1 hzzP (hzP n) (hzz_le n)).trans (hz1bd n)
  have hy_one : y = 1 := by
    have := hF1 ⟨1 - y, hzzP⟩ (by rw [← wv_eq]; exact hzz0)
    exact (sub_eq_zero.1 this).symm
  have hone : wv phi0 1 = 1 := (wv_eq phi0 (positiveOne M)).trans hS0
  have hnorm := normal_seq phi0 hN0 c cmono cP y ⟨hyM, hy0⟩ hyub hylub
  rw [hy_one, hone] at hnorm
  set a : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) * ENNReal.ofReal ε with ha
  have hcn : ∀ n, wv phi0 (c n) + a ≤ 1 := by
    intro n
    have hsum : wv phi0 (c n) + wv phi0 (z n) = 1 := by
      rw [← wv_add phi0 (cP n) (hzP n), ← hone]
      congr 1
      simp [hcdef]
    rw [← hsum]
    gcongr
    exact hz0bd n
  have hle : (⨆ n, wv phi0 (c n)) + a ≤ 1 := by
    rw [ENNReal.iSup_add]
    exact iSup_le hcn
  rw [← hnorm] at hle
  have ha0 : a ≠ 0 := by
    rw [ha]
    refine mul_ne_zero (by simp) ?_
    simpa using hε
  exact absurd hle (not_le.2 (ENNReal.lt_add_right ENNReal.one_ne_top ha0))

end P33Aux

open QAlgorithms.Papers.Independent.Next46.P33 in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (phi1 phi0 : Weight M)
    (hNormal1 : IsNormalWeight phi1) (hState1 : IsStateWeight phi1)
    (hFaithful1 : IsFaithfulWeight phi1)
    (hNormal0 : IsNormalWeight phi0) (hState0 : IsStateWeight phi0) :
    WeightEpsilonDelta phi0 phi1 := by
  exact P33Aux.main M phi1 phi0 hNormal1 hFaithful1 hNormal0 hState0
