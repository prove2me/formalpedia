-- Prove2me | solution 1 for RobustMeanCov.Projection.general_projection_property
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:05:20.314283+00:00
-- url     : https://prove2.me/submissions/4300ae37-fb2d-4888-a506-148ab238c6bf

import Mathlib
import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
import Definitions.Def_RobustMeanCov_Shared_MeanVarClass
open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder


namespace RobustMeanCov.Projection

theorem lift_sum_aux {ι E : Type*} [Fintype ι] [MeasurableSpace E] (ζ : Measure ℝ)
    (w : ENNReal) (hw : w ≠ ⊤) (F : ι → ℝ → E) (hF : ∀ p, Measurable (F p))
    (g : E → ℝ) (hg : Measurable g) (h : ∀ p, Integrable (fun t => g (F p t)) ζ) :
    Integrable g (∑ p, w • ζ.map (F p)) ∧
      ∫ x, g x ∂(∑ p, w • ζ.map (F p)) = w.toReal * ∑ p, ∫ t, g (F p t) ∂ζ := by
  have hI : ∀ p, Integrable g (w • ζ.map (F p)) := by
    intro p
    refine Integrable.smul_measure ?_ hw
    exact (integrable_map_measure hg.aestronglyMeasurable (hF p).aemeasurable).2 (h p)
  refine ⟨integrable_finsetSum_measure.2 fun p _ => hI p, ?_⟩
  rw [integral_finsetSum_measure fun p _ => hI p, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, integral_map (hF p).aemeasurable hg.aestronglyMeasurable,
    smul_eq_mul]

theorem exists_isotropic_lift_core {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) (hy : ⟪y, y⟫ = 1)
    (ζ : Measure ℝ) (hζ : ζ ∈ RobustMeanCov.Shared.MeanVarClass 0 1) :
    ∃ Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ),
      Q.map (fun Z => ⟪y, Z⟫) = ζ := by
  obtain ⟨hprob, hL2, hmean, hvar⟩ := hζ
  simp only [sub_zero] at hvar
  have hyy : ∑ k, y k * y k = 1 := by
    rw [← hy, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => by simp; try ring
  have hn : n ≠ 0 := by
    rintro rfl; simp at hyy
  have hint1 : Integrable (fun t : ℝ => t) ζ := hL2.integrable one_le_two
  have hint2 : Integrable (fun t : ℝ => t ^ 2) ζ := hL2.integrable_sq
  set s : ℝ := Real.sqrt n with hs
  have hs2 : s * s = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  let c : Fin n × Bool → EuclideanSpace ℝ (Fin n) := fun p =>
    (if p.2 then s else -s) • (EuclideanSpace.single p.1 (1 : ℝ) - y p.1 • y)
  let F : Fin n × Bool → ℝ → EuclideanSpace ℝ (Fin n) := fun p t => t • y + c p
  have hF : ∀ p, Measurable (F p) := fun p => by fun_prop
  have hcoord : ∀ p t i, F p t i = t * y i + (if p.2 then s else -s) *
      ((if p.1 = i then 1 else 0) - y p.1 * y i) := by
    intro p t i
    rcases p with ⟨k, _ | _⟩ <;> by_cases h : k = i
    all_goals first
      | (subst h; simp [F, c])
      | simp [F, c, h, Ne.symm h]
  have hcsum : ∀ i, ∑ p : Fin n × Bool, (if p.2 then s else -s) *
      ((if p.1 = i then 1 else 0) - y p.1 * y i) = 0 := by
    intro i
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, neg_mul, add_neg_cancel,
      Finset.sum_const_zero]
  have hcprod : ∀ i j, ∑ p : Fin n × Bool, (if p.2 then s else -s) *
      ((if p.1 = i then 1 else 0) - y p.1 * y i) * ((if p.2 then s else -s) *
      ((if p.1 = j then 1 else 0) - y p.1 * y j)) =
      2 * n * ((if i = j then 1 else 0) - y i * y j) := by
    intro i j
    rw [Fintype.sum_prod_type]
    have : ∀ k : Fin n, ∑ b : Bool, (if b then s else -s) *
        ((if k = i then 1 else 0) - y k * y i) * ((if b then s else -s) *
        ((if k = j then 1 else 0) - y k * y j)) =
        2 * n * (((if k = i then 1 else 0) - y k * y i) * ((if k = j then 1 else 0) - y k * y j)) := by
      intro k
      rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]
      rw [← hs2]; ring
    rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.mul_sum]
    congr 1
    have e : ∀ k : Fin n, ((if k = i then (1:ℝ) else 0) - y k * y i) *
        ((if k = j then 1 else 0) - y k * y j) =
        (if k = i then (if k = j then 1 else 0) else 0) - (if k = i then y k * y j else 0)
         - (if k = j then y k * y i else 0) + y k * y k * (y i * y j) := by
      intro k; split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hyy]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs with hij
    · subst hij; ring
    · ring
  set w : ENNReal := ((2 * n : ℕ) : ENNReal)⁻¹ with hw
  have hwtop : w ≠ ⊤ := by
    rw [hw, ENNReal.inv_ne_top]; exact_mod_cast (by omega : 2 * n ≠ 0)
  have hwr : w.toReal = (2 * n : ℝ)⁻¹ := by
    rw [hw, ENNReal.toReal_inv]; simp
  have hcard : (Finset.univ : Finset (Fin n × Bool)).card = 2 * n := by
    simp [Finset.card_univ, mul_comm]
  -- the measure
  refine ⟨∑ p, w • ζ.map (F p), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · constructor
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    simp_rw [Measure.map_apply (hF _) MeasurableSet.univ, Set.preimage_univ, measure_univ,
      mul_one]
    rw [Finset.sum_const, hcard, nsmul_eq_mul, hw]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : 2 * n ≠ 0)) (ENNReal.natCast_ne_top _)
  · intro i
    have hm : Measurable (fun R : EuclideanSpace ℝ (Fin n) => R i) := by fun_prop
    rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
    refine (lift_sum_aux ζ w hwtop F hF _ (by fun_prop) fun p => ?_).1
    simp_rw [hcoord]
    have := ((hint2.const_mul (y i ^ 2)).add (hint1.const_mul (2 * y i *
      ((if p.2 then s else -s) * ((if p.1 = i then 1 else 0) - y p.1 * y i))))).add
      (integrable_const (((if p.2 then s else -s) * ((if p.1 = i then 1 else 0) - y p.1 * y i)) ^ 2))
    exact this.congr (ae_of_all _ fun t => by simp only [Pi.add_apply]; ring)
  · intro i
    have hm : Measurable (fun R : EuclideanSpace ℝ (Fin n) => R i) := by fun_prop
    have hI : ∀ p, Integrable (fun t => F p t i) ζ := by
      intro p; simp_rw [hcoord]
      exact (hint1.mul_const _).add (integrable_const _)
    rw [(lift_sum_aux ζ w hwtop F hF _ hm hI).2]
    simp_rw [hcoord]
    have : ∀ p : Fin n × Bool, ∫ t, t * y i + (if p.2 then s else -s) *
        ((if p.1 = i then 1 else 0) - y p.1 * y i) ∂ζ = (if p.2 then s else -s) *
        ((if p.1 = i then 1 else 0) - y p.1 * y i) := by
      intro p
      rw [integral_add (hint1.mul_const _) (integrable_const _), integral_mul_const, hmean,
        integral_const]
      simp
    rw [Finset.sum_congr rfl fun p _ => this p, hcsum]
    simp
  · intro i j
    have hm : Measurable (fun R : EuclideanSpace ℝ (Fin n) => (R i - (0 : EuclideanSpace ℝ (Fin n)) i)
        * (R j - (0 : EuclideanSpace ℝ (Fin n)) j)) := by fun_prop
    have key : ∀ p : Fin n × Bool, ∀ a b : ℝ,
        Integrable (fun t : ℝ => (t * y i + a) * (t * y j + b)) ζ ∧
        ∫ t : ℝ, (t * y i + a) * (t * y j + b) ∂ζ = y i * y j + a * b := by
      intro p a b
      have e : (fun t : ℝ => (t * y i + a) * (t * y j + b)) =
          fun t => (y i * y j) * t ^ 2 + (y i * b + a * y j) * t + a * b := by
        funext t; ring
      rw [e]
      have h1 := hint2.const_mul (y i * y j)
      have h2 := hint1.const_mul (y i * b + a * y j)
      refine ⟨(h1.add h2).add (integrable_const _), ?_⟩
      beta_reduce
      rw [integral_add (f := fun t : ℝ => y i * y j * t ^ 2 + (y i * b + a * y j) * t)
        (g := fun _ => a * b) (h1.add h2) (integrable_const _), integral_add h1 h2,
        integral_const_mul, integral_const_mul, hvar, hmean, integral_const]
      simp
    have hI : ∀ p, Integrable (fun t => (F p t i - (0 : EuclideanSpace ℝ (Fin n)) i) *
        (F p t j - (0 : EuclideanSpace ℝ (Fin n)) j)) ζ := by
      intro p; simp_rw [hcoord]; simpa using (key p _ _).1
    rw [(lift_sum_aux ζ w hwtop F hF _ hm hI).2]
    simp_rw [hcoord]
    simp only [PiLp.zero_apply, sub_zero]
    rw [Finset.sum_congr rfl fun p _ => (key p _ _).2, Finset.sum_add_distrib, hcprod,
      Finset.sum_const, hcard, nsmul_eq_mul, hwr, Matrix.one_apply]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
    push_cast
    split_ifs <;> ring
  · ext A hA
    rw [Measure.map_apply (by fun_prop) hA, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    have hpre : ∀ p, (F p) ⁻¹' ((fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) ⁻¹' A) = A := by
      intro p
      ext t
      simp only [Set.mem_preimage, F, c, inner_add_right, inner_smul_right, hy, inner_sub_right,
        EuclideanSpace.inner_single_right]
      simp at *
    have hmA : MeasurableSet ((fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) ⁻¹' A) :=
      (by fun_prop : Measurable fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) hA
    have hq : ∀ p, ζ.map (F p) ((fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) ⁻¹' A) = ζ A := by
      intro p; rw [Measure.map_apply (hF p) hmA, hpre p]
    simp only [hq]
    rw [Finset.sum_const, hcard, nsmul_eq_mul, ← mul_assoc, hw,
      ENNReal.mul_inv_cancel (by exact_mod_cast (by omega : 2 * n ≠ 0)) (ENNReal.natCast_ne_top _),
      one_mul]


theorem aux_aip_selfadj {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (x Z : EuclideanSpace ℝ (Fin n)) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z⟫ = ⟪toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x, Z⟫ := by
  have hA : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) :=
    (CFC.sqrt_nonneg S).isSelfAdjoint.map _
  rw [← ContinuousLinearMap.adjoint_inner_left, hA.adjoint_eq]


theorem gp_affine_image_projection {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hq : 0 < x.ofLp ⬝ᵥ S *ᵥ x.ofLp)
    (Z : EuclideanSpace ℝ (Fin n)) :
    let y : EuclideanSpace ℝ (Fin n) :=
      (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x
    ⟪x, μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z⟫ =
      ⟪x, μ⟫ + (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (1 / 2 : ℝ) * ⟪y, Z⟫ := by
  intro y
  have h1 : (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (1 / 2 : ℝ) * (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hq]; norm_num
  simp only [y, inner_add_right, real_inner_smul_left, aux_aip_selfadj]
  rw [← mul_assoc, h1, one_mul]



set_option backward.isDefEq.respectTransparency false in
theorem aux_ndis_sqrt_inner {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) :
    ⟪toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x, toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x⟫
      = x.ofLp ⬝ᵥ S *ᵥ x.ofLp := by
  rw [← ContinuousLinearMap.adjoint_inner_right, IsSelfAdjoint.adjoint_eq,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    CFC.sqrt_mul_sqrt_self _ hS.nonneg, inner_toEuclideanCLM]
  exact (CFC.sqrt_nonneg S).isSelfAdjoint.map _


theorem gp_normalized {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hq : 0 < x.ofLp ⬝ᵥ S *ᵥ x.ofLp) :
    let y : EuclideanSpace ℝ (Fin n) :=
      (x.ofLp ⬝ᵥ S *ᵥ x.ofLp) ^ (-(1 / 2 : ℝ)) • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x
    ⟪y, y⟫ = 1 := by
  intro y
  simp only [y, inner_smul_left, inner_smul_right, aux_ndis_sqrt_inner x S hS]
  set q := x.ofLp ⬝ᵥ S *ᵥ x.ofLp with hqdef
  simp only [conj_trivial]
  rw [← mul_assoc, ← Real.rpow_add hq]
  norm_num
  rw [Real.rpow_neg_one]
  exact inv_mul_cancel₀ hq.ne'



theorem aux_pdeg_inner {n : ℕ} (x R : EuclideanSpace ℝ (Fin n)) :
    ⟪x, R⟫ = ∑ i, x i * R i := by
  simp [PiLp.inner_apply, mul_comm]


theorem gp_degenerate {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hq : x.ofLp ⬝ᵥ S *ᵥ x.ofLp = 0)
    (P : Measure (EuclideanSpace ℝ (Fin n))) (hP : P ∈ MeanCovClass μ S) :
    ∀ᵐ R ∂P, ⟪x, R⟫ = ⟪x, μ⟫ := by
  obtain ⟨hprob, hL2, _hmean, hcov⟩ := hP
  set g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i R => R i - μ i with hg
  have hgL2 : ∀ i, MemLp (g i) 2 P := fun i => (hL2 i).sub (memLp_const _)
  have hgg : ∀ i j, Integrable (fun R => g i R * g j R) P := fun i j =>
    (hgL2 i).integrable_mul (hgL2 j)
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun R => ∑ i, x i * g i R with hf
  have hfR : ∀ R, ⟪x, R⟫ - ⟪x, μ⟫ = f R := by
    intro R
    simp only [aux_pdeg_inner, hf, hg, ← Finset.sum_sub_distrib, mul_sub]
  have hff : ∀ R, f R * f R = ∑ i, ∑ j, (x i * x j) * (g i R * g j R) := by
    intro R
    simp only [hf, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : Integrable (fun R => f R * f R) P := by
    simp_rw [hff]
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact (hgg i j).const_mul _
  have hval : ∫ R, f R * f R ∂P = 0 := by
    simp_rw [hff]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hgg i j).const_mul _]
    simp_rw [integral_finsetSum _ fun j _ => (hgg _ j).const_mul _]
    simp_rw [integral_const_mul]
    have : ∀ i j, ∫ R, g i R * g j R ∂P = S i j := fun i j => hcov i j
    simp_rw [this]
    rw [← hq]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hae : (fun R => f R * f R) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun R => mul_self_nonneg (f R)) hint).1 hval
  filter_upwards [hae] with R hR
  have h0 : f R = 0 := mul_self_eq_zero.1 hR
  have := hfR R
  linarith




theorem gp_mapsTo {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) :
    Set.MapsTo (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
      (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) := by
  rintro P ⟨hP, hL, hmean, hcov⟩
  have hf : Continuous (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫) :=
    continuous_const.inner continuous_id
  have hfm : AEMeasurable (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫) P :=
    hf.measurable.aemeasurable
  have hfeq : (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫) = fun R => ∑ i, x i * R i := by
    ext R; simp [PiLp.inner_apply, mul_comm]
  have hint : ∀ i, Integrable (fun R : EuclideanSpace ℝ (Fin n) => R i) P :=
    fun i => (hL i).integrable one_le_two
  have hLc : ∀ i, MemLp (fun R : EuclideanSpace ℝ (Fin n) => R i - μ i) 2 P :=
    fun i => (hL i).sub (memLp_const _)
  have hij : ∀ i j, Integrable
      (fun R : EuclideanSpace ℝ (Fin n) => (R i - μ i) * (R j - μ j)) P :=
    fun i j => (hLc i).integrable_mul (hLc j)
  have hμ : ⟪x, μ⟫ = ∑ i, x i * μ i := by simp [PiLp.inner_apply, mul_comm]
  refine ⟨Measure.isProbabilityMeasure_map hfm, ?_, ?_, ?_⟩ <;> dsimp only
  · rw [memLp_map_measure_iff (g := fun r : ℝ => r) aestronglyMeasurable_id hfm]
    have : (fun r : ℝ => r) ∘ (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫)
        = fun R => ∑ i, x i * R i := by rw [← hfeq]; rfl
    rw [this]
    exact memLp_finsetSum _ (fun i _ => (hL i).const_mul (x i))
  · rw [integral_map (f := fun r : ℝ => r) hfm aestronglyMeasurable_id, hfeq, integral_finsetSum _
      (fun i _ => (hint i).const_mul (x i)), hμ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, hmean]
  · rw [integral_map (f := fun r : ℝ => (r - ⟪x, μ⟫) ^ 2) hfm (by fun_prop)]
    have hsq : (fun R : EuclideanSpace ℝ (Fin n) => (⟪x, R⟫ - ⟪x, μ⟫) ^ 2)
        = fun R => ∑ i, ∑ j, (x i * x j) * ((R i - μ i) * (R j - μ j)) := by
      ext R
      rw [show ⟪x, R⟫ = ∑ i, x i * R i from congrFun hfeq R, hμ, ← Finset.sum_sub_distrib, sq,
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      ring
    rw [hsq, integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hij i j).const_mul _))]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => (hij i j).const_mul _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul, hcov]
    ring



theorem aux_stdz_sq (v : ℝ) (hv : 0 < v) : (v ^ (-(1 / 2 : ℝ))) ^ 2 * v = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp


theorem gp_standardize (m v : ℝ) (hv : 0 < v) (ν : Measure ℝ) (hν : ν ∈ RobustMeanCov.Shared.MeanVarClass m v) :
    ν.map (fun r => v ^ (-(1 / 2 : ℝ)) * (r - m)) ∈ RobustMeanCov.Shared.MeanVarClass 0 1 := by
  obtain ⟨hP, hL, hmean, hvar⟩ := hν
  set c : ℝ := v ^ (-(1 / 2 : ℝ)) with hc
  have hmeas : Measurable (fun r : ℝ => c * (r - m)) := by fun_prop
  have hae : AEMeasurable (fun r : ℝ => c * (r - m)) ν := hmeas.aemeasurable
  have hint : Integrable (fun r : ℝ => r) ν := hL.integrable (by norm_num)
  have hL2 : MemLp (fun r : ℝ => c * (r - m)) 2 ν := (hL.sub (memLp_const m)).const_mul c
  refine ⟨Measure.isProbabilityMeasure_map hae, ?_, ?_, ?_⟩
  · rw [memLp_map_measure_iff (by fun_prop) hae]
    exact hL2
  · rw [integral_map hae (by fun_prop)]
    rw [integral_const_mul, integral_sub hint (integrable_const m), hmean]
    simp
  · rw [integral_map hae (by fun_prop)]
    simp only [sub_zero]
    have : (fun r : ℝ => (c * (r - m)) ^ 2) = fun r => c ^ 2 * (r - m) ^ 2 := by
      funext r; ring
    rw [this, integral_const_mul, hvar, hc]
    exact aux_stdz_sq v hv



theorem aux_affm_coord {n : ℕ} (μ : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ)
    (Z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (μ + toEuclideanCLM (𝕜 := ℝ) A Z) i = μ i + ∑ k, A i k * Z k := by
  simp [ofLp_toEuclideanCLM, mulVec, dotProduct]

theorem aux_affm_sq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (i j : Fin n) :
    ∑ k, CFC.sqrt S i k * CFC.sqrt S j k = S i j := by
  have h1 : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self _ hS.nonneg
  have h2 : IsSelfAdjoint (CFC.sqrt S) := (CFC.sqrt_nonneg S).isSelfAdjoint
  have h3 : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    have := h2.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  conv_rhs => rw [← h1]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  conv_rhs => rw [← h3]
  rfl


theorem gp_affine_mem {n : ℕ} (μ : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (Q : Measure (EuclideanSpace ℝ (Fin n)))
    (hQ : Q ∈ MeanCovClass (0 : EuclideanSpace ℝ (Fin n)) (1 : Matrix (Fin n) (Fin n) ℝ)) :
    Q.map (fun Z => μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z) ∈ MeanCovClass μ S := by
  obtain ⟨hprob, hL2, hmean, hcov⟩ := hQ
  set A := CFC.sqrt S with hA
  have hmeas : Measurable (fun Z : EuclideanSpace ℝ (Fin n) => μ + toEuclideanCLM (𝕜 := ℝ) A Z) := by
    fun_prop
  have hcoordm : ∀ i : Fin n, Measurable (fun R : EuclideanSpace ℝ (Fin n) => R i) := by
    intro i; fun_prop
  have hint : ∀ k, Integrable (fun Z : EuclideanSpace ℝ (Fin n) => Z k) Q :=
    fun k => (hL2 k).integrable one_le_two
  have hint2 : ∀ k l, Integrable (fun Z : EuclideanSpace ℝ (Fin n) => Z k * Z l) Q :=
    fun k l => (hL2 k).integrable_mul (hL2 l)
  refine ⟨Measure.isProbabilityMeasure_map hmeas.aemeasurable, ?_, ?_, ?_⟩
  · intro i
    rw [memLp_map_measure_iff (hcoordm i).aestronglyMeasurable hmeas.aemeasurable]
    have : (fun R : EuclideanSpace ℝ (Fin n) => R i) ∘
        (fun Z : EuclideanSpace ℝ (Fin n) => μ + toEuclideanCLM (𝕜 := ℝ) A Z) =
        fun Z => μ i + ∑ k, A i k * Z k := funext fun Z => aux_affm_coord μ A Z i
    rw [this]
    have hs : MemLp (fun Z : EuclideanSpace ℝ (Fin n) => ∑ k, A i k * Z k) 2 Q := by
      have := memLp_finsetSum' (p := 2) (μ := Q) (Finset.univ : Finset (Fin n))
        (f := fun k (Z : EuclideanSpace ℝ (Fin n)) => A i k * Z k) (fun k _ => (hL2 k).const_mul (A i k))
      convert this using 1
      funext Z; simp [Finset.sum_apply]
    exact (memLp_const (μ i)).add hs
  · intro i
    rw [integral_map hmeas.aemeasurable (hcoordm i).aestronglyMeasurable]
    simp_rw [aux_affm_coord μ A _ i]
    rw [integral_add (integrable_const _)
      (integrable_finsetSum _ fun k _ => (hint k).const_mul _), integral_const,
      integral_finsetSum _ fun k _ => (hint k).const_mul _]
    simp_rw [integral_const_mul, hmean]
    simp
  · intro i j
    have hg : Measurable (fun R : EuclideanSpace ℝ (Fin n) => (R i - μ i) * (R j - μ j)) := by
      fun_prop
    rw [integral_map hmeas.aemeasurable hg.aestronglyMeasurable]
    simp_rw [aux_affm_coord μ A _ i, aux_affm_coord μ A _ j, add_sub_cancel_left,
      Finset.sum_mul_sum]
    have hterm : ∀ k l, ∫ Z : EuclideanSpace ℝ (Fin n), A i k * Z k * (A j l * Z l) ∂Q =
        A i k * A j l * (1 : Matrix (Fin n) (Fin n) ℝ) k l := by
      intro k l
      have h := hcov k l
      simp only [PiLp.zero_apply, sub_zero] at h
      rw [← h, ← integral_const_mul]
      congr 1; funext Z; ring
    have hI : ∀ k l, Integrable
        (fun Z : EuclideanSpace ℝ (Fin n) => A i k * Z k * (A j l * Z l)) Q := by
      intro k l
      have := (hint2 k l).const_mul (A i k * A j l)
      convert this using 1
      funext Z; ring
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => hI k l)]
    have hsum : ∀ k, ∫ Z : EuclideanSpace ℝ (Fin n), ∑ l, A i k * Z k * (A j l * Z l) ∂Q =
        ∑ l, A i k * A j l * (1 : Matrix (Fin n) (Fin n) ℝ) k l := by
      intro k
      rw [integral_finsetSum _ fun l _ => hI k l]
      exact Finset.sum_congr rfl fun l _ => hterm k l
    rw [Finset.sum_congr rfl fun k _ => hsum k]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [hA]
    exact aux_affm_sq S hS i j



theorem gp_core {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hx : x ≠ 0) :
    Set.MapsTo (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
        (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) ∧
      Set.SurjOn (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
        (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) := by
  refine ⟨gp_mapsTo μ x S, ?_⟩
  intro ν hν
  set q := x.ofLp ⬝ᵥ S *ᵥ x.ofLp with hqdef
  have hq0 : 0 ≤ q := hS.dotProduct_mulVec_nonneg _
  have hAm : Measurable (fun Z : EuclideanSpace ℝ (Fin n) =>
      μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z) := by fun_prop
  have hxm : Measurable (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫) := by fun_prop
  rcases hq0.lt_or_eq with hq | hq
  · -- nondegenerate case
    set c : ℝ := q ^ (-(1 / 2 : ℝ)) with hc
    set ζ := ν.map (fun r => c * (r - ⟪x, μ⟫)) with hζdef
    have hζ : ζ ∈ RobustMeanCov.Shared.MeanVarClass 0 1 := gp_standardize _ q hq ν hν
    set y : EuclideanSpace ℝ (Fin n) := c • toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x with hy
    have hyy : ⟪y, y⟫ = 1 := gp_normalized x S hS hq
    obtain ⟨Q, hQ, hQmap⟩ := exists_isotropic_lift_core y hyy ζ hζ
    refine ⟨Q.map (fun Z => μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z),
      gp_affine_mem μ S hS Q hQ, ?_⟩
    show (Q.map _).map _ = ν
    rw [Measure.map_map hxm hAm]
    have hfun : (fun R : EuclideanSpace ℝ (Fin n) => ⟪x, R⟫) ∘
        (fun Z => μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z) =
        (fun t => ⟪x, μ⟫ + q ^ (1 / 2 : ℝ) * t) ∘ (fun Z => ⟪y, Z⟫) := by
      funext Z; exact gp_affine_image_projection μ x S hS hq Z
    have hym : Measurable (fun Z : EuclideanSpace ℝ (Fin n) => ⟪y, Z⟫) := by fun_prop
    rw [hfun, ← Measure.map_map (by fun_prop) hym, hQmap, hζdef,
      Measure.map_map (by fun_prop) (by fun_prop)]
    have hcq : q ^ (1 / 2 : ℝ) * c = 1 := by
      rw [hc, ← Real.rpow_add hq]; norm_num
    have : ((fun t => ⟪x, μ⟫ + q ^ (1 / 2 : ℝ) * t) ∘ fun r => c * (r - ⟪x, μ⟫)) = id := by
      funext r
      simp only [Function.comp_apply, id]
      rw [← mul_assoc, hcq]; ring
    rw [this, Measure.map_id]
  · -- degenerate case
    have hne : Nonempty (Fin n) := by
      by_contra h
      apply hx; ext i; exact (h ⟨i⟩).elim
    obtain ⟨i0⟩ := hne
    set y : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i0 1
    have hyy : ⟪y, y⟫ = 1 := by simp [y]
    have hG : ProbabilityTheory.gaussianReal 0 1 ∈ RobustMeanCov.Shared.MeanVarClass 0 1 := by
      refine ⟨inferInstance, ?_, ProbabilityTheory.integral_id_gaussianReal, ?_⟩
      · exact ProbabilityTheory.memLp_id_gaussianReal 2
      · have := ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := 1)
        rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable] at this
        simpa [ProbabilityTheory.integral_id_gaussianReal] using this
    obtain ⟨Q, hQ, -⟩ := exists_isotropic_lift_core y hyy _ hG
    have hP := gp_affine_mem μ S hS Q hQ
    refine ⟨_, hP, ?_⟩
    obtain ⟨hνp, hνL, hνm, hνv⟩ := hν
    have hPp : IsProbabilityMeasure (Q.map (fun Z => μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) Z)) :=
      hP.1
    show Measure.map _ _ = ν
    rw [Measure.map_congr (gp_degenerate μ x S hq.symm _ hP), Measure.map_const, measure_univ,
      one_smul]
    -- ν = dirac
    have hsq : Integrable (fun r : ℝ => (r - ⟪x, μ⟫) ^ 2) ν :=
      (hνL.sub (memLp_const _)).integrable_sq
    have hae : (fun r : ℝ => (r - ⟪x, μ⟫) ^ 2) =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun r => sq_nonneg _) hsq).1 (by rw [hνv, hq])
    have hae2 : (fun r : ℝ => r) =ᵐ[ν] (fun _ => ⟪x, μ⟫) := by
      filter_upwards [hae] with r hr
      have : r - ⟪x, μ⟫ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hr
      linarith
    have := Measure.map_congr (mβ := Real.measurableSpace) hae2
    rw [Measure.map_const, measure_univ, one_smul] at this
    rw [← this]
    exact Measure.map_id


end RobustMeanCov.Projection

open RobustMeanCov.Projection


theorem solution {n : ℕ} (μ x : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hx : x ≠ 0) :
    Set.MapsTo (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
        (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) ∧
      Set.SurjOn (fun P : Measure (EuclideanSpace ℝ (Fin n)) => P.map (fun R => ⟪x, R⟫))
        (MeanCovClass μ S) (RobustMeanCov.Shared.MeanVarClass ⟪x, μ⟫ (x.ofLp ⬝ᵥ S *ᵥ x.ofLp)) := by
  exact gp_core μ x S hS hx
