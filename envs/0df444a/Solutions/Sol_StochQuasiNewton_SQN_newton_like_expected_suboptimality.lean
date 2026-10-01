-- Prove2me | solution 1 for StochQuasiNewton.SQN.newton_like_expected_suboptimality
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:50:09.219002+00:00
-- url     : https://prove2.me/submissions/4818a1d5-e8e2-4b1d-b82b-9b04d6ae86b8

import Definitions.Def_StochQuasiNewton_SQN_NewtonLike
import Definitions.Def_StochQuasiNewton_SQN_FiniteSum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped RealInnerProductSpace
open StochQuasiNewton.SQN
open MeasureTheory Filter
namespace SQNProof

theorem quadratic_lower {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (lam : ℝ)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      lam * ‖v‖ ^ 2 < ⟪fderiv ℝ (gradient F) w v, v⟫)
    (w v : EuclideanSpace ℝ (Fin n)) :
    F w + ⟪gradient F w, v-w⟫ + lam / 2 * ‖v-w‖^2 ≤ F v := by
  let d := v-w
  let q : ℝ → ℝ := fun t => F (w+t • d) - lam/2*t^2*‖d‖^2
  let q' : ℝ → ℝ := fun t => ⟪gradient F (w+t • d), d⟫ - lam*t*‖d‖^2
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdG : Differentiable ℝ (gradient F) := by
    have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
      (hfder.differentiable (by norm_num))
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w+s • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add w
  have hq : ∀ t, HasDerivAt q (q' t) t := by
    intro t
    have hchain := (hdF (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [← inner_gradient_left] at hchain
    convert! hchain.sub (((hasDerivAt_id t).pow 2).const_mul (lam/2) |>.mul_const (‖d‖^2)) using 1 <;>
      dsimp only [q, q', id_eq] <;> ring
  have hq' : ∀ t, HasDerivAt q'
      (⟪fderiv ℝ (gradient F) (w+t • d) d, d⟫-lam*‖d‖^2) t := by
    intro t
    have hchain := (hdG (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    convert! (hchain.inner ℝ (hasDerivAt_const t d)).sub
      (((hasDerivAt_id t).const_mul lam).mul_const (‖d‖^2)) using 1 <;> simp [q']
  have hmono : Monotone q' := monotone_of_hasDerivAt_nonneg hq' (by
    intro t
    by_cases hd : d = 0
    · simp [hd]
    · exact sub_nonneg.mpr (hHess (w+t • d) d hd).le)
  have hconv : ConvexOn ℝ Set.univ q :=
    (show Monotone (deriv q) from fun x y hxy => by
      rw [(hq x).deriv, (hq y).deriv]; exact hmono hxy).monotoneOn (interior Set.univ) |>.convexOn_of_deriv
      convex_univ (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).differentiableAt.differentiableWithinAt)
  have hh := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0:ℝ)<1) (hq 0)
  simp [q, q', slope_def_field, d] at hh
  rw [inner_gradient_left, map_sub]
  linarith

theorem spectral_ratio {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ s, s ≠ 0 → a*‖s‖^2 < ⟪A s,s⟫ ∧ ⟪A s,s⟫ < b*‖s‖^2)
    (s : E) (hs : s ≠ 0) : a ≤ ‖A s‖^2/⟪A s,s⟫ ∧ ‖A s‖^2/⟪A s,s⟫ ≤ b := by
  let e := hA.eigenvalues (n := Module.finrank ℝ E) rfl
  let v := hA.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  have hev : ∀ i, A (v i) = e i • v i := hA.apply_eigenvectorBasis rfl
  have he : ∀ i, a < e i ∧ e i < b := by
    intro i
    have hvne : v i ≠ 0 := by
      intro hz
      have hh := v.norm_eq_one i
      rw [hz,norm_zero] at hh
      norm_num at hh
    have hh := hbounds (v i) hvne
    simpa [hev, real_inner_smul_left, real_inner_self_eq_norm_sq, v.norm_eq_one] using hh
  have hi : ∀ i, ⟪v i,A s⟫ = e i*⟪v i,s⟫ := by
    intro i
    rw [← hA, hev, real_inner_smul_left]
  have hn : ‖A s‖^2 = ∑ i, (e i*⟪v i,s⟫)^2 := by
    rw [← v.sum_sq_inner_right]
    simp_rw [hi]
  have hid : ⟪A s,s⟫ = ∑ i, e i*⟪v i,s⟫^2 := by
    rw [← v.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (v i) (A s), hi]
    ring
  have hd : 0 < ⟪A s,s⟫ := lt_trans (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hs))) (hbounds s hs).1
  constructor
  · apply (le_div_iff₀ hd).mpr
    rw [hn,hid,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hmul := mul_nonneg (show 0 ≤ e i from (ha.trans (he i).1).le) (sub_nonneg.mpr (he i).1.le)
    have hh := mul_nonneg hmul (sq_nonneg ⟪v i,s⟫)
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    rw [hn,hid,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hmul := mul_nonneg (show 0 ≤ e i from (ha.trans (he i).1).le) (sub_nonneg.mpr (he i).2.le)
    have hh := mul_nonneg hmul (sq_nonneg ⟪v i,s⟫)
    nlinarith


end SQNProof

namespace SQNProof
open scoped RealInnerProductSpace
open StochQuasiNewton.SQN
open MeasureTheory Filter

theorem quadratic_upper {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (Lam : ℝ)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      ⟪fderiv ℝ (gradient F) w v, v⟫ < Lam * ‖v‖ ^ 2)
    (w v : EuclideanSpace ℝ (Fin n)) :
    F v ≤ F w + ⟪gradient F w, v-w⟫ + Lam / 2 * ‖v-w‖^2 := by
  let d := v-w
  let q : ℝ → ℝ := fun t => Lam/2*t^2*‖d‖^2-F (w+t • d)
  let q' : ℝ → ℝ := fun t => Lam*t*‖d‖^2-⟪gradient F (w+t • d), d⟫
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdG : Differentiable ℝ (gradient F) := by
    have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.differentiable.comp
      (hfder.differentiable (by norm_num))
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w+s • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add w
  have hq : ∀ t, HasDerivAt q (q' t) t := by
    intro t
    have hchain := (hdF (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [← inner_gradient_left] at hchain
    convert! (((hasDerivAt_id t).pow 2).const_mul (Lam/2) |>.mul_const (‖d‖^2)).sub hchain using 1 <;>
      dsimp only [q, q', id_eq] <;> ring
  have hq' : ∀ t, HasDerivAt q'
      (Lam*‖d‖^2-⟪fderiv ℝ (gradient F) (w+t • d) d, d⟫) t := by
    intro t
    have hchain := (hdG (w+t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    convert! (((hasDerivAt_id t).const_mul Lam).mul_const (‖d‖^2)).sub
      (hchain.inner ℝ (hasDerivAt_const t d)) using 1 <;> simp [q']
  have hmono : Monotone q' := monotone_of_hasDerivAt_nonneg hq' (by
    intro t
    by_cases hd : d=0
    · simp [hd]
    · exact sub_nonneg.mpr (hHess (w+t • d) d hd).le)
  have hconv : ConvexOn ℝ Set.univ q :=
    (show Monotone (deriv q) from fun x y hxy => by
      rw [(hq x).deriv, (hq y).deriv]; exact hmono hxy).monotoneOn (interior Set.univ) |>.convexOn_of_deriv
      convex_univ (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).differentiableAt.differentiableWithinAt)
  have hh := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) (hq 0)
  simp [q,q',slope_def_field,d] at hh
  rw [inner_gradient_left,map_sub]
  linarith

theorem objective_lower {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) (lam : ℝ) (hlam : 0 < lam)
    (hHess : ∀ w v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      lam * ‖v‖ ^ 2 < ⟪fderiv ℝ (gradient F) w v, v⟫)
    (w v : EuclideanSpace ℝ (Fin n)) :
    F w - 1/(2*lam)*‖gradient F w‖^2 ≤ F v := by
  have hq := quadratic_lower F hF lam hHess w v
  have hs := sq_nonneg ‖gradient F w + lam • (v-w)‖
  rw [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hs
  have he : -(1/(2*lam)*‖gradient F w‖^2) ≤
      ⟪gradient F w,v-w⟫+lam/2*‖v-w‖^2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 2*lam by positivity)).mp
    field_simp
    nlinarith
  linarith

theorem matrix_bounds {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hl : (H-a • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
    (hu : (b • (1 : Matrix (Fin n) (Fin n) ℝ)-H).PosDef) :
    (H.toEuclideanLin.IsSymmetric) ∧
      (∀ v : EuclideanSpace ℝ (Fin n), a*‖v‖^2 ≤ ⟪H.toEuclideanLin v,v⟫) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), ‖H.toEuclideanLin v‖ ≤ b*‖v‖ := by
  have hId (c : ℝ) : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  have hH : H.IsHermitian := by
    simpa only [sub_add_cancel] using hl.isHermitian.add (hId a)
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hstrict (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
      a*‖v‖^2 < ⟪H.toEuclideanLin v,v⟫ ∧ ⟪H.toEuclideanLin v,v⟫ < b*‖v‖^2 := by
    have hv' : v.ofLp ≠ 0 := by simpa using hv
    have h1 := hl.dotProduct_mulVec_pos hv'
    have h2 := hu.dotProduct_mulVec_pos hv'
    have hn : dotProduct v.ofLp v.ofLp = ‖v‖^2 := by
      simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using real_inner_self_eq_norm_sq v
    have he : ⟪H.toEuclideanLin v,v⟫ = dotProduct v.ofLp (H.mulVec v.ofLp) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,Matrix.ofLp_toEuclideanLin_apply]
    simp only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,
      Matrix.one_mulVec,dotProduct_smul,smul_eq_mul,hn] at h1 h2
    rw [he]
    exact ⟨sub_pos.mp h1,sub_pos.mp h2⟩
  refine ⟨hsym,?_,?_⟩
  · intro v
    by_cases hv : v=0
    · simp [hv]
    · exact (hstrict v hv).1.le
  · intro v
    by_cases hv : v=0
    · simp [hv]
    have hr := (spectral_ratio H.toEuclideanLin hsym a b ha hstrict v hv).2
    have hp : 0 < ⟪H.toEuclideanLin v,v⟫ :=
      lt_trans (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hv))) (hstrict v hv).1
    have hs := (div_le_iff₀ hp).mp hr
    have hq := mul_le_mul_of_nonneg_left (hstrict v hv).2.le (ha.le.trans hab)
    have hb : 0 ≤ b*‖v‖ := mul_nonneg (ha.le.trans hab) (norm_nonneg _)
    nlinarith [norm_nonneg (H.toEuclideanLin v)]
end SQNProof

namespace SQNProof
open scoped RealInnerProductSpace
open StochQuasiNewton.SQN
open MeasureTheory Filter

theorem gradient_continuous {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : ContDiff ℝ 2 F) : Continuous (gradient F) := by
  have hfder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.continuous.comp hfder.continuous

theorem matrix_apply_measurable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (H : Ω → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i j, Measurable (fun ω => H ω i j))
    (v : Ω → EuclideanSpace ℝ (Fin n)) (hv : Measurable v) :
    Measurable (fun ω => Matrix.toEuclideanLin (H ω) (v ω)) := by
  simp only [Matrix.toEuclideanLin_apply,Matrix.mulVec,dotProduct]
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  simp only [Matrix.mulVec,dotProduct]
  fun_prop

theorem L2_inner {E Ω : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : Measure Ω} (f g : Ω → E) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => ⟪f ω,g ω⟫) P := by
  apply (hf.norm.integrable_mul hg.norm).mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact Eventually.of_forall fun ω => norm_inner_le_norm _ _

variable {n : ℕ} {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ}
  {F : EuclideanSpace ℝ (Fin n) → ℝ}
  {G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)} {γ : ℝ} {α : ℕ → ℝ}
  {μ₁ μ₂ : ℝ} {w1 : EuclideanSpace ℝ (Fin n)}
  {w : ℕ → Ω → EuclideanSpace ℝ (Fin n)} {ξ : ℕ → Ω → Ξ}
  {H : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ}
  (hrun : NewtonLikeIteration P ℱ F G γ α μ₁ μ₂ w1 w ξ H)

include hrun

theorem run_g_measurable (k : ℕ) : Measurable (fun ω => G (w k ω) (ξ k ω)) := by
  exact hrun.measurable_G.comp (((hrun.adapted_w k).mono (ℱ.le k) le_rfl).prodMk
    ((hrun.measurable_ξ k).mono (ℱ.le (k+1)) le_rfl))

theorem run_g_L2 (k : ℕ) (hk : 1 ≤ k) : MemLp (fun ω => G (w k ω) (ξ k ω)) 2 P :=
  (memLp_two_iff_integrable_sq_norm (run_g_measurable hrun k).aestronglyMeasurable).mpr (hrun.sq_integrable k hk)

theorem run_gradient_L2 (k : ℕ) (hk : 1 ≤ k) : MemLp (fun ω => gradient F (w k ω)) 2 P :=
  MemLp.ae_eq (hrun.unbiased k hk) ((run_g_L2 hrun k hk).condExp (m := ℱ k) (by norm_num))

theorem run_matrix_gradient_measurable (hF : ContDiff ℝ 2 F) (k : ℕ) :
    Measurable[ℱ k] (fun ω => Matrix.toEuclideanLin (H k ω) (gradient F (w k ω))) :=
  @matrix_apply_measurable n Ω (ℱ k) _ (hrun.adapted_H k) _ ((gradient_continuous F hF).measurable.comp (hrun.adapted_w k))

theorem run_matrix_gradient_L2 (hF : ContDiff ℝ 2 F) (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂)
    (k : ℕ) (hk : 1 ≤ k) :
    MemLp (fun ω => Matrix.toEuclideanLin (H k ω) (gradient F (w k ω))) 2 P := by
  apply (run_gradient_L2 hrun k hk).of_le_mul (c := μ₂)
    ((run_matrix_gradient_measurable hrun hF k).mono (ℱ.le k) le_rfl).aestronglyMeasurable
  exact Eventually.of_forall fun ω => (matrix_bounds (H k ω) μ₁ μ₂ hμ₁ hμ
    (hrun.eig_bounds k hk ω).1 (hrun.eig_bounds k hk ω).2).2.2 _

theorem run_descent_pointwise (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hLam : 0 < Lam)
    (hHess : ∀ z, StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) z))
    (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂) (k : ℕ) (hk : 1 ≤ k) (hα : 0 < α k) (ω : Ω) :
    F (w (k+1) ω) ≤ F (w k ω) - α k *
      ⟪Matrix.toEuclideanLin (H k ω) (gradient F (w k ω)),G (w k ω) (ξ k ω)⟫ +
        Lam/2*(α k*μ₂)^2*‖G (w k ω) (ξ k ω)‖^2 := by
  let g := G (w k ω) (ξ k ω)
  let A := Matrix.toEuclideanLin (H k ω)
  have hb := matrix_bounds (H k ω) μ₁ μ₂ hμ₁ hμ (hrun.eig_bounds k hk ω).1 (hrun.eig_bounds k hk ω).2
  have hd : w (k+1) ω-w k ω = -(α k • A g) := by rw [hrun.step k hk]; simp [A,g]
  have ht := quadratic_upper F hF Lam (fun z v hv => (hHess z v hv).2) (w k ω) (w (k+1) ω)
  rw [hd,inner_neg_right,real_inner_smul_right,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hα] at ht
  have hi : ⟪gradient F (w k ω),A g⟫ = ⟪A (gradient F (w k ω)),g⟫ := (hb.1 _ _).symm
  rw [hi] at ht
  have hn := hb.2.2 g
  have hns : ‖A g‖^2 ≤ μ₂^2*‖g‖^2 := by
    have hp := mul_nonneg (hμ₁.le.trans hμ) (norm_nonneg g)
    nlinarith [norm_nonneg (A g)]
  have hm := mul_le_mul_of_nonneg_left hns (show 0 ≤ Lam/2*(α k)^2 by positivity)
  dsimp [A,g] at ht hm ⊢
  nlinarith
end SQNProof

namespace SQNProof
open scoped RealInnerProductSpace
open StochQuasiNewton.SQN
open MeasureTheory Filter

theorem condExp_affine {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (f g q : Ω → ℝ)
    (hf : Integrable f P) (hg : Integrable g P) (hq : Integrable q P)
    (hfm : StronglyMeasurable[m] f) (a b : ℝ) :
    P[fun ω => f ω-a*g ω+b*q ω | m] =ᵐ[P]
      fun ω => f ω-a*(P[g | m] ω)+b*(P[q | m] ω) := by
  have hadd := condExp_add (hf.sub (hg.const_mul a)) (hq.const_mul b) m
  have hsub := condExp_sub hf (hg.const_mul a) m
  have hga := condExp_smul (μ := P) a g m
  have hqb := condExp_smul (μ := P) b q m
  have he := condExp_of_stronglyMeasurable hm hfm hf
  simp only [Pi.add_def,Pi.sub_def,Pi.smul_def,smul_eq_mul] at hadd hsub hga hqb
  filter_upwards [hadd,hsub,hga,hqb] with ω ha hs hg' hq'
  rw [ha,hs,hg',hq',he]

variable {n : ℕ} {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ}
  {F : EuclideanSpace ℝ (Fin n) → ℝ}
  {G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)} {γ : ℝ} {α : ℕ → ℝ}
  {μ₁ μ₂ : ℝ} {w1 : EuclideanSpace ℝ (Fin n)}
  {w : ℕ → Ω → EuclideanSpace ℝ (Fin n)} {ξ : ℕ → Ω → Ξ}
  {H : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ}
  (hrun : NewtonLikeIteration P ℱ F G γ α μ₁ μ₂ w1 w ξ H)

include hrun

theorem run_line_integrable (hF : ContDiff ℝ 2 F) (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂)
    (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => ⟪Matrix.toEuclideanLin (H k ω) (gradient F (w k ω)),G (w k ω) (ξ k ω)⟫) P :=
  L2_inner _ _ (run_matrix_gradient_L2 hrun hF hμ₁ hμ k hk) (run_g_L2 hrun k hk)

theorem run_value_integrable (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hHess : ∀ z, StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) z))
    (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂) (hα : ∀ k, 1 ≤ k → 0 < α k) :
    ∀ k, 1 ≤ k → Integrable (fun ω => F (w k ω)) P := by
  intro k hk
  induction k,hk using Nat.le_induction with
  | base => simpa only [hrun.init] using (integrable_const (F w1) : Integrable (fun _ : Ω => F w1) P)
  | succ k hk ih =>
    apply integrable_of_le_of_le
      (hF.continuous.measurable.comp ((hrun.adapted_w (k+1)).mono (ℱ.le (k+1)) le_rfl)).aestronglyMeasurable
      (Eventually.of_forall fun ω => objective_lower F hF lam hlam (fun z v hv => (hHess z v hv).1) 0 (w (k+1) ω))
      (Eventually.of_forall fun ω => run_descent_pointwise hrun hF lam Lam hLam hHess hμ₁ hμ k hk (hα k hk) ω)
      (integrable_const _)
    exact (ih.sub ((run_line_integrable hrun hF hμ₁ hμ k hk).const_mul (α k))).add
      ((hrun.sq_integrable k hk).const_mul (Lam/2*(α k*μ₂)^2))

theorem expected_descent (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hHess : ∀ z, StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) z))
    (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂) (hα : ∀ k, 1 ≤ k → 0 < α k)
    (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => F (w (k+1) ω)) P ∧
      P[fun ω => F (w (k+1) ω) | ℱ k] ≤ᵐ[P] fun ω =>
        F (w k ω)-α k*μ₁*‖gradient F (w k ω)‖^2+Lam/2*(α k*μ₂)^2*γ^2 := by
  have hi := run_value_integrable hrun hF lam Lam hlam hLam hHess hμ₁ hμ hα
  have hn := hi (k+1) (by omega)
  have hv := hi k hk
  have hl := run_line_integrable hrun hF hμ₁ hμ k hk
  have hq := hrun.sq_integrable k hk
  let l : Ω → ℝ := fun ω => ⟪Matrix.toEuclideanLin (H k ω) (gradient F (w k ω)),G (w k ω) (ξ k ω)⟫
  let q : Ω → ℝ := fun ω => ‖G (w k ω) (ξ k ω)‖^2
  let C := Lam/2*(α k*μ₂)^2
  have hmodel : Integrable (fun ω => F (w k ω)-α k*l ω+C*q ω) P :=
    (hv.sub (hl.const_mul (α k))).add (hq.const_mul C)
  have hm := condExp_mono (m := ℱ k) hn hmodel
    (Eventually.of_forall fun ω => run_descent_pointwise hrun hF lam Lam hLam hHess hμ₁ hμ k hk (hα k hk) ω)
  have ha := condExp_affine (ℱ.le k) (fun ω => F (w k ω)) l q hv hl hq
    (hF.continuous.measurable.comp (hrun.adapted_w k)).stronglyMeasurable (α k) C
  have hp : P[l | ℱ k] =ᵐ[P] fun ω =>
      ⟪Matrix.toEuclideanLin (H k ω) (gradient F (w k ω)),P[fun ω => G (w k ω) (ξ k ω) | ℱ k] ω⟫ :=
    condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ)
      (run_matrix_gradient_measurable hrun hF k).stronglyMeasurable hl
      ((run_g_L2 hrun k hk).integrable (by norm_num))
  refine ⟨hn,?_⟩
  filter_upwards [hm,ha,hp,hrun.unbiased k hk,hrun.second_moment k hk] with ω hmω haω hpω huω hqω
  rw [haω,hpω,huω] at hmω
  have hquad := (matrix_bounds (H k ω) μ₁ μ₂ hμ₁ hμ
    (hrun.eig_bounds k hk ω).1 (hrun.eig_bounds k hk ω).2).2.1 (gradient F (w k ω))
  have hlinear := mul_le_mul_of_nonneg_left hquad (hα k hk).le
  have hnoise := mul_le_mul_of_nonneg_left hqω (show 0 ≤ C by dsimp [C]; positivity)
  dsimp [q,C] at hmω hnoise
  nlinarith
end SQNProof

namespace SQNProof
open scoped RealInnerProductSpace
open StochQuasiNewton.SQN
open MeasureTheory Filter

variable {n : ℕ} {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℕ mΩ}
  {F : EuclideanSpace ℝ (Fin n) → ℝ}
  {G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)} {γ : ℝ} {α : ℕ → ℝ}
  {μ₁ μ₂ : ℝ} {w1 : EuclideanSpace ℝ (Fin n)}
  {w : ℕ → Ω → EuclideanSpace ℝ (Fin n)} {ξ : ℕ → Ω → Ξ}
  {H : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ}
  (hrun : NewtonLikeIteration P ℱ F G γ α μ₁ μ₂ w1 w ξ H)

include hrun

theorem suboptimality_recursion (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : 0 < Lam)
    (hHess : ∀ z, StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) z))
    (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂) (hα : ∀ k, 1 ≤ k → 0 < α k)
    (wstar : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => F (w k ω)) P ∧ Integrable (fun ω => F (w (k+1) ω)) P ∧
      (∫ ω, F (w (k+1) ω)-F wstar ∂P) ≤
        (1-2*α k*μ₁*lam)*(∫ ω, F (w k ω)-F wstar ∂P)+Lam/2*(α k*μ₂)^2*γ^2 := by
  have hi := run_value_integrable hrun hF lam Lam hlam hLam hHess hμ₁ hμ hα
  have hv := hi k hk
  obtain ⟨hn,he⟩ := expected_descent hrun hF lam Lam hlam hLam hHess hμ₁ hμ hα k hk
  have hg : Integrable (fun ω => ‖gradient F (w k ω)‖^2) P :=
    (memLp_two_iff_integrable_sq_norm (run_gradient_L2 hrun k hk).aestronglyMeasurable).mp (run_gradient_L2 hrun k hk)
  have hb : Integrable (fun ω => F (w k ω)-α k*μ₁*‖gradient F (w k ω)‖^2+Lam/2*(α k*μ₂)^2*γ^2) P :=
    (hv.sub (hg.const_mul (α k*μ₁))).add (integrable_const _)
  have hexp := integral_mono_ae (integrable_condExp (μ := P) (m := ℱ k) (f := fun ω => F (w (k+1) ω))) hb he
  rw [integral_condExp (ℱ.le k)] at hexp
  have hsub := integral_sub hv (hg.const_mul (α k*μ₁))
  have hadd := integral_add (hv.sub (hg.const_mul (α k*μ₁))) (integrable_const (Lam/2*(α k*μ₂)^2*γ^2) : Integrable (fun _ : Ω => _) P)
  simp only [Pi.sub_def,Pi.add_def] at hsub hadd
  rw [hadd,hsub,integral_const_mul,integral_const] at hexp
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hexp
  have hp (ω : Ω) : 2*lam*(F (w k ω)-F wstar) ≤ ‖gradient F (w k ω)‖^2 := by
    have hl := objective_lower F hF lam hlam (fun z v hv => (hHess z v hv).1) (w k ω) wstar
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*lam by positivity)
    field_simp at hm
    nlinarith
  have hgrad := integral_mono_ae ((hv.sub (integrable_const _)).const_mul (2*lam)) hg (Eventually.of_forall hp)
  rw [integral_const_mul] at hgrad
  have hgscale := mul_le_mul_of_nonneg_left hgrad (mul_nonneg (hα k hk).le hμ₁.le)
  simp only [Pi.sub_apply] at hgscale
  have hnsub := integral_sub hn (integrable_const (F wstar) : Integrable (fun _ : Ω => F wstar) P)
  have hvsub := integral_sub hv (integrable_const (F wstar) : Integrable (fun _ : Ω => F wstar) P)
  simp only [Pi.sub_def,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hnsub hvsub
  refine ⟨hv,hn,?_⟩
  rw [hnsub,hvsub]
  rw [hvsub] at hgscale
  nlinarith
end SQNProof

namespace SQNProof
open StochQuasiNewton.SQN
open MeasureTheory Filter

theorem scalar_rate (φ : ℕ → ℝ) (c B Q : ℝ) (hc : 1 < c) (hB : 0 ≤ B)
    (hQ : B ≤ (c-1)*Q) (hQ2 : 2*B ≤ Q) (hinit : φ 1 ≤ Q)
    (hφ : ∀ k, 1 ≤ k → 0 ≤ φ k)
    (hrec : ∀ k, 1 ≤ k → φ (k+1) ≤ (1-c/k)*φ k+B/(k:ℝ)^2) :
    ∀ k, 1 ≤ k → φ k ≤ Q/k := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ2
  intro k hk
  induction k,hk using Nat.le_induction with
  | base => simpa using hinit
  | succ k hk ih =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkp : (0 : ℝ) < k := by positivity
    have hksp : (0 : ℝ) < k+1 := by positivity
    have hkn : (k : ℝ) ≠ 0 := ne_of_gt hkp
    have hksn : (k : ℝ)+1 ≠ 0 := ne_of_gt hksp
    rw [Nat.cast_add,Nat.cast_one]
    by_cases hsign : 0 ≤ 1-c/k
    · have hmul := mul_le_mul_of_nonneg_left ih hsign
      have he : Q/((k:ℝ)+1)-((1-c/k)*(Q/k)+B/(k:ℝ)^2) =
          (((c-1)*Q-B)*((k:ℝ)+1)+Q)/((k:ℝ)^2*((k:ℝ)+1)) := by
        field_simp
        ring
      have hnum : 0 ≤ ((c-1)*Q-B)*((k:ℝ)+1)+Q := by positivity
      have hnon := div_nonneg hnum (show 0 ≤ (k:ℝ)^2*((k:ℝ)+1) by positivity)
      rw [← he] at hnon
      linarith [hrec k hk]
    · have hmul : (1-c/k)*φ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hsign) (hφ k hk)
      have hquot : B/(k:ℝ)^2 ≤ Q/((k:ℝ)+1) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hkp) hksp).mpr
        have hsq : (k:ℝ)+1 ≤ 2*(k:ℝ)^2 := by nlinarith
        have h1 := mul_le_mul_of_nonneg_left hsq hB
        have h2 := mul_le_mul_of_nonneg_right hQ2 (sq_nonneg (k:ℝ))
        nlinarith
      linarith [hrec k hk]
end SQNProof

open StochQuasiNewton.SQN
open MeasureTheory

/-- Theorem 3.2 (corrected constant): for the Newton-like iteration (3.14) on a `C²` objective
`F` with `λ I ≺ ∇²F(w) ≺ Λ I` (3.4) and minimizer `w*`, with `μ₁ I ≺ H_k ≺ μ₂ I`,
`0 < μ₁ ≤ μ₂` (3.15), step lengths `α^k = β/k` with `β > 1/(2 μ₁ λ)`, and the conditions of
`NewtonLikeIteration`, for every `k ≥ 1`, `F(w^k)` is integrable and
`E[F(w^k) − F(w*)] ≤ Q_c(β)/k`, where
`Q_c(β) = max { Λ μ₂² β² γ² / (2(2 μ₁ λ β − 1)), Λ μ₂² β² γ², F(w¹) − F(w*) }`. -/
theorem solution {n : ℕ} {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Ξ] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ 2 F) (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : 0 < Lam)
    (hHess : ∀ w : EuclideanSpace ℝ (Fin n),
      StrictLoewnerBounds lam Lam (fderiv ℝ (gradient F) w))
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : IsMinOn F Set.univ wstar)
    (G : EuclideanSpace ℝ (Fin n) → Ξ → EuclideanSpace ℝ (Fin n)) (γ μ₁ μ₂ β : ℝ)
    (hμ₁ : 0 < μ₁) (hμ : μ₁ ≤ μ₂) (hβ : 1 / (2 * μ₁ * lam) < β)
    (w1 : EuclideanSpace ℝ (Fin n)) (w : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ξ : ℕ → Ω → Ξ)
    (H : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hrun : NewtonLikeIteration P ℱ F G γ (fun k => β / k) μ₁ μ₂ w1 w ξ H) :
    ∀ k : ℕ, 1 ≤ k →
      Integrable (fun ω => F (w k ω)) P ∧
        ∫ ω, (F (w k ω) - F wstar) ∂P ≤
          rateConstant Lam lam μ₁ μ₂ β γ (F w1 - F wstar) / k := by
  have hd : 0 < 2*μ₁*lam := by positivity
  have hβpos : 0 < β := lt_trans (one_div_pos.mpr hd) hβ
  have hα (k : ℕ) (hk : 1 ≤ k) : 0 < β/(k:ℝ) := by
    have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    exact div_pos hβpos hkp
  let φ : ℕ → ℝ := fun k => ∫ ω, F (w k ω)-F wstar ∂P
  let c := 2*μ₁*lam*β
  let B := Lam/2*(β*μ₂)^2*γ^2
  let Q := rateConstant Lam lam μ₁ μ₂ β γ (F w1-F wstar)
  have hc : 1 < c := by
    have hh := (div_lt_iff₀ hd).mp hβ
    dsimp [c]
    nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ2 : 2*B ≤ Q := by
    have hh : Lam*μ₂^2*β^2*γ^2 ≤ Q := le_trans (le_max_right _ _) (le_max_left _ _)
    convert! hh using 1 <;> dsimp [B] <;> ring
  have hQ : B ≤ (c-1)*Q := by
    have hh : Lam*μ₂^2*β^2*γ^2/(2*(2*μ₁*lam*β-1)) ≤ Q :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have he : B/(c-1)=Lam*μ₂^2*β^2*γ^2/(2*(2*μ₁*lam*β-1)) := by
      dsimp [B,c]
      field_simp
    rw [← he] at hh
    have ht := (div_le_iff₀ (sub_pos.mpr hc)).mp hh
    simpa only [mul_comm] using ht
  have hinit : φ 1 ≤ Q := by
    dsimp [φ]
    simp only [hrun.init,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    exact le_max_right _ _
  have hφ : ∀ k, 1 ≤ k → 0 ≤ φ k := by
    intro k hk
    exact integral_nonneg fun ω => sub_nonneg.mpr (hwstar (Set.mem_univ _))
  have hrec : ∀ k, 1 ≤ k → φ (k+1) ≤ (1-c/(k:ℝ))*φ k+B/(k:ℝ)^2 := by
    intro k hk
    have hh := (SQNProof.suboptimality_recursion hrun hF lam Lam hlam hLam hHess hμ₁ hμ hα wstar k hk).2.2
    convert! hh using 1 <;> dsimp [φ,c,B] <;> simp only [div_pow,div_eq_mul_inv] <;> ring
  intro k hk
  exact ⟨SQNProof.run_value_integrable hrun hF lam Lam hlam hLam hHess hμ₁ hμ hα k hk,
    SQNProof.scalar_rate φ c B Q hc hB hQ hQ2 hinit hφ hrec k hk⟩


