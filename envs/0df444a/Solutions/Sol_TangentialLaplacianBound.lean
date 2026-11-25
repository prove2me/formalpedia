-- Prove2me | solution 1 for TangentialLaplacianBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:03:46.509456+00:00
-- url     : https://prove2.me/submissions/8ee1523c-304c-4588-909b-47ad099c9565

module
public import Definitions.Def_PHarmonicPoly_FrameHessian
public import Definitions.Def_PHarmonicPoly_MvPolyContDiff
public import Definitions.Def_PHarmonicPoly_MvPolyFDerivEuclidean
public import Definitions.Def_PHarmonicPoly_MvPolyGradientInner
public import Definitions.Def_PHarmonicPoly_AdaptedPlanarFrame
public import Definitions.Def_PHarmonicPoly_SecondDerivAtMaxNonpos
public import Definitions.Def_PHarmonicPoly_TangentialLaplacianBound
public import Theorems.Thm_AdaptedPlanarFrame
public import Theorems.Thm_FrameHessian
public import Theorems.Thm_GreatCircleSecondDeriv
public import Theorems.Thm_MvPolyContDiff
public import Theorems.Thm_MvPolyFDerivEuclidean
public import Theorems.Thm_MvPolyGradientInner
public import Theorems.Thm_MvPolyHessian
public import Theorems.Thm_SecondDerivAtMaxNonpos


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m)
    {P : MvPolynomial (Fin n) ℝ} (hhom : P.IsHomogeneous m)
    {e v₀ : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hv : ‖v₀‖ = 1)
    (hev : inner ℝ e v₀ = (0 : ℝ))
    (hv0max : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) →
      MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
          EuclideanSpace ℝ (Fin n)) i) P
        ≤ MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ :
          EuclideanSpace ℝ (Fin n)) i) P) :
    (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → inner ℝ e w = (0 : ℝ) →
        inner ℝ v₀ w = (0 : ℝ) →
        inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) =>
          MvPolynomial.eval (fun i => y i) P)
          (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) w = (0 : ℝ))
      ∧ (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → inner ℝ e w = (0 : ℝ) →
          inner ℝ v₀ w = (0 : ℝ) →
          iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => y i) P)
            (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![w, w]
          ≤ (m : ℝ) * MvPolynomial.eval (fun i =>
                (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ :
                  EuclideanSpace ℝ (Fin n)) i) P
            + deriv (fun s : ℝ => MvPolynomial.eval
                (fun i => (Real.cos s • e + Real.sin s • v₀ :
                  EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m)
              * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m)))
      ∧ Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) =>
            MvPolynomial.eval (fun i => y i) P)
          (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)
        ≤ (m : ℝ) * ((m : ℝ) + (n : ℝ) - 2) * MvPolynomial.eval (fun i =>
              (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ :
                EuclideanSpace ℝ (Fin n)) i) P
          + iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
              (fun i => (Real.cos s • e + Real.sin s • v₀ :
                EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m)
          + ((n : ℝ) - 2) * deriv (fun s : ℝ => MvPolynomial.eval
              (fun i => (Real.cos s • e + Real.sin s • v₀ :
                EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m)
            * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m)) := by
  classical
  have hnorm1 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 = 1 → ‖x‖ = 1 := by
    intro x hsq
    have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hf : (‖x‖ - 1) * (‖x‖ + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hf with h | h
    · linarith
    · linarith
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hthpos : 0 < Real.pi / m := div_pos Real.pi_pos hmpos
  have hthlt : Real.pi / m < Real.pi := by
    rw [div_lt_iff₀ hmpos]
    nlinarith [Real.pi_pos]
  have hspos : 0 < Real.sin (Real.pi / m) := Real.sin_pos_of_pos_of_lt_pi hthpos hthlt
  have hcssq : Real.cos (Real.pi / m) ^ 2 + Real.sin (Real.pi / m) ^ 2 = 1 := by
    rw [add_comm]
    exact Real.sin_sq_add_cos_sq _
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  have hvv : (inner ℝ v₀ v₀ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hve : (inner ℝ v₀ e : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hev
  have hchain : ∀ (C A B : EuclideanSpace ℝ (Fin n)) (σ : ℝ), HasDerivAt
      (fun r : ℝ => MvPolynomial.eval
        (fun i => (C + Real.cos r • A + Real.sin r • B : EuclideanSpace ℝ (Fin n)) i) P)
      (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (C + Real.cos σ • A + Real.sin σ • B))
        ((-Real.sin σ) • A + Real.cos σ • B) : ℝ) σ := by
    intro C A B σ
    have hcurve : HasDerivAt
        (fun r : ℝ => (C + Real.cos r • A + Real.sin r • B : EuclideanSpace ℝ (Fin n)))
        ((-Real.sin σ) • A + Real.cos σ • B) σ := by
      have hval : ((0 : EuclideanSpace ℝ (Fin n)) + (-Real.sin σ) • A + Real.cos σ • B)
          = ((-Real.sin σ) • A + Real.cos σ • B : EuclideanSpace ℝ (Fin n)) := by
        rw [zero_add]
      exact hval ▸ (((hasDerivAt_const σ (C : EuclideanSpace ℝ (Fin n))).add
        ((Real.hasDerivAt_cos σ).smul_const A)).add
        ((Real.hasDerivAt_sin σ).smul_const B))
    have h := HasFDerivAt.comp_hasDerivAt σ
      (MvPolyFDerivEuclidean P (C + Real.cos σ • A + Real.sin σ • B)) hcurve
    rw [(MvPolyGradientInner P (C + Real.cos σ • A + Real.sin σ • B)
      ((-Real.sin σ) • A + Real.cos σ • B)).2] at h
    exact h
  have hfr := FrameHessian (show 1 ≤ m by omega) hhom e v₀ (Real.pi / m)
  -- the per-direction key estimate
  have key : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → inner ℝ e w = (0 : ℝ) → inner ℝ v₀ w = (0 : ℝ) →
      (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) w = (0 : ℝ))
      ∧ iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![w, w]
        ≤ (m : ℝ) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P + deriv (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m)) := by
    intro w hw hew hvw
    have hwe : (inner ℝ w e : ℝ) = 0 := by
      rw [real_inner_comm]
      exact hew
    have hwv : (inner ℝ w v₀ : ℝ) = 0 := by
      rw [real_inner_comm]
      exact hvw
    have hww : (inner ℝ w w : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hw]
      norm_num
    have heta0 : (Real.cos (Real.pi / m) • e + Real.cos (0:ℝ) • (Real.sin (Real.pi / m) • v₀) + Real.sin (0:ℝ) • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) = (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) := by
      simp
    have hA : (Real.cos (0 : ℝ) • (Real.sin (Real.pi / m) • v₀) + Real.sin (0 : ℝ) • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n))
        = Real.sin (Real.pi / m) • v₀ := by
      simp
    have hB : ((-Real.sin (0 : ℝ)) • (Real.sin (Real.pi / m) • v₀) + Real.cos (0 : ℝ) • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n))
        = Real.sin (Real.pi / m) • w := by
      simp
    have hmaxh : ∀ σ : ℝ, MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P
        ≤ MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos (0:ℝ) • (Real.sin (Real.pi / m) • v₀) + Real.sin (0:ℝ) • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P := by
      intro σ
      have hvs : ‖(Real.cos σ • v₀ + Real.sin σ • w : EuclideanSpace ℝ (Fin n))‖ = 1 := by
        have hsq : ‖(Real.cos σ • v₀ + Real.sin σ • w : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_add_left, inner_add_right, real_inner_smul_left,
            real_inner_smul_right, hvv, hww, hvw, hwv]
          nlinarith [Real.sin_sq_add_cos_sq σ]
        exact hnorm1 _ hsq
      have hevs : inner ℝ e (Real.cos σ • v₀ + Real.sin σ • w : EuclideanSpace ℝ (Fin n)) = (0 : ℝ) := by
        rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hev, hew]
        ring
      have h := hv0max _ hvs hevs
      rw [heta0]
      have hre : (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) = (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • (Real.cos σ • v₀ + Real.sin σ • w) : EuclideanSpace ℝ (Fin n)) := by
        module
      rw [hre]
      exact h
    have hd1 := hchain (Real.cos (Real.pi / m) • e) (Real.sin (Real.pi / m) • v₀) (Real.sin (Real.pi / m) • w) 0
    rw [heta0, hB] at hd1
    have hlm : IsLocalMax (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P) 0 := Filter.Eventually.of_forall hmaxh
    have hzero := hlm.hasDerivAt_eq_zero hd1
    rw [real_inner_smul_right] at hzero
    have hgw : (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) w : ℝ) = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (ne_of_gt hspos)
      · exact h
    refine ⟨hgw, ?_⟩
    have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P) := by
      have hcurveC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun σ : ℝ => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n))) :=
        (contDiff_const.add (Real.contDiff_cos.smul contDiff_const)).add
          (Real.contDiff_sin.smul contDiff_const)
      exact (MvPolyContDiff P _).comp hcurveC
    have hdiffh : Differentiable ℝ (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P) := (contDiff_infty_iff_deriv.mp hsmooth).1
    have hdiffdh : Differentiable ℝ (deriv (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P)) :=
      (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsmooth).2).1
    have hiter : iteratedDeriv 2 (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P) 0 = deriv (deriv (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P)) 0 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hDD : HasDerivAt (deriv (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P)) (iteratedDeriv 2 (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P) 0) 0 := by
      rw [hiter]
      exact (hdiffdh 0).hasDerivAt
    have hsd := SecondDerivAtMaxNonpos (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P) (iteratedDeriv 2 (fun σ : ℝ => MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.cos σ • (Real.sin (Real.pi / m) • v₀) + Real.sin σ • (Real.sin (Real.pi / m) • w) : EuclideanSpace ℝ (Fin n)) i) P) 0) hdiffh hmaxh hDD
    have hgcsd := GreatCircleSecondDeriv P (Real.cos (Real.pi / m) • e) (Real.sin (Real.pi / m) • v₀) (Real.sin (Real.pi / m) • w) 0
    rw [heta0, hB, hA] at hgcsd
    have hhess : iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![Real.sin (Real.pi / m) • w, Real.sin (Real.pi / m) • w]
        = Real.sin (Real.pi / m) ^ 2 * iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![w, w] := by
      rw [MvPolyHessian P _ _ _, MvPolyHessian P _ _ _, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hc : ∀ z : Fin n, ((Real.sin (Real.pi / m) • w : EuclideanSpace ℝ (Fin n)) z) = Real.sin (Real.pi / m) * w z := fun z => rfl
      rw [hc, hc]
      ring
    have hgv : (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀)) v₀ : ℝ)
        = Real.sin (Real.pi / m) * (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀))
            (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) : ℝ)
          + Real.cos (Real.pi / m) * (inner ℝ (gradient (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀))
            ((-Real.sin (Real.pi / m) • e + Real.cos (Real.pi / m) • v₀) : EuclideanSpace ℝ (Fin n)) : ℝ) := by
      rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
      congr 1
      match_scalars
      all_goals first
        | ring1
        | exact (Real.sin_sq_add_cos_sq _).symm
        | linarith [Real.sin_sq_add_cos_sq (Real.pi * (m : ℝ)⁻¹)]
    rw [hhess, real_inner_smul_right, hgv, hfr.1, hfr.2.1] at hgcsd
    rw [hgcsd] at hsd
    have hs2 : (0 : ℝ) < Real.sin (Real.pi / m) ^ 2 := by positivity
    refine le_of_mul_le_mul_left ?_ hs2
    have hexp : Real.sin (Real.pi / m) ^ 2 * ((m : ℝ) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P + deriv (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m)))
        = Real.sin (Real.pi / m) * (Real.sin (Real.pi / m) * ((m : ℝ) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P) + Real.cos (Real.pi / m) * deriv (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m)) := by
      field_simp
    rw [hexp]
    linarith [hsd]
  refine ⟨fun w h1 h2 h3 => (key w h1 h2 h3).1, fun w h1 h2 h3 => (key w h1 h2 h3).2, ?_⟩
  -- the adapted orthonormal frame, from `AdaptedPlanarFrame`
  obtain ⟨i0, i1, b, hi01, hb0, hb1, hperp0⟩ :=
    AdaptedPlanarFrame (show 2 ≤ n by omega) he hv hev (Real.pi / m)
  -- each remaining frame direction is admissible
  have hrest : ∀ i ∈ (Finset.univ.erase i0).erase i1,
      iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![b i, b i]
        ≤ (m : ℝ) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P + deriv (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m)) := by
    intro i hi
    have hne1 : i ≠ i1 := (Finset.mem_erase.mp hi).1
    have hne0 : i ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hbn : ‖b i‖ = 1 := b.orthonormal.1 i
    obtain ⟨hei, hvi⟩ := hperp0 i hne0 hne1
    exact (key (b i) hbn hei hvi).2
  -- cardinality of the remaining index set
  have hcard : ((Finset.univ.erase i0).erase i1).card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hi01, Finset.mem_univ i1⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
    omega
  have hcast : (((n - 2 : ℕ)) : ℝ) = (n : ℝ) - 2 := by
    have h : 2 ≤ n := by omega
    push_cast [Nat.cast_sub h]
    ring
  have hsum_le : ∑ i ∈ (Finset.univ.erase i0).erase i1,
      iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => y i) P) (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀) ![b i, b i]
      ≤ ((n : ℝ) - 2) * ((m : ℝ) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P + deriv (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m))) := by
    have h := Finset.sum_le_card_nsmul _ _ _ hrest
    rw [hcard, nsmul_eq_mul, hcast] at h
    exact h
  -- split the frame sum
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only []
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hi01, Finset.mem_univ i1⟩),
    hb0, hb1, hfr.2.2.1, hfr.2.2.2.2]
  have hring : (m : ℝ) * ((m : ℝ) - 1) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P
      + ((iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m) + (m : ℝ) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P)
        + ((n : ℝ) - 2) * ((m : ℝ) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P + deriv (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m))))
      = (m : ℝ) * ((m : ℝ) + (n : ℝ) - 2) * MvPolynomial.eval (fun i => (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v₀ : EuclideanSpace ℝ (Fin n)) i) P + iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m)
        + ((n : ℝ) - 2) * deriv (fun s : ℝ => MvPolynomial.eval (fun i => (Real.cos s • e + Real.sin s • v₀ : EuclideanSpace ℝ (Fin n)) i) P) (Real.pi / m) * (Real.cos (Real.pi / m) / Real.sin (Real.pi / m)) := by
    ring
  linarith [hsum_le, hring]
