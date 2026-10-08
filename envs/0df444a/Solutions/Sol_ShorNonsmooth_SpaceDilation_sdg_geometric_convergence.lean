-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.sdg_geometric_convergence
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T19:05:11.793977+00:00
-- url     : https://prove2.me/submissions/dc5634c5-d63c-4554-a4b1-07415306e49c

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

set_option autoImplicit false

/- Complete checked body: DilationCore -/
section

noncomputable section
open ShorNonsmooth.SpaceDilation
open scoped RealInnerProductSpace
namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}

theorem dilation_apply (a : ℝ) (ξ u : EuclideanSpace ℝ (Fin n)) :
    dilation a ξ u = u + ((a - 1) * inner ℝ ξ u) • ξ := by
  simp only [dilation, add_apply, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  module

theorem inner_dilation (a : ℝ) {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ‖ξ‖ = 1)
    (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ξ (dilation a ξ u) = a * inner ℝ ξ u := by
  rw [dilation_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hξ]
  ring

theorem dilation_comp (a b : ℝ) {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ‖ξ‖ = 1) :
    (dilation a ξ).comp (dilation b ξ) = dilation (a * b) ξ := by
  apply ContinuousLinearMap.ext
  intro u
  change dilation a ξ (dilation b ξ u) = dilation (a * b) ξ u
  calc
    dilation a ξ (dilation b ξ u) =
        (u + ((b - 1) * inner ℝ ξ u) • ξ) +
          ((a - 1) * (b * inner ℝ ξ u)) • ξ := by
      rw [dilation_apply, inner_dilation b hξ, dilation_apply]
    _ = dilation (a * b) ξ u := by
      rw [dilation_apply]
      module

theorem dilation_one (ξ : EuclideanSpace ℝ (Fin n)) :
    dilation 1 ξ = ContinuousLinearMap.id ℝ _ := by
  ext u
  simp [dilation_apply]

theorem dilation_inverse (a : ℝ) (ha : a ≠ 0) {ξ : EuclideanSpace ℝ (Fin n)}
    (hξ : ‖ξ‖ = 1) :
    (dilation (1 / a) ξ).comp (dilation a ξ) = ContinuousLinearMap.id ℝ _ ∧
      (dilation a ξ).comp (dilation (1 / a) ξ) = ContinuousLinearMap.id ℝ _ := by
  simp [dilation_comp _ _ hξ, ha, dilation_one]

theorem dilation_norm_sq (a : ℝ) {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ‖ξ‖ = 1)
    (u : EuclideanSpace ℝ (Fin n)) :
    ‖dilation a ξ u‖ ^ 2 = ‖u‖ ^ 2 + (a ^ 2 - 1) * (inner ℝ ξ u) ^ 2 := by
  rw [dilation_apply, norm_add_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hξ,
    mul_one]
  rw [real_inner_comm u ξ]
  ring

theorem dilation_contract {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ‖ξ‖ = 1) (u : EuclideanSpace ℝ (Fin n)) :
    ‖dilation a ξ u‖ ≤ ‖u‖ := by
  have he := dilation_norm_sq a hξ u
  have ht : (a ^ 2 - 1) * (inner ℝ ξ u) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)
  nlinarith [norm_nonneg u, norm_nonneg (dilation a ξ u)]

theorem dilation_expand {a : ℝ} (ha : 1 ≤ a)
    {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ‖ξ‖ = 1) (u : EuclideanSpace ℝ (Fin n)) :
    ‖u‖ ≤ ‖dilation a ξ u‖ := by
  have he := dilation_norm_sq a hξ u
  have ht : 0 ≤ (a ^ 2 - 1) * (inner ℝ ξ u) ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  nlinarith [norm_nonneg u, norm_nonneg (dilation a ξ u)]

theorem normalized_norm {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) :
    ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

end ShorNonsmooth.SpaceDilationProof
end
end

/- Complete checked body: SpectralNorm -/
section

noncomputable section
open scoped RealInnerProductSpace
namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}

theorem det_sq_le_opNorm_pow (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    A.toLinearMap.det ^ 2 ≤ (‖A‖ ^ 2) ^ n := by
  let T := A.adjoint.comp A
  have hs : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (A.adjoint (A x)) y = inner ℝ x (A.adjoint (A y))
    rw [A.adjoint_inner_left, A.adjoint_inner_right]
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n :=
    finrank_euclideanSpace_fin
  let b := hs.eigenvectorBasis hn
  let ev := hs.eigenvalues hn
  have he (i : Fin n) : ev i = ‖A (b i)‖ ^ 2 := by
    have h := A.apply_norm_sq_eq_inner_adjoint_right (b i)
    have hi := hs.apply_eigenvectorBasis hn i
    change T (b i) = ev i • b i at hi
    change ‖A (b i)‖ ^ 2 = inner ℝ (b i) (T (b i)) at h
    rw [hi, inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one i] at h
    nlinarith
  have hnon (i : Fin n) : 0 ≤ ev i := by rw [he]; positivity
  have hle (i : Fin n) : ev i ≤ ‖A‖ ^ 2 := by
    rw [he]
    have h := A.le_opNorm (b i)
    rw [b.orthonormal.norm_eq_one i, mul_one] at h
    nlinarith [norm_nonneg (A (b i)), norm_nonneg A]
  have hp : (∏ i : Fin n, ev i) ≤ (‖A‖ ^ 2) ^ n := by
    calc
      (∏ i : Fin n, ev i) ≤ ∏ _i : Fin n, ‖A‖ ^ 2 :=
        Finset.prod_le_prod (fun i _ => hnon i) (fun i _ => hle i)
      _ = (‖A‖ ^ 2) ^ n := by simp
  have hd : A.toLinearMap.det ^ 2 = T.toLinearMap.det := by
    simpa [ContinuousLinearMap.det, LinearMap.normDet_eq_norm_det, Real.norm_eq_abs,
      sq_abs, T] using A.normDet_sq
  rw [hd, hs.det_eq_prod_eigenvalues hn]
  exact hp

end ShorNonsmooth.SpaceDilationProof
end
end

/- Complete checked body: DilationDeterminant -/
section

noncomputable section
open ShorNonsmooth.SpaceDilation
open scoped RealInnerProductSpace
namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}

theorem dilation_det (a : ℝ) {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ‖ξ‖ = 1) :
    (dilation a ξ).toLinearMap.det = a := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hm : LinearMap.toMatrix b.toBasis b.toBasis (dilation a ξ).toLinearMap =
      1 + Matrix.replicateCol Unit (fun i => (a - 1) * ξ i) *
        Matrix.replicateRow Unit (fun i => ξ i) := by
    ext i j
    simp [LinearMap.toMatrix_apply, b, dilation_apply, EuclideanSpace.inner_single_right,
      Matrix.mul_apply, Matrix.one_apply, PiLp.single_apply, mul_assoc, mul_comm, mul_left_comm]
  rw [← LinearMap.det_toMatrix b.toBasis, hm,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hsum : ∑ i : Fin n, (ξ i) ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hξ]
    norm_num
  change 1 + ∑ i : Fin n, ξ i * ((a - 1) * ξ i) = a
  have he : (∑ i : Fin n, ξ i * ((a - 1) * ξ i)) = (a - 1) * ∑ i : Fin n, (ξ i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hsum]
  ring

end ShorNonsmooth.SpaceDilationProof
end
end

/- Complete checked body: DilationGrowth -/
section

noncomputable section
open ShorNonsmooth.SpaceDilation
open scoped RealInnerProductSpace
namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}

theorem dilation_comp_norm_sq_le (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {a : ℝ} (ha : 1 ≤ a) {ξ : EuclideanSpace ℝ (Fin n)} (hξ : ‖ξ‖ = 1) :
    ‖(dilation a ξ).comp A‖ ^ 2 ≤ ‖A‖ ^ 2 + (a ^ 2 - 1) * ‖A.adjoint ξ‖ ^ 2 := by
  let C := ‖A‖ ^ 2 + (a ^ 2 - 1) * ‖A.adjoint ξ‖ ^ 2
  have ha2 : 0 ≤ a ^ 2 - 1 := by nlinarith
  have hC : 0 ≤ C := add_nonneg (sq_nonneg _) (mul_nonneg ha2 (sq_nonneg _))
  have hb : ‖(dilation a ξ).comp A‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro u hu
    have hA : ‖A u‖ ≤ ‖A‖ := by simpa [hu] using A.le_opNorm u
    have hi : |inner ℝ ξ (A u)| ≤ ‖A.adjoint ξ‖ := by
      rw [← A.adjoint_inner_left]
      simpa [hu] using abs_real_inner_le_norm (A.adjoint ξ) u
    have hi2 : (inner ℝ ξ (A u)) ^ 2 ≤ ‖A.adjoint ξ‖ ^ 2 := by
      nlinarith [sq_abs (inner ℝ ξ (A u)), abs_nonneg (inner ℝ ξ (A u)),
        norm_nonneg (A.adjoint ξ)]
    have hmul := mul_le_mul_of_nonneg_left hi2 ha2
    have he := dilation_norm_sq a hξ (A u)
    change ‖dilation a ξ (A u)‖ ≤ Real.sqrt C
    have hc2 := Real.sq_sqrt hC
    dsimp only [C] at hc2
    nlinarith [norm_nonneg (A u), norm_nonneg A,
      norm_nonneg (dilation a ξ (A u)), Real.sqrt_nonneg C]
  have hc2 := Real.sq_sqrt hC
  change ‖(dilation a ξ).comp A‖ ^ 2 ≤ C
  nlinarith [norm_nonneg ((dilation a ξ).comp A), Real.sqrt_nonneg C]

end ShorNonsmooth.SpaceDilationProof
end
end

/- Complete checked body: RunAlgebra -/
section

noncomputable section
open ShorNonsmooth.SpaceDilation
open scoped RealInnerProductSpace
namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem inverse_adjoint_apply (A B : E →L[ℝ] E)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ E) (v : E) :
    A.adjoint (B.adjoint v) = v := by
  have ht := congrArg ContinuousLinearMap.adjoint hBA
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at ht
  exact congrArg (fun T : E →L[ℝ] E => T v) ht

theorem inverse_adjoint_ne_zero (A B : E →L[ℝ] E)
    (hBA : B.comp A = ContinuousLinearMap.id ℝ E) {v : E} (hv : v ≠ 0) :
    B.adjoint v ≠ 0 := by
  intro hz
  have ht := inverse_adjoint_apply A B hBA v
  rw [hz, map_zero] at ht
  exact hv ht.symm

theorem step_inverse_contract (g : E → E) (h : ℕ → E → E → ℝ)
    {a : ℝ} (ha : 1 ≤ a) (k : ℕ) (s : SDGState n)
    (hAB : s.A.comp s.B = ContinuousLinearMap.id ℝ E)
    (hBA : s.B.comp s.A = ContinuousLinearMap.id ℝ E)
    (hB : ∀ u, ‖s.B u‖ ≤ ‖u‖) :
    let s' := sdgStep g h (fun _ => a) k s
    s'.A.comp s'.B = ContinuousLinearMap.id ℝ E ∧
      s'.B.comp s'.A = ContinuousLinearMap.id ℝ E ∧
      ∀ u, ‖s'.B u‖ ≤ ‖u‖ := by
  by_cases hg : g s.x = 0
  · simpa [sdgStep, hg] using And.intro hAB (And.intro hBA hB)
  · have hgt := inverse_adjoint_ne_zero s.A s.B hBA hg
    let ξ := ‖s.B.adjoint (g s.x)‖⁻¹ • s.B.adjoint (g s.x)
    have hξ : ‖ξ‖ = 1 := normalized_norm hgt
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
    have hi := dilation_inverse a (ne_of_gt ha0) hξ
    have hab (u : E) : s.A (s.B u) = u := congrArg (fun T : E →L[ℝ] E => T u) hAB
    have hba (u : E) : s.B (s.A u) = u := congrArg (fun T : E →L[ℝ] E => T u) hBA
    dsimp only
    rw [sdgStep, if_neg hg]
    refine ⟨?_, ?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro u
      change dilation a ξ (s.A (s.B (dilation (1 / a) ξ u))) = u
      rw [hab]
      exact congrArg (fun T : E →L[ℝ] E => T u) hi.2
    · apply ContinuousLinearMap.ext
      intro u
      change s.B (dilation (1 / a) ξ (dilation a ξ (s.A u))) = u
      have hr := congrArg (fun T : E →L[ℝ] E => T (s.A u)) hi.1
      change dilation (1 / a) ξ (dilation a ξ (s.A u)) = s.A u at hr
      rw [hr, hba]
    · intro u
      change ‖s.B (dilation (1 / a) ξ u)‖ ≤ ‖u‖
      exact (hB _).trans (dilation_contract (by positivity) ((div_le_one₀ ha0).mpr ha) hξ u)

theorem run_inverse_contract (g : E → E) (h : ℕ → E → E → ℝ)
    (x₀ : E) {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    let s := sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k
    s.A.comp s.B = ContinuousLinearMap.id ℝ E ∧
      s.B.comp s.A = ContinuousLinearMap.id ℝ E ∧ ∀ u, ‖s.B u‖ ≤ ‖u‖ := by
  induction k with
  | zero => simp [sdg]
  | succ k ih => exact step_inverse_contract g h ha k _ ih.1 ih.2.1 ih.2.2

theorem run_B_norm_le (g : E → E) (h : ℕ → E → E → ℝ)
    (x₀ : E) {a : ℝ} (ha : 1 ≤ a) (k : ℕ) :
    ‖(sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k).B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa using (run_inverse_contract g h x₀ ha k).2.2 u

theorem run_gTilde_ne_zero (g : E → E) (h : ℕ → E → E → ℝ)
    (x₀ : E) {a : ℝ} (ha : 1 ≤ a) (k : ℕ)
    (hg : g (sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k).x ≠ 0) :
    gTilde g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k ≠ 0 :=
  inverse_adjoint_ne_zero _ _ (run_inverse_contract g h x₀ ha k).2.1 hg

theorem run_det (g : E → E) (h : ℕ → E → E → ℝ)
    (x₀ : E) {a : ℝ} (ha : 1 ≤ a) (k : ℕ)
    (hg : ∀ i < k, g (sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) i).x ≠ 0) :
    (sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k).A.toLinearMap.det = a ^ k := by
  induction k with
  | zero => simp [sdg]
  | succ k ih =>
    have hk := hg k (Nat.lt_succ_self k)
    have hgt := run_gTilde_ne_zero g h x₀ ha k hk
    dsimp only [gTilde] at hgt
    have hind := ih (fun i hi => hg i (Nat.lt_trans hi (Nat.lt_succ_self k)))
    change (sdgStep g h (fun _ => a) k
      (sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k)).A.toLinearMap.det = _
    rw [sdgStep, if_neg hk]
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      dilation_det a (normalized_norm hgt), hind, pow_succ']

theorem run_norm_growth (g : E → E) (h : ℕ → E → E → ℝ)
    (x₀ : E) {a : ℝ} (ha : 1 ≤ a) (k : ℕ)
    (hg : g (sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k).x ≠ 0) :
    let s := sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k
    ‖(sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) (k+1)).A‖ ^ 2 ≤
      ‖s.A‖ ^ 2 + (a ^ 2 - 1) * ‖g s.x‖ ^ 2 /
        ‖gTilde g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k‖ ^ 2 := by
  let s := sdg g h (fun _ => a) x₀ (ContinuousLinearEquiv.refl ℝ E) k
  let gt := s.B.adjoint (g s.x)
  let ξ := ‖gt‖⁻¹ • gt
  have hgt : gt ≠ 0 := run_gTilde_ne_zero g h x₀ ha k hg
  have hξ : ‖ξ‖ = 1 := normalized_norm hgt
  have hadj : s.A.adjoint ξ = ‖gt‖⁻¹ • g s.x := by
    rw [map_smul]
    exact congrArg (fun z : E => ‖gt‖⁻¹ • z)
      (inverse_adjoint_apply s.A s.B (run_inverse_contract g h x₀ ha k).2.1 (g s.x))
  have hb := dilation_comp_norm_sq_le s.A ha hξ
  rw [hadj, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hb
  dsimp only
  change ‖(sdgStep g h (fun _ => a) k s).A‖ ^ 2 ≤ _
  rw [sdgStep, if_neg hg]
  convert hb using 1
  dsimp only [gTilde, s, gt, ξ]
  ring

end ShorNonsmooth.SpaceDilationProof
end
end

/- Complete checked body: AngleContraction -/
section

set_option autoImplicit false

namespace ShorNonsmooth.SpaceDilationProof

theorem gap_nonnegative {N M gap pairing : ℝ} (hNM : N<M)
    (hlo : N*gap ≤ pairing) (hhi : pairing ≤ M*gap) : 0≤gap := by
  have h := hlo.trans hhi
  nlinarith

theorem centered_angle_contraction {N M α κ q η : ℝ}
    (hN : 0<N) (hNM : N<M) (hα : 0≤α)
    (hαMN : α≤(M+N)/(M-N)) (hκ : 0≤κ)
    (hlo : N*κ≤q) (hhi : q≤M*κ)
    (hη : η=2*M*N/(M+N)*κ) : α^2*(q-η)^2 ≤ q^2 := by
  have hM : 0<M := hN.trans hNM
  have hsum : 0<M+N := by linarith
  have hq : 0≤q := (mul_nonneg hN.le hκ).trans hlo
  have hα' : α*(M-N)≤M+N := (le_div_iff₀ (sub_pos.mpr hNM)).mp hαMN
  have heta : (M+N)*η=2*M*N*κ := by rw [hη]; field_simp
  have hlo' := mul_le_mul_of_nonneg_left hlo (show 0≤2*M by positivity)
  have hhi' := mul_le_mul_of_nonneg_left hhi (show 0≤2*N by positivity)
  have hb : |(M+N)*(q-η)|≤(M-N)*q := by
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos hsum] at hb
  have hs := mul_le_mul_of_nonneg_left hb hα
  have ht := mul_le_mul_of_nonneg_right hα' hq
  have hf : α*|q-η|≤q := by
    apply (mul_le_mul_iff_of_pos_left hsum).mp
    nlinarith
  have hsq := mul_self_le_mul_self (mul_nonneg hα (abs_nonneg _)) hf
  simpa only [← pow_two, mul_pow, sq_abs] using hsq

end ShorNonsmooth.SpaceDilationProof

end

/- Complete checked body: ScalarRecord -/
section

set_option autoImplicit false

namespace ShorNonsmooth.SpaceDilationProof

theorem growth_prefix_upper (S : ℕ → ℝ) (β t : ℝ) (k : ℕ)
    (h0 : S 0=1) (hstep : ∀ j<k, S (j+1)≤S j+β/t^2) :
    S k≤1+(k:ℝ)*β/t^2 := by
  have hh : ∀ j≤k, S j≤1+(j:ℝ)*β/t^2 := by
    intro j
    induction j with
    | zero => intro _; simp [h0]
    | succ j ih =>
      intro hj
      have hs := hstep j (by omega)
      have hp := ih (by omega)
      calc
        S (j+1)≤S j+β/t^2 := hs
        _ ≤ (1+(j:ℝ)*β/t^2)+β/t^2 := add_le_add hp le_rfl
        _ = 1+((j+1:ℕ):ℝ)*β/t^2 := by push_cast; ring
  exact hh k le_rfl

theorem record_from_growth (S a : ℕ → ℝ) (β q : ℝ) (hβ : 0≤β)
    (k : ℕ) (hk : 0<k) (h0 : S 0=1)
    (ha : ∀ i<k, 0<a i)
    (hstep : ∀ i<k, S (i+1)≤S i+β/(a i)^2)
    (hlower : q^k≤S k) :
    ∃ i<k, (a i)^2*(q^k-1)≤(k:ℝ)*β := by
  classical
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (Finset.range k) a
    ⟨0, Finset.mem_range.mpr hk⟩
  have hik : i<k := Finset.mem_range.mp hi
  have hai := ha i hik
  have hstep' (j : ℕ) (hj : j<k) : S (j+1)≤S j+β/(a i)^2 := by
    have hminj := hmin j (Finset.mem_range.mpr hj)
    have hsq : (a i)^2≤(a j)^2 := by nlinarith [ha j hj]
    have hdiv := div_le_div_of_nonneg_left hβ (sq_pos_of_pos hai) hsq
    exact (hstep j hj).trans (add_le_add le_rfl hdiv)
  have hb := growth_prefix_upper S β (a i) k h0 hstep'
  have hh : q^k-1≤(k:ℝ)*β/(a i)^2 := by linarith
  have he := (le_div_iff₀ (sq_pos_of_pos hai)).mp hh
  refine ⟨i, hik, ?_⟩
  nlinarith

end ShorNonsmooth.SpaceDilationProof

end

/- Complete checked body: ScalarSubsequence -/
section

set_option autoImplicit false
open Filter Topology

namespace ShorNonsmooth.SpaceDilationProof

theorem increment_of_large_value {β C q Q a : ℝ} (ha : 0<a) (hQ : 0<Q)
    (hC : 0<C) (hq : 1<q) (hbudget : 2*β≤C^2*(q-1))
    (hlarge : C/Real.sqrt Q≤a) : β/a^2≤(q-1)/2*Q := by
  have hs : 0<Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hmul := (div_le_iff₀ hs).mp hlarge
  have hsq := mul_self_le_mul_self hC.le hmul
  have he : (a*Real.sqrt Q)^2=a^2*Q := by rw [mul_pow, Real.sq_sqrt hQ.le]
  have hbound : C^2≤a^2*Q := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hbound (sub_nonneg.mpr hq.le)
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  nlinarith

theorem arbitrarily_late_small_values (S a : ℕ → ℝ) (β q C : ℝ)
    (hq : 1<q) (hC : 0<C) (hbudget : 2*β≤C^2*(q-1))
    (ha : ∀ k, 0<a k)
    (hstep : ∀ k, S (k+1)≤S k+β/(a k)^2)
    (hlower : ∀ k, q^k≤S k) :
    ∀ N : ℕ, ∃ k : ℕ, N≤k ∧ a k≤C/Real.sqrt (q^k) := by
  intro N
  by_contra hbad
  push Not at hbad
  let T : ℕ → ℝ := fun k => S k-q^k/2
  have hdec (k : ℕ) (hk : N≤k) : T (k+1)≤T k := by
    have hi := increment_of_large_value (ha k) (pow_pos (by linarith : 0<q) k)
      hC hq hbudget (hbad k hk).le
    have hh := hstep k
    dsimp [T]
    rw [pow_succ]
    nlinarith
  have hb (k : ℕ) (hk : N≤k) : T k≤T N := by
    induction k, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact (hdec k hk).trans ih
  have ht : Tendsto (fun k : ℕ => q^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hq
  have hev : ∀ᶠ k : ℕ in atTop, 2*S N-q^N<q^k := ht (eventually_gt_atTop _)
  obtain ⟨k, hk, hlarge⟩ := ((eventually_ge_atTop N).and hev).exists
  have hbound := hb k hk
  dsimp [T] at hbound
  nlinarith [hlower k]

theorem geometric_subsequence_from_growth (S a : ℕ → ℝ) (β q : ℝ)
    (hβ : 0≤β) (hq : 1<q) (ha : ∀ k, 0<a k)
    (hstep : ∀ k, S (k+1)≤S k+β/(a k)^2)
    (hlower : ∀ k, q^k≤S k) :
    ∃ C : ℝ, 0<C ∧ ∃ kp : ℕ → ℕ, StrictMono kp ∧
      ∀ p, a (kp p)≤C/Real.sqrt (q^(kp p)) := by
  let C := Real.sqrt (2*β/(q-1))+1
  have hq0 : 0<q-1 := sub_pos.mpr hq
  have hC : 0<C := by dsimp [C]; positivity
  have he : (Real.sqrt (2*β/(q-1)))^2*(q-1)=2*β := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hbase : (Real.sqrt (2*β/(q-1)))^2≤C^2 := by
    dsimp [C]
    nlinarith [Real.sqrt_nonneg (2*β/(q-1))]
  have hbudget : 2*β≤C^2*(q-1) := by
    have hh := mul_le_mul_of_nonneg_right hbase hq0.le
    linarith
  have hgood := arbitrarily_late_small_values S a β q C hq hC hbudget ha hstep hlower
  obtain ⟨kp, hkp, hp⟩ := Nat.exists_strictMono_subsequence
    (P := fun k => a k≤C/Real.sqrt (q^k)) (fun N => by
      obtain ⟨k, hk, hgoodk⟩ := hgood (N+1)
      exact ⟨k, by omega, hgoodk⟩)
  exact ⟨C, hC, kp, hkp, hp⟩

end ShorNonsmooth.SpaceDilationProof

end

/- Complete checked body: RunModel -/
section

set_option autoImplicit false
open ShorNonsmooth.SpaceDilation

namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def objectiveRule (f : E → ℝ) (xstar : E) (M N : ℝ) : ℕ → E → E → ℝ :=
  fun _ x gt => 2*M*N/(M+N)*(f x-f xstar)/‖gt‖

noncomputable def objectiveState (f : E → ℝ) (g : E → E) (xstar x₀ : E)
    (M N α : ℝ) (k : ℕ) : SDGState n :=
  sdg g (objectiveRule f xstar M N) (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k

noncomputable def objectiveGradient (f : E → ℝ) (g : E → E) (xstar x₀ : E)
    (M N α : ℝ) (k : ℕ) : E :=
  gTilde g (objectiveRule f xstar M N) (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k

theorem sdg_stays_after_stop (g : E → E) (h : ℕ → E → E → ℝ) (α : ℕ → ℝ)
    (x₀ : E) (B₀ : E ≃L[ℝ] E) (k : ℕ) (hg : g (sdg g h α x₀ B₀ k).x=0)
    (j : ℕ) : sdg g h α x₀ B₀ (k+j)=sdg g h α x₀ B₀ k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, sdg, ih]
    simp only [sdgStep, hg, if_pos]

end ShorNonsmooth.SpaceDilationProof
end

/- Complete checked body: RealPowerRates -/
section

set_option autoImplicit false

namespace ShorNonsmooth.SpaceDilationProof

theorem rate_base_gt_one {α : ℝ} (hα : 1<α) {n : ℕ} (hn : 0<n) :
    1<α^(2/(n:ℝ)) := Real.one_lt_rpow hα (by positivity)

theorem rate_power {α : ℝ} (hα : 0<α) (n k : ℕ) :
    (α^(2/(n:ℝ)))^k=α^((2*k:ℝ)/n) := by
  rw [← Real.rpow_mul_natCast hα.le]
  congr 1
  ring

theorem rate_power_dimension {α : ℝ} (hα : 0<α) {n : ℕ} (hn : 0<n) (k : ℕ) :
    ((α^(2/(n:ℝ)))^k)^n=(α^k)^2 := by
  have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hbase : (α^(2/(n:ℝ)))^n=α^2 := by
    rw [← Real.rpow_mul_natCast hα.le, div_mul_cancel₀ 2 hn0]
    exact Real.rpow_natCast α 2
  calc
    _ = ((α^(2/(n:ℝ)))^n)^k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (α^k)^2 := by rw [hbase, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem rate_inverse_sqrt {α : ℝ} (hα : 0<α) (n k : ℕ) :
    1/Real.sqrt ((α^(2/(n:ℝ)))^k)=α^(-(k:ℝ)/n) := by
  have hs : (α^((k:ℝ)/n))^2=(α^(2/(n:ℝ)))^k := by
    rw [← Real.rpow_mul_natCast hα.le, rate_power hα n k]
    congr 1
    ring
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hα _)]
  rw [one_div, ← Real.rpow_neg hα.le]
  congr 1
  ring

theorem lower_from_determinant_power {α S : ℝ} (hα : 0<α) (hS : 0≤S)
    {n : ℕ} (hn : 0<n) (k : ℕ) (hdet : (α^k)^2≤S^n) :
    (α^(2/(n:ℝ)))^k≤S := by
  apply le_of_pow_le_pow_left₀ hn.ne' hS
  rwa [rate_power_dimension hα hn k]

end ShorNonsmooth.SpaceDilationProof

end

/- Complete checked body: DistanceStep -/
section

set_option autoImplicit false
open ShorNonsmooth.SpaceDilation

namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem dilated_step_contract {N M α κ η : ℝ} (hN : 0<N) (hNM : N<M)
    (hα : 0≤α) (hαMN : α≤(M+N)/(M-N)) (hκ : 0≤κ)
    {ξ : E} (hξ : ‖ξ‖=1) (y : E)
    (hlo : N * κ ≤ inner ℝ ξ y) (hhi : inner ℝ ξ y ≤ M * κ)
    (hη : η=2*M*N/(M+N)*κ) :
    ‖dilation α ξ (y-η • ξ)‖≤‖y‖ := by
  have hs := centered_angle_contraction hN hNM hα hαMN hκ hlo hhi hη
  have he := dilation_norm_sq α hξ (y-η • ξ)
  have hi : inner ℝ ξ (y-η • ξ)=inner ℝ ξ y-η := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hξ]
    ring
  have hn : ‖y-η • ξ‖^2=‖y‖^2-2*η*inner ℝ ξ y+η^2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, hξ, real_inner_comm y ξ]
    ring
  rw [hi, hn] at he
  nlinarith [norm_nonneg y, norm_nonneg (dilation α ξ (y-η • ξ))]

theorem normalized_adjoint_pairing (A B : E →L[ℝ] E)
    (hBA : B.comp A=ContinuousLinearMap.id ℝ E) (g z : E) :
    inner ℝ (‖B.adjoint g‖⁻¹ • B.adjoint g) (A z)=inner ℝ g z/‖B.adjoint g‖ := by
  have he : B (A z)=z := congrArg (fun T : E →L[ℝ] E => T z) hBA
  rw [real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left, he]
  ring

theorem transformed_step_error (A B : E →L[ℝ] E)
    (hAB : A.comp B=ContinuousLinearMap.id ℝ E) (x z ξ : E) (η : ℝ) :
    A (x-η • B ξ-z)=A (x-z)-η • ξ := by
  have he : A (B ξ)=ξ := congrArg (fun T : E →L[ℝ] E => T ξ) hAB
  simp only [map_sub, map_smul, he]
  abel

end ShorNonsmooth.SpaceDilationProof

end

/- Complete checked body: DistanceInvariant -/
section

set_option autoImplicit false
open ShorNonsmooth.SpaceDilation

namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem ball_of_transformed_bound (A B : E →L[ℝ] E)
    (hBA : B.comp A=ContinuousLinearMap.id ℝ E) (hB : ∀ u, ‖B u‖≤‖u‖)
    (x z : E) (d : ℝ) (hx : ‖A (x-z)‖≤d) : x∈Metric.closedBall z d := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have he : B (A (x-z))=x-z := congrArg (fun T : E →L[ℝ] E => T (x-z)) hBA
  calc
    ‖x-z‖ = ‖B (A (x-z))‖ := by rw [he]
    _ ≤ ‖A (x-z)‖ := hB _
    _ ≤ d := hx

theorem run_geometry (f : E → ℝ) (g : E → E) (xstar x₀ : E) (d M N α : ℝ)
    (hN : 0<N) (hNM : N<M) (hα : 1≤α) (hαMN : α≤(M+N)/(M-N))
    (h318 : ∀ x∈Metric.closedBall xstar d,
      N*(f x-f xstar) ≤ inner ℝ (g x) (x-xstar) ∧
      inner ℝ (g x) (x-xstar)≤M*(f x-f xstar))
    (hx₀ : x₀∈Metric.closedBall xstar d) :
    ∀ k, ‖(objectiveState f g xstar x₀ M N α k).A
      ((objectiveState f g xstar x₀ M N α k).x-xstar)‖≤d ∧
      (objectiveState f g xstar x₀ M N α k).x∈Metric.closedBall xstar d := by
  let h := objectiveRule f xstar M N
  have hop (k : ℕ) := run_inverse_contract g h x₀ hα k
  have hmain : ∀ k, ‖(objectiveState f g xstar x₀ M N α k).A
      ((objectiveState f g xstar x₀ M N α k).x-xstar)‖≤d := by
    intro k
    induction k with
    | zero =>
      change ‖x₀-xstar‖≤d
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hx₀
    | succ k ih =>
      let s := objectiveState f g xstar x₀ M N α k
      have hball : s.x∈Metric.closedBall xstar d :=
        ball_of_transformed_bound s.A s.B (hop k).2.1 (hop k).2.2 s.x xstar d ih
      obtain ⟨hlo, hhi⟩ := h318 s.x hball
      change ‖(sdgStep g h (fun _ => α) k s).A
        ((sdgStep g h (fun _ => α) k s).x-xstar)‖≤d
      by_cases hg : g s.x=0
      · simpa only [sdgStep, if_pos hg] using ih
      · let gt := s.B.adjoint (g s.x)
        have hgt : gt≠0 := inverse_adjoint_ne_zero s.A s.B (hop k).2.1 hg
        have ht : 0<‖gt‖ := norm_pos_iff.mpr hgt
        let ξ := ‖gt‖⁻¹ • gt
        have hξ : ‖ξ‖=1 := normalized_norm hgt
        let κ := (f s.x-f xstar)/‖gt‖
        have hgap := gap_nonnegative hNM hlo hhi
        have hκ : 0≤κ := div_nonneg hgap ht.le
        have hp : inner ℝ ξ (s.A (s.x-xstar))=inner ℝ (g s.x) (s.x-xstar)/‖gt‖ :=
          normalized_adjoint_pairing s.A s.B (hop k).2.1 (g s.x) (s.x-xstar)
        have hql : N*κ ≤ inner ℝ ξ (s.A (s.x-xstar)) := by
          rw [hp]
          calc
            N*κ = (N*(f s.x-f xstar))/‖gt‖ := by dsimp [κ]; ring
            _ ≤ _ := div_le_div_of_nonneg_right hlo ht.le
        have hqu : inner ℝ ξ (s.A (s.x-xstar))≤M*κ := by
          rw [hp]
          calc
            _ ≤ (M*(f s.x-f xstar))/‖gt‖ := div_le_div_of_nonneg_right hhi ht.le
            _ = M*κ := by dsimp [κ]; ring
        let η := h (k+1) s.x gt
        have heta : η=2*M*N/(M+N)*κ := by dsimp [η, h, objectiveRule, κ]; ring
        have hc := dilated_step_contract hN hNM (zero_le_one.trans hα) hαMN hκ hξ
          (s.A (s.x-xstar)) hql hqu heta
        simp only [sdgStep, if_neg hg]
        change ‖dilation α ξ (s.A (s.x-η • s.B ξ-xstar))‖≤d
        rw [transformed_step_error s.A s.B (hop k).1]
        exact hc.trans ih
  intro k
  refine ⟨hmain k, ?_⟩
  exact ball_of_transformed_bound _ _ (hop k).2.1 (hop k).2.2 _ _ d (hmain k)

end ShorNonsmooth.SpaceDilationProof

end

/- Complete checked body: ObjectiveGap -/
section

set_option autoImplicit false
open ShorNonsmooth.SpaceDilation

namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem objective_gap_le_gradient (f : E → ℝ) (g : E → E) (xstar x₀ : E)
    (d M N α : ℝ) (hN : 0<N) (hNM : N<M) (hα : 1≤α)
    (hαMN : α≤(M+N)/(M-N))
    (h318 : ∀ x∈Metric.closedBall xstar d,
      N*(f x-f xstar) ≤ inner ℝ (g x) (x-xstar) ∧
      inner ℝ (g x) (x-xstar) ≤ M*(f x-f xstar))
    (hx₀ : x₀∈Metric.closedBall xstar d) (k : ℕ) :
    f (objectiveState f g xstar x₀ M N α k).x-f xstar ≤
      (d/N)*‖objectiveGradient f g xstar x₀ M N α k‖ := by
  let s := objectiveState f g xstar x₀ M N α k
  let gt := objectiveGradient f g xstar x₀ M N α k
  have hgeo := run_geometry f g xstar x₀ d M N α hN hNM hα hαMN h318 hx₀ k
  have hlo := (h318 s.x hgeo.2).1
  have hop := run_inverse_contract g (objectiveRule f xstar M N) x₀ hα k
  have he : s.B (s.A (s.x-xstar))=s.x-xstar :=
    congrArg (fun T : E →L[ℝ] E => T (s.x-xstar)) hop.2.1
  have hp : inner ℝ gt (s.A (s.x-xstar))=inner ℝ (g s.x) (s.x-xstar) := by
    change inner ℝ (s.B.adjoint (g s.x)) (s.A (s.x-xstar))=_
    rw [ContinuousLinearMap.adjoint_inner_left, he]
  have hb := (real_inner_le_norm gt (s.A (s.x-xstar))).trans
    (mul_le_mul_of_nonneg_left hgeo.1 (norm_nonneg gt))
  rw [hp] at hb
  calc
    f s.x-f xstar ≤ (‖gt‖*d)/N := by
      apply (le_div_iff₀ hN).mpr
      nlinarith
    _ = (d/N)*‖gt‖ := by ring

end ShorNonsmooth.SpaceDilationProof

end

/- Complete checked body: GradientRates -/
section

noncomputable section
open ShorNonsmooth.SpaceDilation
namespace ShorNonsmooth.SpaceDilationProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem gradient_growth_bound (g : E → E) (h : ℕ → E → E → ℝ) (x₀ : E)
    {α G : ℝ} (hα : 1 < α) (hG : 0 ≤ G) (k : ℕ)
    (hg : g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).x ≠ 0)
    (hbound : ‖g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).x‖ ≤ G) :
    let s := sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k
    ‖(sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) (k+1)).A‖ ^ 2 ≤
      ‖s.A‖ ^ 2 + ((α ^ 2 - 1) * G ^ 2) /
        ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k‖ ^ 2 := by
  have hgrowth := run_norm_growth g h x₀ hα.le k hg
  have hs : ‖g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).x‖ ^ 2 ≤ G ^ 2 := by
    nlinarith [norm_nonneg (g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).x)]
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ α ^ 2 - 1 by nlinarith)
  have hd := div_le_div_of_nonneg_right hm
    (sq_nonneg ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k‖)
  exact hgrowth.trans (add_le_add le_rfl hd)

theorem gradient_determinant_lower (hn : 0 < n) (g : E → E) (h : ℕ → E → E → ℝ)
    (x₀ : E) {α : ℝ} (hα : 1 < α) (k : ℕ)
    (hg : ∀ i < k, g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) i).x ≠ 0) :
    (α ^ (2 / (n : ℝ))) ^ k ≤
      ‖(sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).A‖ ^ 2 := by
  have hd := det_sq_le_opNorm_pow
    (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).A
  rw [run_det g h x₀ hα.le k hg] at hd
  exact lower_from_determinant_power (zero_lt_one.trans hα) (sq_nonneg _) hn k hd

theorem gradient_subsequence (hn : 0 < n) (g : E → E) (h : ℕ → E → E → ℝ)
    (x₀ : E) {α G : ℝ} (hα : 1 < α) (hG : 0 ≤ G)
    (hbound : ∀ k, ‖g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).x‖ ≤ G) :
    ∃ C : ℝ, 0 < C ∧ ∃ kp : ℕ → ℕ, StrictMono kp ∧
      ∀ p, ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) (kp p)‖ ≤
        C * α ^ (-(kp p : ℝ) / n) := by
  by_cases hstop : ∃ j, g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) j).x = 0
  · obtain ⟨j, hj⟩ := hstop
    refine ⟨1, zero_lt_one, (fun p => j + p), ?_, ?_⟩
    · intro p q hpq
      exact Nat.add_lt_add_left hpq j
    · intro p
      have he := sdg_stays_after_stop g h (fun _ => α) x₀
        (ContinuousLinearEquiv.refl ℝ E) j hj p
      simp only [gTilde, he, hj, map_zero, norm_zero, one_mul]
      exact (Real.rpow_pos_of_pos (zero_lt_one.trans hα) _).le
  · push Not at hstop
    let S := fun k => ‖(sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).A‖ ^ 2
    let a := fun k => ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k‖
    let β := (α ^ 2 - 1) * G ^ 2
    let q := α ^ (2 / (n : ℝ))
    have hβ : 0 ≤ β := mul_nonneg (by nlinarith) (sq_nonneg _)
    have ha (k : ℕ) : 0 < a k := norm_pos_iff.mpr (run_gTilde_ne_zero g h x₀ hα.le k (hstop k))
    have hstep (k : ℕ) : S (k+1) ≤ S k + β / (a k)^2 :=
      gradient_growth_bound g h x₀ hα hG k (hstop k) (hbound k)
    have hlower (k : ℕ) : q ^ k ≤ S k :=
      gradient_determinant_lower hn g h x₀ hα k (fun i _ => hstop i)
    obtain ⟨C, hC, kp, hkp, hp⟩ := geometric_subsequence_from_growth S a β q hβ
      (rate_base_gt_one hα hn) ha hstep hlower
    refine ⟨C, hC, kp, hkp, ?_⟩
    intro p
    have hh := hp p
    change a (kp p) ≤ C / Real.sqrt ((α ^ (2 / (n : ℝ))) ^ (kp p)) at hh
    rw [div_eq_mul_one_div, rate_inverse_sqrt (zero_lt_one.trans hα) n (kp p)] at hh
    exact hh

theorem gradient_record (hn : 0 < n) (g : E → E) (h : ℕ → E → E → ℝ)
    (x₀ : E) {α G : ℝ} (hα : 1 < α) (hG : 0 ≤ G)
    (hbound : ∀ k, ‖g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) k).x‖ ≤ G)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ i < k, ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) i‖ ≤
      G * Real.sqrt (k * (α ^ 2 - 1)) / Real.sqrt (α ^ ((2 * k : ℝ) / n) - 1) := by
  by_cases hstop : ∃ j < k, g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) j).x = 0
  · obtain ⟨j, hjk, hj⟩ := hstop
    refine ⟨j, hjk, ?_⟩
    simp only [gTilde, hj, map_zero, norm_zero]
    exact div_nonneg (mul_nonneg hG (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · push Not at hstop
    let : NeZero n := ⟨hn.ne'⟩
    let S := fun i => ‖(sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) i).A‖ ^ 2
    let a := fun i => ‖gTilde g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ E) i‖
    let β := (α ^ 2 - 1) * G ^ 2
    let q := α ^ (2 / (n : ℝ))
    have hβ : 0 ≤ β := mul_nonneg (by nlinarith) (sq_nonneg _)
    have hq : 1 < q := rate_base_gt_one hα hn
    have h0 : S 0 = 1 := by simp [S, sdg]
    have ha (i : ℕ) (hi : i < k) : 0 < a i :=
      norm_pos_iff.mpr (run_gTilde_ne_zero g h x₀ hα.le i (hstop i hi))
    have hstep (i : ℕ) (hi : i < k) : S (i+1) ≤ S i + β / (a i)^2 :=
      gradient_growth_bound g h x₀ hα hG i (hstop i hi) (hbound i)
    have hlower : q ^ k ≤ S k := gradient_determinant_lower hn g h x₀ hα k hstop
    obtain ⟨i, hi, hrec⟩ := record_from_growth S a β q hβ k (by omega) h0 ha hstep hlower
    have hQ : 0 < q ^ k - 1 := sub_pos.mpr (one_lt_pow₀ hq (by omega : k ≠ 0))
    have hden : 0 < Real.sqrt (q ^ k - 1) := Real.sqrt_pos.mpr hQ
    have ht : 0 ≤ (k : ℝ) * (α ^ 2 - 1) := mul_nonneg (Nat.cast_nonneg _) (by nlinarith)
    have hnum : (G * Real.sqrt ((k : ℝ) * (α ^ 2 - 1))) ^ 2 = (k : ℝ) * β := by
      rw [mul_pow, Real.sq_sqrt ht]
      dsimp only [β]
      ring
    have hleft : (a i * Real.sqrt (q ^ k - 1)) ^ 2 = (a i)^2 * (q ^ k - 1) := by
      rw [mul_pow, Real.sq_sqrt hQ.le]
    have hmul : a i * Real.sqrt (q ^ k - 1) ≤ G * Real.sqrt ((k : ℝ) * (α ^ 2 - 1)) := by
      nlinarith [mul_nonneg (ha i hi).le hden.le,
        mul_nonneg hG (Real.sqrt_nonneg ((k : ℝ) * (α ^ 2 - 1)))]
    have hh := (le_div_iff₀ hden).mpr hmul
    refine ⟨i, hi, ?_⟩
    change a i ≤ G * Real.sqrt ((k : ℝ) * (α ^ 2 - 1)) /
      Real.sqrt (α ^ ((2 * k : ℝ) / n) - 1)
    dsimp only [q] at hh
    rwa [rate_power (zero_lt_one.trans hα) n k] at hh

end ShorNonsmooth.SpaceDilationProof
end
end

/- Complete checked body: ShorRoot -/
section

set_option autoImplicit false

namespace ShorNonsmooth.SpaceDilation

/-- Shor (1985), pp. 58–59, Theorem 3.4, with the record bound its proof (p. 59) establishes.
Under the assumptions of Theorem 3.3 (with `B₀ = I`), and with `G` a bound for `‖g‖` on
`S_d = {x : ‖x - x*‖ ≤ d}` (the book's `G = max_{x ∈ S_d} ‖g_f(x)‖`):

1. there are a constant `c > 0` and a strictly increasing sequence of indices `k_p` with
   `f(x_{k_p}) - f(x*) ≤ c α^{-k_p/n}` for every `p`;
2. for every `k ≥ 1`, `min_{0 ≤ i ≤ k-1} [f(x_i) - f(x*)] ≤ G √(k(α² - 1)) d / (N √(α^{2k/n} - 1))`.

(The printed statement has no factor `1/N` and takes the minimum over `1 ≤ i ≤ k`; the proof
derives the bound with `1/N` from Theorem 3.2, whose proof bounds `g̃_0, …, g̃_{k-1}`.
See the mission's HARD.md.) -/
theorem sdg_geometric_convergence {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (xstar x₀ : EuclideanSpace ℝ (Fin n)) (d M N α G : ℝ)
    (hd : 0 < d) (hN : 0 < N) (hNM : N < M)
    (h318 : ∀ x ∈ Metric.closedBall xstar d,
      N * (f x - f xstar) ≤ inner ℝ (g x) (x - xstar) ∧
        inner ℝ (g x) (x - xstar) ≤ M * (f x - f xstar))
    (hG : ∀ x ∈ Metric.closedBall xstar d, ‖g x‖ ≤ G)
    (hx₀ : x₀ ∈ Metric.closedBall xstar d)
    (hα : 1 < α) (hαMN : α ≤ (M + N) / (M - N)) :
    (∃ c : ℝ, 0 < c ∧ ∃ kp : ℕ → ℕ, StrictMono kp ∧
      ∀ p : ℕ,
        f (sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
            (ContinuousLinearEquiv.refl ℝ _) (kp p)).x - f xstar ≤
          c * α ^ (-(kp p : ℝ) / n)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ i : ℕ, i < k ∧
      f (sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
          (ContinuousLinearEquiv.refl ℝ _) i).x - f xstar ≤
        G * Real.sqrt (k * (α ^ 2 - 1)) * d / (N * Real.sqrt (α ^ ((2 * k : ℝ) / n) - 1)) := by
  let h := ShorNonsmooth.SpaceDilationProof.objectiveRule f xstar M N
  have hgeo := ShorNonsmooth.SpaceDilationProof.run_geometry f g xstar x₀ d M N α
    hN hNM hα.le hαMN h318 hx₀
  have hgap := ShorNonsmooth.SpaceDilationProof.objective_gap_le_gradient
    f g xstar x₀ d M N α hN hNM hα.le hαMN h318 hx₀
  have hG0 : 0 ≤ G := (norm_nonneg (g x₀)).trans (hG x₀ hx₀)
  have hbound (k : ℕ) :
      ‖g (sdg g h (fun _ => α) x₀ (ContinuousLinearEquiv.refl ℝ _) k).x‖ ≤ G :=
    hG _ (hgeo k).2
  constructor
  · obtain ⟨C, hC, kp, hkp, hp⟩ := ShorNonsmooth.SpaceDilationProof.gradient_subsequence
      hn g h x₀ hα hG0 hbound
    refine ⟨(d/N)*C, by positivity, kp, hkp, ?_⟩
    intro p
    have hb : ‖ShorNonsmooth.SpaceDilationProof.objectiveGradient f g xstar x₀ M N α (kp p)‖ ≤
        C * α ^ (-(kp p : ℝ) / n) := hp p
    have hm := mul_le_mul_of_nonneg_left hb (div_nonneg hd.le hN.le)
    change f (ShorNonsmooth.SpaceDilationProof.objectiveState f g xstar x₀ M N α (kp p)).x-
      f xstar ≤ ((d/N)*C)*α^(-(kp p:ℝ)/n)
    calc
      _ ≤ (d/N)*‖ShorNonsmooth.SpaceDilationProof.objectiveGradient f g xstar x₀ M N α (kp p)‖ :=
        hgap (kp p)
      _ ≤ (d/N)*(C*α^(-(kp p:ℝ)/n)) := hm
      _ = _ := by ring
  · intro k hk
    obtain ⟨i, hi, hgi⟩ := ShorNonsmooth.SpaceDilationProof.gradient_record
      hn g h x₀ hα hG0 hbound k hk
    refine ⟨i, hi, ?_⟩
    have hb : ‖ShorNonsmooth.SpaceDilationProof.objectiveGradient f g xstar x₀ M N α i‖ ≤
        G*Real.sqrt (k*(α^2-1))/Real.sqrt (α^((2*k:ℝ)/n)-1) := hgi
    have hm := mul_le_mul_of_nonneg_left hb (div_nonneg hd.le hN.le)
    change f (ShorNonsmooth.SpaceDilationProof.objectiveState f g xstar x₀ M N α i).x-f xstar ≤ _
    calc
      _ ≤ (d/N)*‖ShorNonsmooth.SpaceDilationProof.objectiveGradient f g xstar x₀ M N α i‖ := hgap i
      _ ≤ (d/N)*(G*Real.sqrt (k*(α^2-1))/Real.sqrt (α^((2*k:ℝ)/n)-1)) := hm
      _ = _ := by rw [div_mul_div_comm]; ring


end ShorNonsmooth.SpaceDilation

end

open ShorNonsmooth.SpaceDilation

theorem solution {n : ℕ} (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (xstar x₀ : EuclideanSpace ℝ (Fin n)) (d M N α G : ℝ)
    (hd : 0 < d) (hN : 0 < N) (hNM : N < M)
    (h318 : ∀ x ∈ Metric.closedBall xstar d,
      N * (f x - f xstar) ≤ inner ℝ (g x) (x - xstar) ∧
        inner ℝ (g x) (x - xstar) ≤ M * (f x - f xstar))
    (hG : ∀ x ∈ Metric.closedBall xstar d, ‖g x‖ ≤ G)
    (hx₀ : x₀ ∈ Metric.closedBall xstar d)
    (hα : 1 < α) (hαMN : α ≤ (M + N) / (M - N)) :
    (∃ c : ℝ, 0 < c ∧ ∃ kp : ℕ → ℕ, StrictMono kp ∧
      ∀ p : ℕ,
        f (sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
            (ContinuousLinearEquiv.refl ℝ _) (kp p)).x - f xstar ≤
          c * α ^ (-(kp p : ℝ) / n)) ∧
    ∀ k : ℕ, 1 ≤ k → ∃ i : ℕ, i < k ∧
      f (sdg g (fun _ x gt => 2 * M * N / (M + N) * (f x - f xstar) / ‖gt‖) (fun _ => α) x₀
          (ContinuousLinearEquiv.refl ℝ _) i).x - f xstar ≤
        G * Real.sqrt (k * (α ^ 2 - 1)) * d / (N * Real.sqrt (α ^ ((2 * k : ℝ) / n) - 1)) := by
  exact ShorNonsmooth.SpaceDilation.sdg_geometric_convergence hn f g xstar x₀ d M N α G hd hN hNM h318 hG hx₀ hα hαMN

#print axioms ShorNonsmooth.SpaceDilation.sdg_geometric_convergence
#print axioms solution
