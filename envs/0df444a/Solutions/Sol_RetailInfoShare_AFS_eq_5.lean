-- Prove2me | solution 1 for RetailInfoShare.AFS.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:49:27.743679+00:00
-- url     : https://prove2.me/submissions/a50f2fad-6fab-428c-8e20-7c82127836ce

import Mathlib
import Definitions.Def_RetailInfoShare_AFS_Model
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RetailInfoShare.AFS.GaussAux

open RetailInfoShare.AFS

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Covariance of two linear combinations of independent centered Gaussians. -/
lemma cov_lin [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hlaw : ∀ k, HasLaw (Y k) (gaussianReal 0 (v k)) μ) (hind : iIndepFun Y μ)
    (α β : ι → ℝ) :
    cov[fun ω => ∑ k, α k * Y k ω, fun ω => ∑ k, β k * Y k ω; μ] =
      ∑ k, α k * β k * (v k : ℝ) := by
  have hmem : ∀ k, MemLp (Y k) 2 μ := fun k =>
    (hlaw k).hasGaussianLaw.memLp_two
  rw [covariance_fun_sum_fun_sum (fun k => (hmem k).const_mul (α k))
    (fun k => (hmem k).const_mul (β k))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_self (hlaw k).aemeasurable, (hlaw k).variance_eq, variance_id_gaussianReal]
    ring
  · intro l _ hlk
    rw [covariance_const_mul_left, covariance_const_mul_right,
      (hind.indepFun (Ne.symm hlk)).covariance_eq_zero (hmem k) (hmem l)]
    ring
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Orthogonal linear combinations of independent centered Gaussians are independent. -/
lemma indep_lin [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (Y : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hlaw : ∀ k, HasLaw (Y k) (gaussianReal 0 (v k)) μ) (hind : iIndepFun Y μ)
    (α : ι → ℝ) (β : κ → ι → ℝ) (horth : ∀ c, ∑ k, α k * β c k * (v k : ℝ) = 0) :
    IndepFun (fun ω => ∑ k, α k * Y k ω) (fun ω c => ∑ k, β c k * Y k ω) μ := by
  have hG : ∀ k, HasGaussianLaw (Y k) μ := fun k => (hlaw k).hasGaussianLaw
  have hJ : HasGaussianLaw (fun ω => (Y · ω)) μ := hind.hasGaussianLaw hG
  let LA : (ι → ℝ) →L[ℝ] ℝ := ∑ k, α k • ContinuousLinearMap.proj k
  let LB : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
    ContinuousLinearMap.pi fun c => ∑ k, β c k • ContinuousLinearMap.proj k
  let L : (ι → ℝ) →L[ℝ] (Unit → ℝ) × (κ → ℝ) :=
    (ContinuousLinearMap.pi fun _ => LA).prod LB
  have hL : (fun ω => L (Y · ω)) =
      fun ω => ((fun _ : Unit => ∑ k, α k * Y k ω), fun c => ∑ k, β c k * Y k ω) := by
    funext ω
    simp [L, LA, LB]
  have hXY := hJ.map_fun L
  rw [hL] at hXY
  have hcov : ∀ (i : Unit) (c : κ),
      cov[fun ω => ∑ k, α k * Y k ω, fun ω => ∑ k, β c k * Y k ω; μ] = 0 := by
    intro _ c
    rw [cov_lin Y v hlaw hind]
    exact horth c
  have h := HasGaussianLaw.indepFun_of_covariance_eval
    (X := fun (_ : Unit) => fun ω => ∑ k, α k * Y k ω)
    (Y := fun c => fun ω => ∑ k, β c k * Y k ω) hXY hcov
  have h2 := h.comp (φ := fun f : Unit → ℝ => f ()) (ψ := id) (show Measurable fun f : Unit → ℝ => f () from measurable_pi_apply ())
    measurable_id
  exact h2

end RetailInfoShare.AFS.GaussAux

namespace RetailInfoShare.AFS.Eq5Aux

open RetailInfoShare.AFS RetailInfoShare.AFS.GaussAux

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The primitives relevant to seller `j`: `u`, the `e i`, and the `ξ i j`. -/
def idx (j : Fin P.N) : Option (Fin P.N ⊕ Fin P.N) → Prim P.N
  | none => .u
  | some (.inl i) => .e i
  | some (.inr i) => .ξ i j

lemma idx_injective (j : Fin P.N) : Function.Injective (idx (P := P) j) := by
  intro x y h
  rcases x with _ | x | x <;> rcases y with _ | y | y <;> simp_all [idx]

/-- The random variables indexed by `idx j`. -/
def Yv (Z : Primitives P Ω μ) (j : Fin P.N) : Option (Fin P.N ⊕ Fin P.N) → Ω → ℝ
  | none => Z.u
  | some (.inl i) => Z.e i
  | some (.inr i) => Z.ξ i j

def vv (P : Params) : Option (Fin P.N ⊕ Fin P.N) → ℝ≥0
  | none => P.sig
  | some (.inl _) => P.t
  | some (.inr _) => 1

lemma Yv_law (Z : Primitives P Ω μ) (j : Fin P.N) :
    ∀ k, HasLaw (Yv Z j k) (gaussianReal 0 (vv P k)) μ := by
  intro k
  rcases k with _ | i | i
  · exact Z.law_u
  · exact Z.law_e i
  · exact Z.law_ξ i j

lemma Yv_indep (Z : Primitives P Ω μ) (j : Fin P.N) : iIndepFun (Yv Z j) μ := by
  have h := Z.indep.precomp (idx_injective (P := P) j)
  convert h using 2 with k
  rcases k with _ | i | i <;> rfl

end RetailInfoShare.AFS.Eq5Aux

open RetailInfoShare.AFS RetailInfoShare.AFS.GaussAux RetailInfoShare.AFS.Eq5Aux in
theorem solution (P : Params) (hP : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Primitives P Ω μ)
    (M : NoiseMatrix P.N) (j : Fin P.N) (η : ℝ≥0) (hη : ∀ i, M i j = (η : ℝ≥0∞)) :
    μ[Z.u | info Z M j] =ᵐ[μ] fun ω =>
      (P.sig : ℝ) / ((P.sig : ℝ) + ((P.t : ℝ) + (η : ℝ)) / P.N) *
        ((1 / (P.N : ℝ)) * ∑ i, xhat Z M i j ω) := by
  classical
  haveI := Z.isProb
  have hN : (0 : ℝ) < P.N := by exact_mod_cast hP.1
  have hs : (0 : ℝ) < P.sig := NNReal.coe_pos.mpr hP.2.2.2.1
  have ht : (0 : ℝ) < P.t := NNReal.coe_pos.mpr hP.2.2.2.2.1
  have hη0 : (0 : ℝ) ≤ η := η.2
  set lam : ℝ := (P.sig : ℝ) / ((P.sig : ℝ) + ((P.t : ℝ) + (η : ℝ)) / P.N) with hlam
  set s : ℝ := Real.sqrt (η : ℝ) with hs_def
  have hss : s * s = η := Real.mul_self_sqrt hη0
  have hMj : ∀ i, Real.sqrt (M i j).toReal = s := by
    intro i; rw [hη i]; simp [s]
  -- coefficients
  let β : Fin P.N → Option (Fin P.N ⊕ Fin P.N) → ℝ := fun c k =>
    match k with
    | none => 1
    | some (.inl i) => if i = c then 1 else 0
    | some (.inr i) => if i = c then s else 0
  let α : Option (Fin P.N ⊕ Fin P.N) → ℝ := fun k =>
    match k with
    | none => 1 - lam
    | some (.inl _) => -lam / P.N
    | some (.inr _) => -lam * s / P.N
  have hX : ∀ c ω, xhat Z M c j ω = ∑ k, β c k * Yv Z j k ω := by
    intro c ω
    simp [Fintype.sum_option, Fintype.sum_sum_type, β, Yv, xhat, hMj]
    ring
  set W : Ω → ℝ := fun ω => Z.u ω - lam * ((1 / (P.N : ℝ)) * ∑ i, xhat Z M i j ω) with hW
  have hWsum : ∀ ω, W ω = ∑ k, α k * Yv Z j k ω := by
    intro ω
    simp only [hW, xhat, hMj, Fintype.sum_option, Fintype.sum_sum_type, α, Yv,
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have horth : ∀ c, ∑ k, α k * β c k * (vv P k : ℝ) = 0 := by
    intro c
    simp only [Fintype.sum_option, Fintype.sum_sum_type, α, β, vv]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, NNReal.coe_one]
    rw [hlam]
    field_simp
    nlinarith [hss]
  have hind := indep_lin (Yv Z j) (vv P) (Yv_law Z j) (Yv_indep Z j) α β horth
  have hWeq : W = fun ω => ∑ k, α k * Yv Z j k ω := funext hWsum
  have hXeq : (fun ω c => xhat Z M c j ω) = fun ω c => ∑ k, β c k * Yv Z j k ω := by
    funext ω c; exact hX c ω
  rw [← hWeq, ← hXeq] at hind
  -- the information σ-algebra is generated by the vector of signals
  have hinfo : info Z M j =
      MeasurableSpace.comap (fun ω c => xhat Z M c j ω) MeasurableSpace.pi := by
    unfold info
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_congr (fun i => ?_)
    rw [iSup_pos (by rw [hη i]; exact ENNReal.coe_ne_top), MeasurableSpace.comap_comp]
    rfl
  have hmeasX : ∀ c, Measurable (xhat Z M c j) := by
    intro c
    unfold xhat
    exact (Z.meas_u.add (Z.meas_e c)).add ((Z.meas_ξ c j).const_mul _)
  have hmeasV : Measurable (fun ω c => xhat Z M c j ω) := measurable_pi_lambda _ hmeasX
  have hle : info Z M j ≤ ‹MeasurableSpace Ω› := by
    rw [hinfo]; exact hmeasV.comap_le
  have hmeasW : Measurable W := by
    rw [hWeq]
    exact Finset.measurable_sum _ (fun k _ => ((Yv_law Z j k).hasGaussianLaw.aemeasurable
      |> fun _ => by
        rcases k with _ | i | i
        · exact Z.meas_u.const_mul _
        · exact (Z.meas_e i).const_mul _
        · exact (Z.meas_ξ i j).const_mul _))
  -- E[W | info] = E[W] = 0
  have hWint : ∫ ω, W ω ∂μ = 0 := by
    rw [hWeq]
    have hI : ∀ k, Integrable (fun ω => α k * Yv Z j k ω) μ := fun k =>
      ((Yv_law Z j k).hasGaussianLaw.integrable).const_mul _
    rw [integral_finsetSum _ (fun k _ => hI k)]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [integral_const_mul, (Yv_law Z j k).integral_eq, integral_id_gaussianReal, mul_zero]
  have hcW : μ[W | info Z M j] =ᵐ[μ] fun _ => (0 : ℝ) := by
    have h := condExp_indep_eq (m₁ := MeasurableSpace.comap W inferInstance)
      (m₂ := info Z M j) hmeasW.comap_le hle
      (f := W) (Measurable.of_comap_le le_rfl).stronglyMeasurable
      (by rw [hinfo]; exact hind)
    rw [hWint] at h
    exact h
  -- the posterior mean term is info-measurable
  have hXm : ∀ c, Measurable[info Z M j] (xhat Z M c j) := by
    intro c
    rw [hinfo]
    have h1 : Measurable[MeasurableSpace.comap (fun ω c => xhat Z M c j ω) MeasurableSpace.pi]
        (fun ω c => xhat Z M c j ω) := Measurable.of_comap_le le_rfl
    exact (show Measurable fun f : Fin P.N → ℝ => f c from measurable_pi_apply c).comp h1
  set R : Ω → ℝ := fun ω => lam * ((1 / (P.N : ℝ)) * ∑ i, xhat Z M i j ω) with hR
  have hRm : StronglyMeasurable[info Z M j] R := by
    have : Measurable[info Z M j] R :=
      ((Finset.measurable_sum _ (fun i _ => hXm i)).const_mul _).const_mul _
    exact this.stronglyMeasurable
  have hXint : ∀ c, Integrable (xhat Z M c j) μ := by
    intro c
    have : xhat Z M c j = fun ω => ∑ k, β c k * Yv Z j k ω := funext (hX c)
    rw [this]
    exact integrable_finsetSum _ (fun k _ =>
      ((Yv_law Z j k).hasGaussianLaw.integrable).const_mul _)
  have hRint : Integrable R μ :=
    ((integrable_finsetSum _ (fun i _ => hXint i)).const_mul _).const_mul _
  have hWint' : Integrable W μ := by
    rw [hWeq]
    exact integrable_finsetSum _ (fun k _ =>
      ((Yv_law Z j k).hasGaussianLaw.integrable).const_mul _)
  have hu : Z.u = W + R := by
    funext ω; simp [hW, hR]
  rw [hu]
  have hadd := condExp_add hWint' hRint (info Z M j) (μ := μ)
  have hR' : μ[R | info Z M j] = R := condExp_of_stronglyMeasurable hle hRm hRint
  rw [hR'] at hadd
  filter_upwards [hadd, hcW] with ω h1 h2
  rw [h1, Pi.add_apply, h2]
  simp [hR]
