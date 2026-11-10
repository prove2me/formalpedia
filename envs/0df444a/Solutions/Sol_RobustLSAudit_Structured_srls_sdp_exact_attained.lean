-- Prove2me | solution 1 for RobustLSAudit.Structured.srls_sdp_exact_attained
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T10:33:35.190198+00:00
-- url     : https://prove2.me/submissions/c2e5c1fe-609f-4f59-a41b-c262777bbc48

import Mathlib
import Definitions.Def_RobustLSAudit_Structured_SDP32Feasible
import Theorems.Thm_RobustLS_Structured_sdp32_iff_calF
import Theorems.Thm_RobustLS_Structured_srls_sdp_exact

set_option autoImplicit false

namespace RobustLSAuditAttainedProof

open Matrix RobustLS.Structured

/-- The identification of `Fin n → ℝ` with Euclidean space. -/
noncomputable abbrev eE (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm

lemma eucNorm_eq {n : ℕ} (v : Fin n → ℝ) : eucNorm v = ‖eE n v‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucNorm, Real.norm_eq_abs, sq_abs]

lemma abs_le_eucNorm {p : ℕ} (δ : Fin p → ℝ) (i : Fin p) : |δ i| ≤ eucNorm δ := by
  rw [eucNorm]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => δ j ^ 2) (fun j _ => sq_nonneg (δ j))
    (Finset.mem_univ i)

lemma rS_nonneg {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) : 0 ≤ rS A0 A b0 b 1 x := by
  apply Real.sSup_nonneg
  rintro r ⟨δ, -, rfl⟩
  simp only [structuredResidual, eucNorm]
  exact Real.sqrt_nonneg _

/-! ### Clause 1 -/

lemma clause1_pos {n m p : ℕ} (hp : 1 ≤ p) (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    rS A0 A b0 b 1 x ^ 2 ≤ lam ↔
      ∃ τ : ℝ, RobustLSAudit.Structured.SDP32Feasible A0 A b0 b lam τ x := by
  rw [← (srls_sdp_exact hp A0 A b0 b).1 x lam]
  constructor
  · rintro ⟨τ, hτ⟩
    refine ⟨τ, ?_, hτ⟩
    have hpsd : (sdp32Matrix A0 A b0 b lam τ x).PosSemidef := hτ
    have h := hpsd.diag_nonneg (i := Sum.inl (Sum.inr ⟨0, hp⟩))
    simpa [sdp32Matrix] using h
  · rintro ⟨τ, -, hτ⟩
    exact ⟨τ, hτ⟩

lemma rS_zero {n m : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin 0 → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin 0 → Fin n → ℝ)
    (x : Fin m → ℝ) : rS A0 A b0 b 1 x = eucNorm (A0 *ᵥ x - b0) := by
  have hset : {r : ℝ | ∃ δ : Fin 0 → ℝ, eucNorm δ ≤ 1 ∧ r = structuredResidual A0 A b0 b x δ}
      = {eucNorm (A0 *ᵥ x - b0)} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨δ, -, rfl⟩
      simp [structuredResidual, structMatrix, structVector]
    · rintro rfl
      exact ⟨0, by simp [eucNorm], by simp [structuredResidual, structMatrix, structVector]⟩
  rw [rS, hset, csSup_singleton]

lemma calF_zero_eq {n m : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin 0 → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin 0 → Fin n → ℝ)
    (x : Fin m → ℝ) (lam τ : ℝ) :
    calF A0 A b0 b x lam τ = Matrix.diagonal (fun _ => lam - τ - hval A0 b0 x) := by
  ext i j
  rcases i with ⟨⟩ | i
  · rcases j with ⟨⟩ | j
    · simp [calF]
    · exact j.elim0
  · exact i.elim0

lemma clause1_zero {n m : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin 0 → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin 0 → Fin n → ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    rS A0 A b0 b 1 x ^ 2 ≤ lam ↔
      ∃ τ : ℝ, RobustLSAudit.Structured.SDP32Feasible A0 A b0 b lam τ x := by
  simp only [RobustLSAudit.Structured.SDP32Feasible, sdp32_iff_calF, calF_zero_eq,
    posSemidef_diagonal_iff, rS_zero]
  constructor
  · intro h
    refine ⟨0, le_rfl, fun _ => ?_⟩
    simp only [hval]
    linarith
  · rintro ⟨τ, hτ, h⟩
    have h' := h (Sum.inl ())
    simp only [hval] at h'
    linarith

lemma clause1 {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (lam : ℝ) :
    rS A0 A b0 b 1 x ^ 2 ≤ lam ↔
      ∃ τ : ℝ, RobustLSAudit.Structured.SDP32Feasible A0 A b0 b lam τ x := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · exact clause1_zero A0 A b0 b x lam
  · exact clause1_pos hp A0 A b0 b x lam

/-! ### Attainment of the SRLS minimum -/

/-- Residual as a function of the stacked data `y = (A₀x, (Aᵢx)ᵢ)` in Euclidean coordinates. -/
noncomputable def resE {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) (δ : Fin p → ℝ) : ℝ :=
  ‖y.1 - eE n b0 + ∑ i, δ i • (y.2 i - eE n (b i))‖

noncomputable def GE {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) : ℝ :=
  sSup {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧ r = resE b0 b y δ}

noncomputable def LE {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n)) :=
  LinearMap.prod ((eE n).toLinearMap ∘ₗ Matrix.mulVecLin A0)
    (LinearMap.pi fun i => (eE n).toLinearMap ∘ₗ Matrix.mulVecLin (A i))

lemma res_eq {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) (δ : Fin p → ℝ) :
    structuredResidual A0 A b0 b x δ = resE b0 b (LE A0 A x) δ := by
  have h1 : (LE A0 A x).1 = eE n (A0 *ᵥ x) := rfl
  have h2 : ∀ i, (LE A0 A x).2 i = eE n (A i *ᵥ x) := fun i => rfl
  have hv : structMatrix A0 A δ *ᵥ x - structVector b0 b δ =
      (A0 *ᵥ x - b0) + ∑ i, δ i • (A i *ᵥ x - b i) := by
    simp only [structMatrix, structVector, Matrix.add_mulVec, Matrix.sum_mulVec,
      Matrix.smul_mulVec, smul_sub, Finset.sum_sub_distrib]
    abel
  rw [structuredResidual, eucNorm_eq, resE, hv, h1]
  simp only [h2, map_add, map_sub, map_sum, map_smul]

lemma rS_eq {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (x : Fin m → ℝ) : rS A0 A b0 b 1 x = GE b0 b (LE A0 A x) := by
  rw [rS, GE]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, res_eq]

lemma resE_le_bound {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) (δ : Fin p → ℝ)
    (hδ : eucNorm δ ≤ 1) :
    resE b0 b y δ ≤ ‖y.1 - eE n b0‖ + ∑ i, ‖y.2 i - eE n (b i)‖ := by
  have h1 := norm_add_le (y.1 - eE n b0) (∑ i, δ i • (y.2 i - eE n (b i)))
  have h2 : ‖∑ i, δ i • (y.2 i - eE n (b i))‖ ≤ ∑ i, ‖y.2 i - eE n (b i)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) ((abs_le_eucNorm δ i).trans hδ)
  unfold resE
  linarith

lemma GE_bdd {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) :
    BddAbove {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧ r = resE b0 b y δ} := by
  refine ⟨‖y.1 - eE n b0‖ + ∑ i, ‖y.2 i - eE n (b i)‖, ?_⟩
  rintro r ⟨δ, hδ, rfl⟩
  exact resE_le_bound b0 b y δ hδ

lemma GE_ne {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) :
    {r : ℝ | ∃ δ : Fin p → ℝ, eucNorm δ ≤ 1 ∧ r = resE b0 b y δ}.Nonempty :=
  ⟨resE b0 b y 0, 0, by simp [eucNorm], rfl⟩

lemma resE_le_GE {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) (δ : Fin p → ℝ)
    (hδ : eucNorm δ ≤ 1) : resE b0 b y δ ≤ GE b0 b y :=
  le_csSup (GE_bdd b0 b y) ⟨δ, hδ, rfl⟩

lemma resE_lip {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y y' : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) (δ : Fin p → ℝ)
    (hδ : eucNorm δ ≤ 1) :
    resE b0 b y δ ≤ resE b0 b y' δ + (1 + (p : ℝ)) * dist y y' := by
  have key : y.1 - eE n b0 + ∑ i, δ i • (y.2 i - eE n (b i)) =
      (y'.1 - eE n b0 + ∑ i, δ i • (y'.2 i - eE n (b i))) +
        ((y.1 - y'.1) + ∑ i, δ i • (y.2 i - y'.2 i)) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  have h1 : ‖y.1 - y'.1‖ ≤ ‖y - y'‖ := norm_fst_le (y - y')
  have h2 : ∀ i, ‖δ i • (y.2 i - y'.2 i)‖ ≤ ‖y - y'‖ := fun i => by
    rw [norm_smul, Real.norm_eq_abs]
    have h' : ‖y.2 i - y'.2 i‖ ≤ ‖y - y'‖ :=
      (norm_le_pi_norm (y - y').2 i).trans (norm_snd_le (y - y'))
    exact (mul_le_of_le_one_left (norm_nonneg _) ((abs_le_eucNorm δ i).trans hδ)).trans h'
  have h3 : ‖∑ i, δ i • (y.2 i - y'.2 i)‖ ≤ (p : ℝ) * ‖y - y'‖ := by
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h2 i)
  have h4 := norm_add_le (y.1 - y'.1) (∑ i, δ i • (y.2 i - y'.2 i))
  have h5 := norm_add_le (y'.1 - eE n b0 + ∑ i, δ i • (y'.2 i - eE n (b i)))
    ((y.1 - y'.1) + ∑ i, δ i • (y.2 i - y'.2 i))
  unfold resE
  rw [key, dist_eq_norm]
  linarith

lemma GE_lip {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y y' : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) :
    GE b0 b y ≤ GE b0 b y' + (1 + (p : ℝ)) * dist y y' := by
  apply csSup_le (GE_ne b0 b y)
  rintro r ⟨δ, hδ, rfl⟩
  have h1 := resE_lip b0 b y y' δ hδ
  have h2 := resE_le_GE b0 b y' δ hδ
  linarith

lemma GE_cont {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) :
    Continuous (GE b0 b) :=
  (LipschitzWith.of_le_add_mul' (1 + (p : ℝ)) (fun y y' => GE_lip b0 b y y')).continuous

lemma GE_coercive {n p : ℕ} (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ)
    (y : EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) :
    ‖y‖ ≤ 2 * GE b0 b y + (‖eE n b0‖ + ∑ i, ‖eE n (b i)‖) := by
  have hC0 : 0 ≤ ∑ i, ‖eE n (b i)‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have h0 : ‖y.1 - eE n b0‖ ≤ GE b0 b y := by
    have := resE_le_GE b0 b y 0 (by simp [eucNorm])
    simpa [resE] using this
  have hG0 : 0 ≤ GE b0 b y := (norm_nonneg _).trans h0
  have hfst : ‖y.1‖ ≤ GE b0 b y + ‖eE n b0‖ := by
    have := norm_sub_norm_le y.1 (eE n b0)
    linarith
  have hsnd : ∀ i, ‖y.2 i‖ ≤ 2 * GE b0 b y + ∑ j, ‖eE n (b j)‖ := by
    intro i
    have hi : ‖y.1 - eE n b0 + (y.2 i - eE n (b i))‖ ≤ GE b0 b y := by
      have hδ : eucNorm (Pi.single i (1 : ℝ) : Fin p → ℝ) ≤ 1 := by
        simp [eucNorm, Pi.single_apply]
      have := resE_le_GE b0 b y _ hδ
      simpa [resE, Pi.single_apply, ite_smul] using this
    have hv := norm_sub_le (y.1 - eE n b0 + (y.2 i - eE n (b i))) (y.1 - eE n b0)
    have hv' : y.1 - eE n b0 + (y.2 i - eE n (b i)) - (y.1 - eE n b0) = y.2 i - eE n (b i) := by
      abel
    rw [hv'] at hv
    have hw := norm_sub_norm_le (y.2 i) (eE n (b i))
    have hs : ‖eE n (b i)‖ ≤ ∑ j, ‖eE n (b j)‖ :=
      Finset.single_le_sum (f := fun j => ‖eE n (b j)‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)
    linarith
  have hsnd' : ‖y.2‖ ≤ 2 * GE b0 b y + (‖eE n b0‖ + ∑ i, ‖eE n (b i)‖) := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have := hsnd i
    have := norm_nonneg (eE n b0)
    linarith
  refine norm_prod_le_iff.mpr ⟨?_, hsnd'⟩
  have := norm_nonneg (eE n b0)
  linarith

lemma exists_min {n m p : ℕ} (A0 : Matrix (Fin n) (Fin m) ℝ)
    (A : Fin p → Matrix (Fin n) (Fin m) ℝ) (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) :
    ∃ x : Fin m → ℝ, IsSRLSSolution A0 A b0 b 1 x := by
  have hcont := GE_cont b0 b
  let c : ℝ := GE b0 b (LE A0 A 0)
  let S : Set (EuclideanSpace ℝ (Fin n) × (Fin p → EuclideanSpace ℝ (Fin n))) :=
    ((LinearMap.range (LE A0 A) : Submodule ℝ _) : Set _) ∩ {y | GE b0 b y ≤ c}
  have hclosed : IsClosed S :=
    (LinearMap.range (LE A0 A)).closed_of_finiteDimensional.inter
      (isClosed_le hcont continuous_const)
  have hbdd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨2 * c + (‖eE n b0‖ + ∑ i, ‖eE n (b i)‖), fun y hy => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := GE_coercive b0 b y
    have h2 : GE b0 b y ≤ c := hy.2
    linarith
  have hcpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : S.Nonempty := ⟨LE A0 A 0, LinearMap.mem_range.mpr ⟨0, rfl⟩,
    show GE b0 b (LE A0 A 0) ≤ c from le_rfl⟩
  obtain ⟨y, ⟨hyr, hyc⟩, hmin⟩ := hcpt.exists_isMinOn hne hcont.continuousOn
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hyr
  refine ⟨x, fun x' => ?_⟩
  rw [rS_eq, rS_eq]
  by_cases h : GE b0 b (LE A0 A x') ≤ c
  · exact isMinOn_iff.mp hmin _ ⟨LinearMap.mem_range.mpr ⟨x', rfl⟩, h⟩
  · exact (show GE b0 b (LE A0 A x) ≤ c from hyc).trans (not_le.mp h).le

/-! ### Assembly -/

theorem main {n m p : ℕ}
    (A0 : Matrix (Fin n) (Fin m) ℝ) (A : Fin p → Matrix (Fin n) (Fin m) ℝ)
    (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) :
    (∀ (x : Fin m → ℝ) (lam : ℝ),
      RobustLS.Structured.rS A0 A b0 b 1 x ^ 2 ≤ lam ↔
        ∃ τ : ℝ, RobustLSAudit.Structured.SDP32Feasible A0 A b0 b lam τ x) ∧
    (∃ (lam τ : ℝ) (x : Fin m → ℝ), RobustLSAudit.Structured.SDP32Optimal A0 A b0 b lam τ x) ∧
    (∀ (lam τ : ℝ) (x : Fin m → ℝ),
      RobustLSAudit.Structured.SDP32Optimal A0 A b0 b lam τ x ↔
        RobustLSAudit.Structured.SDP32Feasible A0 A b0 b lam τ x ∧
          RobustLS.Structured.IsSRLSSolution A0 A b0 b 1 x ∧
          lam = RobustLS.Structured.rS A0 A b0 b 1 x ^ 2) := by
  have hc1 := fun x lam => clause1 A0 A b0 b x lam
  have hnn := fun x => rS_nonneg A0 A b0 b x
  have key : ∀ x x', IsSRLSSolution A0 A b0 b 1 x →
      rS A0 A b0 b 1 x ^ 2 ≤ rS A0 A b0 b 1 x' ^ 2 := fun x x' h =>
    pow_le_pow_left₀ (hnn x) (h x') 2
  refine ⟨hc1, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := exists_min A0 A b0 b
    obtain ⟨τ, hτ⟩ := (hc1 x _).mp le_rfl
    exact ⟨_, τ, x, hτ, fun lam' τ' x' h' => (key x x' hx).trans ((hc1 x' lam').mpr ⟨τ', h'⟩)⟩
  · intro lam τ x
    constructor
    · rintro ⟨hF, hopt⟩
      have h1 : rS A0 A b0 b 1 x ^ 2 ≤ lam := (hc1 x lam).mpr ⟨τ, hF⟩
      have h2 : ∀ x', lam ≤ rS A0 A b0 b 1 x' ^ 2 := fun x' => by
        obtain ⟨τ', h'⟩ := (hc1 x' _).mp le_rfl
        exact hopt _ τ' x' h'
      refine ⟨hF, fun x' => ?_, le_antisymm (h2 x) h1⟩
      have h3 := h1.trans (h2 x')
      nlinarith [hnn x, hnn x']
    · rintro ⟨hF, hx, rfl⟩
      exact ⟨hF, fun lam' τ' x' h' => (key x x' hx).trans ((hc1 x' lam').mpr ⟨τ', h'⟩)⟩

end RobustLSAuditAttainedProof

open RobustLSAudit.Structured in
theorem solution {n m p : ℕ}
    (A0 : Matrix (Fin n) (Fin m) ℝ) (A : Fin p → Matrix (Fin n) (Fin m) ℝ)
    (b0 : Fin n → ℝ) (b : Fin p → Fin n → ℝ) :
    (∀ (x : Fin m → ℝ) (lam : ℝ),
      RobustLS.Structured.rS A0 A b0 b 1 x ^ 2 ≤ lam ↔
        ∃ τ : ℝ, SDP32Feasible A0 A b0 b lam τ x) ∧
    (∃ (lam τ : ℝ) (x : Fin m → ℝ), SDP32Optimal A0 A b0 b lam τ x) ∧
    (∀ (lam τ : ℝ) (x : Fin m → ℝ),
      SDP32Optimal A0 A b0 b lam τ x ↔
        SDP32Feasible A0 A b0 b lam τ x ∧
          RobustLS.Structured.IsSRLSSolution A0 A b0 b 1 x ∧
          lam = RobustLS.Structured.rS A0 A b0 b 1 x ^ 2) := by
  exact RobustLSAuditAttainedProof.main A0 A b0 b
