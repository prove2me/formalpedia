-- Prove2me | solution 1 for PGDMap20261031.pgd_stability_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-01T02:04:06.493513+00:00
-- url     : https://prove2.me/submissions/e8f54c2d-0b6e-4b54-9f9e-3fd8b58a0db9

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_PGDMap20261031_PGD
import Theorems.Thm_PGDMap20261031_pgd_best_modulus

open PGDMap20261031 Set Filter
open scoped Topology RealInnerProductSpace BigOperators
noncomputable section

private lemma norm_combo_sq {d : ℕ} (a b : Space d) (t : ℝ) :
    ‖t • a + (1 - t) • b‖ ^ 2 =
      t * ‖a‖ ^ 2 + (1 - t) * ‖b‖ ^ 2 - t * (1 - t) * ‖a - b‖ ^ 2 := by
  have heq : a - b = a + (-b) := sub_eq_add_neg a b
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right,
    heq, norm_add_sq_real, inner_neg_right, norm_neg]
  ring

private lemma nonnegative_prox_exists {d : ℕ} (Q : Penalty d)
    (hclosed : IsClosed {z : Space d × ℝ | z.1 ∈ Q.domain ∧ Q.value z.1 ≤ z.2})
    (hne : Q.domain.Nonempty) (hQ : ∀ z ∈ Q.domain, 0 ≤ Q.value z)
    (η : ℝ) (hη : 0 < η) (u : Space d) :
    ∃ z ∈ Q.domain, ∀ w ∈ Q.domain,
      Q.value z + ‖z - u‖ ^ 2 / (2 * η) ≤ Q.value w + ‖w - u‖ ^ 2 / (2 * η) := by
  obtain ⟨w0, hw0⟩ := hne
  let F := fun z : Space d => Q.value z + ‖z - u‖ ^ 2 / (2 * η)
  let C := F w0
  have hFnonneg (z : Space d) (hz : z ∈ Q.domain) : 0 ≤ F z :=
    add_nonneg (hQ z hz) (div_nonneg (sq_nonneg _) (by positivity))
  have hC : 0 ≤ C := hFnonneg w0 hw0
  let R := 2 * η * C + 1
  have hbound (z : Space d) (hz : z ∈ Q.domain) (hv : F z ≤ C) :
      z ∈ Metric.closedBall u R := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsq : ‖z - u‖ ^ 2 ≤ 2 * η * C := by
      have H := hQ z hz
      have HD : ‖z - u‖ ^ 2 / (2 * η) ≤ C := by dsimp [F] at hv; linarith
      have := (div_le_iff₀ (by positivity : 0 < 2 * η)).mp HD
      nlinarith only [this]
    dsimp [R]
    nlinarith [norm_nonneg (z - u), mul_nonneg hη.le hC]
  let Epi : Set (Space d × ℝ) := {z | z.1 ∈ Q.domain ∧ F z.1 ≤ z.2}
  have hEpi : IsClosed Epi := by
    have H := hclosed.preimage (show Continuous (fun z : Space d × ℝ =>
      (z.1, z.2 - ‖z.1 - u‖ ^ 2 / (2 * η))) by fun_prop)
    convert H using 1
    ext z
    change (z.1 ∈ Q.domain ∧ F z.1 ≤ z.2) ↔
      (z.1 ∈ Q.domain ∧ Q.value z.1 ≤ z.2 - ‖z.1 - u‖ ^ 2 / (2 * η))
    dsimp [F]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> linarith
  let K := (Metric.closedBall u R ×ˢ Icc (0 : ℝ) C) ∩ Epi
  have hK : IsCompact K := ((isCompact_closedBall u R).prod isCompact_Icc).inter_right hEpi
  have hKn : K.Nonempty := ⟨(w0, C), ⟨hbound w0 hw0 le_rfl, hC, le_rfl⟩, hw0, le_rfl⟩
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hKn continuous_snd.continuousOn
  refine ⟨z.1, hz.2.1, ?_⟩
  intro w hw
  by_cases hFC : F w ≤ C
  · have hwK : (w, F w) ∈ K := ⟨⟨hbound w hw hFC, hFnonneg w hw, hFC⟩, hw, le_rfl⟩
    have H : z.2 ≤ F w := hmin hwK
    exact hz.2.2.trans H
  · exact hz.2.2.trans (hz.1.2.2.trans (le_of_not_ge hFC))

private lemma nonnegative_prox_comparison {d : ℕ} (Q : Penalty d)
    (hQ : ∀ z ∈ Q.domain, 0 ≤ Q.value z) (η ε : ℝ) (hη : 0 < η)
    (u z w : Space d) (hz : z ∈ Q.domain) (hw : w ∈ Q.domain) (hε : Q.value w ≤ ε)
    (hmin : ∀ y ∈ Q.domain, Q.value z + ‖z - u‖ ^ 2 / (2 * η) ≤
      Q.value y + ‖y - u‖ ^ 2 / (2 * η)) :
    Q.value z ≤ ε + ‖w - u‖ ^ 2 / (2 * η) ∧
      ‖z - w‖ ≤ 2 * ‖u - w‖ + Real.sqrt (2 * η * ε) := by
  have H := hmin w hw
  have hz0 := hQ z hz
  have he0 : 0 ≤ ε := (hQ w hw).trans hε
  constructor
  · have hnon : 0 ≤ ‖z - u‖ ^ 2 / (2 * η) := by positivity
    linarith
  · have hsq : ‖z - u‖ ^ 2 ≤ ‖w - u‖ ^ 2 + 2 * η * ε := by
      have H' := mul_le_mul_of_nonneg_right H (by positivity : 0 ≤ 2 * η)
      field_simp [ne_of_gt hη] at H'
      nlinarith only [H', hε, hz0, hη]
    have hs := Real.sq_sqrt (show 0 ≤ 2 * η * ε by positivity)
    have hzdist : ‖z - u‖ ≤ ‖w - u‖ + Real.sqrt (2 * η * ε) := by
      nlinarith [norm_nonneg (z - u), norm_nonneg (w - u), Real.sqrt_nonneg (2 * η * ε)]
    have htri : ‖z - w‖ ≤ ‖z - u‖ + ‖u - w‖ := by
      calc
        ‖z - w‖ = ‖(z - u) + (u - w)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev w u] at hzdist
    linarith

private def residualPenalty {d : ℕ} (r : Penalty d) (μ : ℝ) : Penalty d :=
  ⟨r.domain, fun x => r.value x - μ / 2 * ‖x‖ ^ 2⟩

private lemma residual_valid {d : ℕ} (r : Penalty d) (hr : IsPenalty r) (μ : ℝ)
    (hs : StrongPenalty r μ) : IsPenalty (residualPenalty r μ) := by
  refine ⟨hr.1, ?_, hr.2.2.1, ?_⟩
  · have H := hr.2.1.preimage (show Continuous (fun z : Space d × ℝ =>
      (z.1, z.2 + μ / 2 * ‖z.1‖ ^ 2)) by fun_prop)
    convert H using 1
    ext z
    change (z.1 ∈ r.domain ∧ r.value z.1 - μ / 2 * ‖z.1‖ ^ 2 ≤ z.2) ↔
      (z.1 ∈ r.domain ∧ r.value z.1 ≤ z.2 + μ / 2 * ‖z.1‖ ^ 2)
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> linarith
  · intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst b
    have H := hs x hx y hy a ⟨ha, by linarith⟩
    have Hnorm := congrArg (fun z : ℝ => μ / 2 * z) (norm_combo_sq x y a)
    change r.value (a • x + (1 - a) • y) - μ / 2 * ‖a • x + (1 - a) • y‖ ^ 2 ≤
      a * (r.value x - μ / 2 * ‖x‖ ^ 2) +
        (1 - a) * (r.value y - μ / 2 * ‖y‖ ^ 2)
    nlinarith only [H, Hnorm]

private lemma residual_strong {d : ℕ} (r : Penalty d) (μ ν : ℝ)
    (hs : StrongPenalty (residualPenalty r μ) ν) : StrongPenalty r (μ + ν) := by
  intro x hx y hy t ht
  have H := hs x hx y hy t ht
  change r.value (t • x + (1 - t) • y) - μ / 2 * ‖t • x + (1 - t) • y‖ ^ 2 ≤
    t * (r.value x - μ / 2 * ‖x‖ ^ 2) + (1 - t) * (r.value y - μ / 2 * ‖y‖ ^ 2) -
      ν / 2 * t * (1 - t) * ‖x - y‖ ^ 2 at H
  have Hnorm := congrArg (fun z : ℝ => μ / 2 * z) (norm_combo_sq x y t)
  nlinarith only [H, Hnorm]

private lemma admissible_bounded {d : ℕ} (r : Penalty d) (hn : NonSingleton r) :
    BddAbove {μ : ℝ | 0 ≤ μ ∧ StrongPenalty r μ} := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  let D := ‖x - y‖ ^ 2 / 8
  let R := (1 / 2 : ℝ) * r.value x + (1 - 1 / 2 : ℝ) * r.value y -
    r.value ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y)
  have hD : 0 < D := div_pos (sq_pos_of_pos (norm_sub_pos_iff.mpr hxy)) (by norm_num)
  refine ⟨R / D, ?_⟩
  intro μ hμ
  apply (le_div_iff₀ hD).2
  have H := hμ.2 x hx y hy (1 / 2) ⟨by norm_num, by norm_num⟩
  dsimp [D, R]
  nlinarith only [H]

private lemma residual_best_zero {d : ℕ} (r : Penalty d) (hr : IsPenalty r) (hn : NonSingleton r) :
    IsPenalty (residualPenalty r (bestModulus r)) ∧
      bestModulus (residualPenalty r (bestModulus r)) = 0 := by
  have hbest := pgd_best_modulus d r hr hn
  have hp := residual_valid r hr (bestModulus r) hbest.2
  refine ⟨hp, ?_⟩
  have hb0 := pgd_best_modulus d (residualPenalty r (bestModulus r)) hp hn
  have HS := residual_strong r (bestModulus r) _ hb0.2
  have Hle : bestModulus r + bestModulus (residualPenalty r (bestModulus r)) ≤ bestModulus r :=
    le_csSup (admissible_bounded r hn) ⟨add_nonneg hbest.1 hb0.1, HS⟩
  linarith only [Hle, hb0.1]

private def blowup {d : ℕ} (p : Penalty d) (c s : Space d) (δ : ℝ) : Penalty d :=
  ⟨{z | c + δ • z ∈ p.domain}, fun z =>
    (p.value (c + δ • z) - p.value c - δ * inner ℝ s z) / δ ^ 2⟩

private lemma blowup_properties {d : ℕ} (p : Penalty d) (hp : IsPenalty p)
    (c s : Space d) (hs : Supports p c s) (δ : ℝ) (hδ : 0 < δ) :
    IsClosed {z : Space d × ℝ | z.1 ∈ (blowup p c s δ).domain ∧
      (blowup p c s δ).value z.1 ≤ z.2} ∧
    (blowup p c s δ).domain.Nonempty ∧
    (∀ z ∈ (blowup p c s δ).domain, 0 ≤ (blowup p c s δ).value z) := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  refine ⟨?_, ⟨0, by simpa [blowup] using hs.1⟩, ?_⟩
  · have H := hp.2.1.preimage (show Continuous (fun z : Space d × ℝ =>
      (c + δ • z.1, δ ^ 2 * z.2 + p.value c + δ * inner ℝ s z.1)) by fun_prop)
    convert H using 1
    ext z
    change (c + δ • z.1 ∈ p.domain ∧
      (p.value (c + δ • z.1) - p.value c - δ * inner ℝ s z.1) / δ ^ 2 ≤ z.2) ↔
        (c + δ • z.1 ∈ p.domain ∧
          p.value (c + δ • z.1) ≤ δ ^ 2 * z.2 + p.value c + δ * inner ℝ s z.1)
    rw [div_le_iff₀ hδsq]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> nlinarith only [h2]
  · intro z hz
    have H := hs.2 (c + δ • z) hz
    rw [add_sub_cancel_left, real_inner_smul_right] at H
    apply div_nonneg _ hδsq.le
    linarith only [H]

private def scalarE (t : ℝ) : Space 1 := EuclideanSpace.single 0 t
private def scalarCo (x : Space 1) : ℝ := x 0

private lemma scalarCo_e (t : ℝ) : scalarCo (scalarE t) = t := by simp [scalarE, scalarCo]

private lemma scalarE_co (x : Space 1) : scalarE (scalarCo x) = x := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [scalarE, scalarCo]

private lemma scalar_norm (x : Space 1) : ‖x‖ = |scalarCo x| := by
  calc
    ‖x‖ = ‖scalarE (scalarCo x)‖ := congrArg norm (scalarE_co x).symm
    _ = |scalarCo x| := by rw [scalarE, EuclideanSpace.norm_single, Real.norm_eq_abs]

private lemma scalar_norm_sq (x : Space 1) : ‖x‖ ^ 2 = scalarCo x ^ 2 := by
  rw [scalar_norm, sq_abs]

private lemma extract_scalar (f : Space 1 → ℝ) (g : Space 1 → Space 1) (L : ℝ)
    (hf : SmoothConvex f g L) :
    (∀ t, HasDerivAt (fun t => f (scalarE t)) (scalarCo (g (scalarE t))) t) ∧
    ConvexOn ℝ univ (fun t => f (scalarE t)) ∧
    (∀ x y, |scalarCo (g (scalarE x)) - scalarCo (g (scalarE y))| ≤ L * |x - y|) := by
  have he (a b x y : ℝ) : scalarE (a * x + b * y) = a • scalarE x + b • scalarE y := by
    apply_fun scalarCo using (fun x y h => by rw [← scalarE_co x, ← scalarE_co y, h])
    simp [scalarCo, scalarE]
  refine ⟨?_, ⟨convex_univ, ?_⟩, ?_⟩
  · intro t
    have heder : HasDerivAt scalarE (scalarE 1) t := by
      have Heq : scalarE = fun t : ℝ => t • scalarE 1 := by
        funext t
        apply_fun scalarCo using (fun x y h => by rw [← scalarE_co x, ← scalarE_co y, h])
        simp [scalarCo, scalarE]
      rw [Heq]
      simpa using (hasDerivAt_id t).smul_const (scalarE 1)
    have H := (hf.2.1 (scalarE t)).hasFDerivAt.comp_hasDerivAt t heder
    have hi : inner ℝ (g (scalarE t)) (scalarE 1) = scalarCo (g (scalarE t)) := by
      rw [real_inner_comm, scalarE, EuclideanSpace.inner_single_left]
      simp [scalarCo]
    convert H using 1 <;> first | rfl | exact hi.symm
  · intro x hx y hy a b ha hb hab
    have H := hf.1.2 (mem_univ (scalarE x)) (mem_univ (scalarE y)) ha hb hab
    simpa only [smul_eq_mul, he] using H
  · intro x y
    have H := hf.2.2 (scalarE x) (scalarE y)
    rw [scalar_norm, scalar_norm] at H
    simpa [scalarCo, scalarE] using H

private lemma quadratic_scalar_update (μ γ c u : ℝ) (hμ : 0 ≤ μ) (hγ : 0 < γ)
    (hmin : ∀ z : ℝ, μ / 2 * u ^ 2 + (u - c) ^ 2 / (2 * γ) ≤
      μ / 2 * z ^ 2 + (z - c) ^ 2 / (2 * γ)) : (1 + γ * μ) * u = c := by
  let b := 1 + γ * μ
  have hb : 0 < b := by dsimp [b]; positivity
  have H := hmin (c / b)
  have hid : μ / 2 * u ^ 2 + (u - c) ^ 2 / (2 * γ) -
      (μ / 2 * (c / b) ^ 2 + (c / b - c) ^ 2 / (2 * γ)) =
        b / (2 * γ) * (u - c / b) ^ 2 := by
    dsimp [b]
    field_simp [ne_of_gt hγ, ne_of_gt hb]
    <;> ring
  have hsq : (u - c / b) ^ 2 = 0 := by
    have hnon : 0 ≤ b / (2 * γ) * (u - c / b) ^ 2 := by positivity
    have hprod : b / (2 * γ) * (u - c / b) ^ 2 = 0 := by linarith only [H, hid, hnon]
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (div_pos hb (by positivity)))
  have heq : u = c / b := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  change b * u = c
  rw [heq, mul_div_cancel₀ _ (ne_of_gt hb)]

private lemma scalar_target_update (f : Space 1 → ℝ) (g : Space 1 → Space 1)
    (μ γ : ℝ) (hμ : 0 ≤ μ) (hγ : 0 < γ) (N : ℕ) (x : ℕ → Space 1)
    (hx : IsPGDTrajectory (quadraticPenalty 1 μ) g γ N x) :
    ∀ i < N, (1 + γ * μ) * scalarCo (x (i + 1)) = scalarCo (x i) - γ * scalarCo (g (x i)) := by
  intro i hi
  apply quadratic_scalar_update μ γ _ _ hμ hγ
  intro z
  have H := hx.2 i hi (scalarE z) (mem_univ _)
  change μ / 2 * ‖x (i + 1)‖ ^ 2 + _ ≤ μ / 2 * ‖scalarE z‖ ^ 2 + _ at H
  simpa [scalar_norm_sq, scalarCo, scalarE] using H

private def liftF {d : ℕ} (φ : ℝ → ℝ) (c k v : Space d) (δ : ℝ) : Space d → ℝ :=
  fun x => δ ^ 2 * φ (inner ℝ v (x - c) / δ) - inner ℝ k x

private def liftG {d : ℕ} (ψ : ℝ → ℝ) (c k v : Space d) (δ : ℝ) : Space d → Space d :=
  fun x => (δ * ψ (inner ℝ v (x - c) / δ)) • v - k

private lemma lift_smooth {d : ℕ} (φ ψ : ℝ → ℝ)
    (hder : ∀ t, HasDerivAt φ (ψ t) t) (hc : ConvexOn ℝ univ φ)
    (L : ℝ) (hL : 0 < L) (hlip : ∀ x y, |ψ x - ψ y| ≤ L * |x - y|)
    (c k v : Space d) (δ : ℝ) (hδ : 0 < δ) (hv : ‖v‖ = 1) :
    SmoothConvex (liftF φ c k v δ) (liftG ψ c k v δ) L := by
  let T := fun x : Space d => inner ℝ v (x - c) / δ
  have hT (x y : Space d) (a b : ℝ) (hab : a + b = 1) :
      T (a • x + b • y) = a * T x + b * T y := by
    have Heq : a • x + b • y - c = a • (x - c) + b • (y - c) := by
      calc
        a • x + b • y - c = a • x + b • y - (a + b) • c := by rw [hab, one_smul]
        _ = _ := by module
    simp only [T, Heq, inner_add_right, real_inner_smul_right]
    ring
  refine ⟨⟨convex_univ, ?_⟩, ?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    have H := mul_le_mul_of_nonneg_left (hc.2 (mem_univ (T x)) (mem_univ (T y)) ha hb hab) (sq_nonneg δ)
    change δ ^ 2 * φ (T (a • x + b • y)) - inner ℝ k (a • x + b • y) ≤
      a * (δ ^ 2 * φ (T x) - inner ℝ k x) + b * (δ ^ 2 * φ (T y) - inner ℝ k y)
    rw [hT x y a b hab, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    simp only [smul_eq_mul] at H
    nlinarith only [H]
  · intro x
    apply hasGradientAt_iff_hasFDerivAt.mpr
    have htd : HasFDerivAt T (δ⁻¹ • InnerProductSpace.toDual ℝ (Space d) v) x := by
      have H := ((InnerProductSpace.toDual ℝ (Space d) v).hasFDerivAt (x := x) |>.sub_const
        (inner ℝ v c)).const_mul δ⁻¹
      convert H using 1 <;> first | rfl | skip
      · funext y
        dsimp [T]
        rw [inner_sub_right]
        ring
    have H := ((hder (T x)).comp_hasFDerivAt x htd).const_mul (δ ^ 2)
    have H' := H.sub (InnerProductSpace.toDual ℝ (Space d) k).hasFDerivAt
    convert H' using 1 <;> first | rfl | skip
    · ext y
      change inner ℝ ((δ * ψ (T x)) • v - k) y = _
      simp only [inner_sub_left, real_inner_smul_left]
      change δ * ψ (T x) * inner ℝ v y - inner ℝ k y =
        δ ^ 2 * (ψ (T x) * (δ⁻¹ * inner ℝ v y)) - inner ℝ k y
      field_simp [ne_of_gt hδ]
      <;> ring
  · intro x y
    have Hnorm : ‖liftG ψ c k v δ x - liftG ψ c k v δ y‖ = δ * |ψ (T x) - ψ (T y)| := by
      have Hvec : liftG ψ c k v δ x - liftG ψ c k v δ y =
          (δ * (ψ (T x) - ψ (T y))) • v := by dsimp [liftG, T]; module
      rw [Hvec, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hδ, hv, mul_one]
    rw [Hnorm]
    have H := mul_le_mul_of_nonneg_left (hlip (T x) (T y)) hδ.le
    have Hproj : δ * |T x - T y| ≤ ‖x - y‖ := by
      have Hinner := abs_real_inner_le_norm v (x - y)
      rw [hv, one_mul] at Hinner
      have Hval : δ * (T x - T y) = inner ℝ v (x - y) := by
        dsimp [T]
        rw [inner_sub_right, inner_sub_right, inner_sub_right]
        field_simp [ne_of_gt hδ]
        <;> ring
      rw [← Hval, abs_mul, abs_of_pos hδ] at Hinner
      exact Hinner
    have Hbound := mul_le_mul_of_nonneg_left Hproj hL.le
    nlinarith only [H, Hbound]

private lemma norm_difference {d : ℕ} (x y : Space d) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
  rw [sub_eq_add_neg, norm_add_sq_real, inner_neg_right, norm_neg]
  ring

private lemma penalty_expansion {d : ℕ} (r : Penalty d) (μ : ℝ) (c s : Space d)
    (δ : ℝ) (hδ : δ ≠ 0) (z : Space d) :
    r.value (c + δ • z) = δ ^ 2 * (blowup (residualPenalty r μ) c s δ).value z +
      r.value c + δ * inner ℝ (s + μ • c) z + μ / 2 * δ ^ 2 * ‖z‖ ^ 2 := by
  dsimp [blowup, residualPenalty]
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_add_left, real_inner_smul_left]
  field_simp [hδ]
  <;> ring

private lemma lifted_total {d : ℕ} (r : Penalty d) (μ : ℝ) (φ : ℝ → ℝ)
    (c s v : Space d) (δ : ℝ) (hδ : δ ≠ 0) (z : Space d) :
    totalValue r (liftF φ c (s + μ • c) v δ) (c + δ • z) =
      δ ^ 2 * (φ (inner ℝ v z) + μ / 2 * ‖z‖ ^ 2 +
        (blowup (residualPenalty r μ) c s δ).value z) +
          r.value c - inner ℝ (s + μ • c) c := by
  rw [totalValue, penalty_expansion r μ c s δ hδ z]
  dsimp [liftF]
  rw [add_sub_cancel_left, real_inner_smul_right, mul_div_cancel_left₀ _ hδ,
    inner_add_right, real_inner_smul_right]
  ring

private lemma prox_difference {d : ℕ} (r : Penalty d) (μ γ : ℝ) (c s V : Space d)
    (δ : ℝ) (hδ : δ ≠ 0) (hγ : γ ≠ 0) (hb : 1 + γ * μ ≠ 0) (z w : Space d) :
    (r.value (c + δ • z) + ‖δ • (z - V) - γ • (s + μ • c)‖ ^ 2 / (2 * γ)) -
      (r.value (c + δ • w) + ‖δ • (w - V) - γ • (s + μ • c)‖ ^ 2 / (2 * γ)) =
    δ ^ 2 * (((blowup (residualPenalty r μ) c s δ).value z +
      ‖z - (1 + γ * μ)⁻¹ • V‖ ^ 2 / (2 * (γ / (1 + γ * μ)))) -
      ((blowup (residualPenalty r μ) c s δ).value w +
      ‖w - (1 + γ * μ)⁻¹ • V‖ ^ 2 / (2 * (γ / (1 + γ * μ))))) := by
  rw [penalty_expansion r μ c s δ hδ z, penalty_expansion r μ c s δ hδ w]
  simp only [norm_difference, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm z (s + μ • c), real_inner_comm w (s + μ • c)]
  have hb' : 1 + μ * γ ≠ 0 := by simpa only [mul_comm] using hb
  field_simp [hγ, hb, hb']
  <;> ring

private lemma lift_trajectory {d : ℕ} (r : Penalty d) (μ γ : ℝ) (hμ : 0 ≤ μ)
    (hγ : 0 < γ) (ψ : ℝ → ℝ) (c s v : Space d) (δ : ℝ) (hδ : 0 < δ)
    (N : ℕ) (z : ℕ → Space d)
    (hdom : ∀ i ≤ N, z i ∈ (blowup (residualPenalty r μ) c s δ).domain)
    (hmin : ∀ i < N, ∀ w ∈ (blowup (residualPenalty r μ) c s δ).domain,
      (blowup (residualPenalty r μ) c s δ).value (z (i + 1)) +
        ‖z (i + 1) - (1 + γ * μ)⁻¹ •
          (z i - (γ * ψ (inner ℝ v (z i))) • v)‖ ^ 2 / (2 * (γ / (1 + γ * μ))) ≤
      (blowup (residualPenalty r μ) c s δ).value w +
        ‖w - (1 + γ * μ)⁻¹ • (z i - (γ * ψ (inner ℝ v (z i))) • v)‖ ^ 2 /
          (2 * (γ / (1 + γ * μ)))) :
    IsPGDTrajectory r (liftG ψ c (s + μ • c) v δ) γ N (fun i => c + δ • z i) := by
  have hb : 0 < 1 + γ * μ := by positivity
  refine ⟨fun i hi => hdom i hi, ?_⟩
  intro i hi y hy
  let w := δ⁻¹ • (y - c)
  have hw : c + δ • w = y := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hδ), one_smul, add_sub_cancel]
  have hwdom : w ∈ (blowup (residualPenalty r μ) c s δ).domain := by
    change c + δ • w ∈ r.domain
    rwa [hw]
  have hid (z' : Space d) : (c + δ • z') -
      ((c + δ • z i) - γ • liftG ψ c (s + μ • c) v δ (c + δ • z i)) =
        δ • (z' - (z i - (γ * ψ (inner ℝ v (z i))) • v)) - γ • (s + μ • c) := by
    dsimp [liftG]
    rw [add_sub_cancel_left, real_inner_smul_right, mul_div_cancel_left₀ _ (ne_of_gt hδ)]
    module
  rw [← hw, hid, hid]
  have H := prox_difference r μ γ c s (z i - (γ * ψ (inner ℝ v (z i))) • v)
    δ (ne_of_gt hδ) (ne_of_gt hγ) (ne_of_gt hb) (z (i + 1)) w
  have Hmin := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg δ) (sub_nonpos.mpr (hmin i hi w hwdom))
  rw [← H] at Hmin
  exact sub_nonpos.mp Hmin

private lemma input_perturbation {d : ℕ} (ψ : ℝ → ℝ) (L γ b : ℝ)
    (hL : 0 < L) (hγ : 0 < γ) (hb : 0 < b)
    (hlip : ∀ x y, |ψ x - ψ y| ≤ L * |x - y|)
    (v z : Space d) (hv : ‖v‖ = 1) (t t' : ℝ) (ht : b * t' = t - γ * ψ t) :
    ‖b⁻¹ • (z - (γ * ψ (inner ℝ v z)) • v) - t' • v‖ ≤
      (b⁻¹ * (1 + γ * L)) * ‖z - t • v‖ := by
  have hin : inner ℝ v (z - t • v) = inner ℝ v z - t := by
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hproj : |inner ℝ v z - t| ≤ ‖z - t • v‖ := by
    have H := abs_real_inner_le_norm v (z - t • v)
    rwa [hin, hv, one_mul] at H
  have hgrad : |ψ (inner ℝ v z) - ψ t| ≤ L * ‖z - t • v‖ :=
    (hlip _ _).trans (mul_le_mul_of_nonneg_left hproj hL.le)
  have hvec : t' • v = b⁻¹ • ((t - γ * ψ t) • v) := by
    rw [← ht, smul_smul, inv_mul_cancel_left₀ (ne_of_gt hb)]
  rw [hvec, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
  have heq : (z - (γ * ψ (inner ℝ v z)) • v) - ((t - γ * ψ t) • v) =
      (z - t • v) - (γ * (ψ (inner ℝ v z) - ψ t)) • v := by module
  rw [heq]
  have hn := norm_sub_le (z - t • v) ((γ * (ψ (inner ℝ v z) - ψ t)) • v)
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hγ, hv, mul_one] at hn
  have Hγ := mul_le_mul_of_nonneg_left hgrad hγ.le
  have Hnorm : ‖z - t • v - (γ * (ψ (inner ℝ v z) - ψ t)) • v‖ ≤
      (1 + γ * L) * ‖z - t • v‖ := by nlinarith only [hn, Hγ]
  have H := mul_le_mul_of_nonneg_left Hnorm (inv_nonneg.mpr hb.le)
  nlinarith only [H]

private lemma approximate_trajectory {d : ℕ} (Q : Penalty d)
    (hclosed : IsClosed {z : Space d × ℝ | z.1 ∈ Q.domain ∧ Q.value z.1 ≤ z.2})
    (hne : Q.domain.Nonempty) (hQ : ∀ z ∈ Q.domain, 0 ≤ Q.value z)
    (ψ : ℝ → ℝ) (L γ b ε : ℝ) (hL : 0 < L) (hγ : 0 < γ) (hb : 0 < b)
    (hlip : ∀ x y, |ψ x - ψ y| ≤ L * |x - y|)
    (N : ℕ) (t : ℕ → ℝ) (v : Space d) (hv : ‖v‖ = 1)
    (ht : ∀ i < N, b * t (i + 1) = t i - γ * ψ (t i))
    (hsmall : ∀ i ≤ N, t i • v ∈ Q.domain ∧ Q.value (t i • v) ≤ ε) :
    ∃ z : ℕ → Space d,
      (∀ i ≤ N, z i ∈ Q.domain) ∧
      (∀ i < N, ∀ w ∈ Q.domain,
        Q.value (z (i + 1)) + ‖z (i + 1) - b⁻¹ • (z i - (γ * ψ (inner ℝ v (z i))) • v)‖ ^ 2 /
          (2 * (γ / b)) ≤ Q.value w +
          ‖w - b⁻¹ • (z i - (γ * ψ (inner ℝ v (z i))) • v)‖ ^ 2 / (2 * (γ / b))) ∧
      z 0 = t 0 • v ∧
      (∀ i < N, ‖z (i + 1) - t (i + 1) • v‖ ≤
        2 * (b⁻¹ * (1 + γ * L)) * ‖z i - t i • v‖ + Real.sqrt (2 * (γ / b) * ε)) ∧
      (∀ i < N, Q.value (z (i + 1)) ≤ ε +
        ((b⁻¹ * (1 + γ * L)) * ‖z i - t i • v‖) ^ 2 / (2 * (γ / b))) := by
  have hη : 0 < γ / b := div_pos hγ hb
  choose P hPdom hPmin using (fun u : Space d => nonnegative_prox_exists Q hclosed hne hQ (γ / b) hη u)
  let step := fun z : Space d => P (b⁻¹ • (z - (γ * ψ (inner ℝ v z)) • v))
  let z : ℕ → Space d := fun i => (step^[i]) (t 0 • v)
  have hz0 : z 0 = t 0 • v := rfl
  have hzstep (i : ℕ) : z (i + 1) = step (z i) := by
    exact Function.iterate_succ_apply' step i (t 0 • v)
  have hzdom (i : ℕ) (hi : i ≤ N) : z i ∈ Q.domain := by
    cases i with
    | zero => rw [hz0]; exact (hsmall 0 (by omega)).1
    | succ i => rw [hzstep]; exact hPdom _
  have hzmin (i : ℕ) (hi : i < N) (w : Space d) (hw : w ∈ Q.domain) :
      Q.value (z (i + 1)) + ‖z (i + 1) - b⁻¹ • (z i - (γ * ψ (inner ℝ v (z i))) • v)‖ ^ 2 /
        (2 * (γ / b)) ≤ Q.value w +
        ‖w - b⁻¹ • (z i - (γ * ψ (inner ℝ v (z i))) • v)‖ ^ 2 / (2 * (γ / b)) := by
    rw [hzstep]
    exact hPmin _ w hw
  have hC : 0 ≤ b⁻¹ * (1 + γ * L) := by positivity
  have hcomp (i : ℕ) (hi : i < N) := nonnegative_prox_comparison Q hQ (γ / b) ε hη
    (b⁻¹ • (z i - (γ * ψ (inner ℝ v (z i))) • v)) (z (i + 1)) (t (i + 1) • v)
    (hzdom _ (by omega)) (hsmall _ (by omega)).1 (hsmall _ (by omega)).2 (hzmin i hi)
  have hinput (i : ℕ) (hi : i < N) :=
    input_perturbation ψ L γ b hL hγ hb hlip v (z i) hv (t i) (t (i + 1)) (ht i hi)
  refine ⟨z, hzdom, hzmin, hz0, ?_, ?_⟩
  · intro i hi
    have H := (hcomp i hi).2
    have HI := hinput i hi
    linarith only [H, HI]
  · intro i hi
    have H := (hcomp i hi).1
    have HI := hinput i hi
    have Hsq := sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)) |>.mpr HI
    have Hdiv := div_le_div_of_nonneg_right Hsq (by positivity : 0 ≤ 2 * (γ / b))
    rw [norm_sub_rev] at H
    linarith only [H, Hdiv]

private lemma unit_embedding_limits {d : ℕ} (v z : ℕ → Space d) (hv : ∀ n, ‖v n‖ = 1)
    (t : ℝ) (he : Tendsto (fun n => ‖z n - t • v n‖) atTop (𝓝 0)) :
    Tendsto (fun n => inner ℝ (v n) (z n)) atTop (𝓝 t) ∧
      Tendsto (fun n => ‖z n‖ ^ 2) atTop (𝓝 (t ^ 2)) := by
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ he
    intro n
    have H := abs_real_inner_le_norm (v n) (z n - t • v n)
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv n] at H
    simpa [Real.norm_eq_abs] using H
  · have hn : Tendsto (fun n => ‖z n‖) atTop (𝓝 |t|) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero (fun _ => norm_nonneg _) _ he
      intro n
      have H := abs_norm_sub_norm_le (z n) (t • v n)
      rw [norm_smul, Real.norm_eq_abs, hv n, mul_one] at H
      simpa [Real.norm_eq_abs] using H
    simpa only [sq_abs] using hn.pow 2

theorem solution : QuadraticAttainmentClaim → FlatSegmentsClaim → FixedPenaltySharpnessClaim := by
  intro hquad hflat d r L h N hr hn hL hh hN ε hε
  let μ := bestModulus r
  have hμ : 0 ≤ μ := (pgd_best_modulus d r hr hn).1
  let γ := h / L
  have hγ : 0 < γ := div_pos hh.1 hL
  let b := 1 + γ * μ
  have hb : 0 < b := by dsimp [b]; positivity
  let p := residualPenalty r μ
  have hp : IsPenalty p := (residual_best_zero r hr hn).1
  have hpzero : bestModulus p = 0 := (residual_best_zero r hr hn).2
  obtain ⟨f1, g1, x1, hf1, hx1, hD1, hR1⟩ := hquad L μ h N hL hμ hh hN
  let φ := fun t : ℝ => f1 (scalarE t)
  let ψ := fun t : ℝ => scalarCo (g1 (scalarE t))
  let t := fun i : ℕ => scalarCo (x1 i)
  have hscalar := extract_scalar f1 g1 L hf1
  have hder : ∀ u, HasDerivAt φ (ψ u) u := hscalar.1
  have hconv : ConvexOn ℝ univ φ := hscalar.2.1
  have hlip : ∀ u w, |ψ u - ψ w| ≤ L * |u - w| := hscalar.2.2
  have ht : ∀ i < N, b * t (i + 1) = t i - γ * ψ (t i) := by
    intro i hi
    have H := scalar_target_update f1 g1 μ γ hμ hγ N x1 hx1 i hi
    simpa only [ψ, t, scalarE_co, b] using H
  let Δ := φ (t 0) - φ (t N) + μ / 2 * (t 0 ^ 2 - t N ^ 2)
  have hΔeq : decrease (quadraticPenalty 1 μ) f1 x1 N = Δ := by
    dsimp [decrease, totalValue, quadraticPenalty, Δ, φ, t]
    rw [scalar_norm_sq, scalar_norm_sq, scalarE_co, scalarE_co]
    ring
  have hΔ : 0 < Δ := hΔeq ▸ hD1
  have hReq : curve N h (μ / L) =
      (t (N - 1) - t N) ^ 2 / γ ^ 2 / (L * Δ) := by
    rw [hΔeq] at hR1
    simpa [residualSquared, scalar_norm_sq, scalarCo, t, γ] using hR1
  let M := 1 + ∑ i ∈ Finset.range (N + 1), |t i|
  have hM : 0 < M := by
    have H : 0 ≤ ∑ i ∈ Finset.range (N + 1), |t i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [M]; linarith
  have htM (i : ℕ) (hi : i ≤ N) : t i ∈ Icc (-M) M := by
    have H : |t i| ≤ ∑ j ∈ Finset.range (N + 1), |t j| :=
      Finset.single_le_sum (fun j hj => abs_nonneg (t j)) (Finset.mem_range.mpr (by omega))
    have HH : |t i| ≤ M := by dsimp [M]; linarith
    exact abs_le.mp HH
  let e := fun n : ℕ => 1 / ((n : ℝ) + 1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have Hflat (n : ℕ) := hflat d p hp hn hpzero M hM (e n) (hepos n)
  choose c s v δ hs hδ hv hseg using Hflat
  let Q := fun n => blowup p (c n) (s n) (δ n)
  have hQprop (n : ℕ) := blowup_properties p hp (c n) (s n) (hs n) (δ n) (hδ n)
  have hsmall (n i : ℕ) (hi : i ≤ N) : t i • v n ∈ (Q n).domain ∧ (Q n).value (t i • v n) ≤ e n := by
    have H := hseg n (t i) (htM i hi)
    constructor
    · change c n + δ n • (t i • v n) ∈ p.domain
      simpa only [smul_smul] using H.1
    · change (p.value (c n + δ n • (t i • v n)) - p.value (c n) -
        δ n * inner ℝ (s n) (t i • v n)) / δ n ^ 2 ≤ e n
      simpa only [smul_smul, real_inner_smul_right, mul_assoc] using H.2.2
  have Happrox (n : ℕ) := approximate_trajectory (Q n) (hQprop n).1 (hQprop n).2.1
    (hQprop n).2.2 ψ L γ b (e n) hL hγ hb hlip N t (v n) (hv n) ht (hsmall n)
  choose z hzdom hzmin hz0 hzrec hzQ using Happrox
  let err := fun n i => ‖z n i - t i • v n‖
  have herr (i : ℕ) (hi : i ≤ N) : Tendsto (fun n => err n i) atTop (𝓝 0) := by
    induction i with
    | zero => simpa [err, hz0] using (tendsto_const_nhds (x := (0 : ℝ)))
    | succ i ih =>
      have HH := (ih (by omega)).const_mul (2 * (b⁻¹ * (1 + γ * L)))
      have HS := (helim.const_mul (2 * (γ / b))).sqrt
      have Hlim : Tendsto (fun n => 2 * (b⁻¹ * (1 + γ * L)) * err n i +
          Real.sqrt (2 * (γ / b) * e n)) atTop (𝓝 0) := by simpa using HH.add HS
      exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hzrec n i (by omega)) Hlim
  have hval (i : ℕ) (hi : i ≤ N) : Tendsto (fun n => (Q n).value (z n i)) atTop (𝓝 0) := by
    have H0 (n : ℕ) : 0 ≤ (Q n).value (z n i) := (hQprop n).2.2 _ (hzdom n i hi)
    cases i with
    | zero =>
      apply squeeze_zero H0 _ helim
      intro n
      rw [hz0]
      exact (hsmall n 0 (by omega)).2
    | succ i =>
      have Hlim : Tendsto (fun n => e n +
          ((b⁻¹ * (1 + γ * L)) * err n i) ^ 2 / (2 * (γ / b))) atTop (𝓝 0) := by
        have H := ((herr i (by omega)).const_mul (b⁻¹ * (1 + γ * L))).pow 2
        simpa using helim.add (H.div_const (2 * (γ / b)))
      exact squeeze_zero H0 (fun n => hzQ n i (by omega)) Hlim
  have hcoords (i : ℕ) (hi : i ≤ N) :=
    unit_embedding_limits v (fun n => z n i) hv (t i) (herr i hi)
  let V := fun n i => φ (inner ℝ (v n) (z n i)) + μ / 2 * ‖z n i‖ ^ 2 + (Q n).value (z n i)
  have hV (i : ℕ) (hi : i ≤ N) : Tendsto (fun n => V n i) atTop (𝓝 (φ (t i) + μ / 2 * t i ^ 2)) := by
    have Hφ := (hder (t i)).continuousAt.tendsto.comp (hcoords i hi).1
    simpa [V] using (Hφ.add ((hcoords i hi).2.const_mul (μ / 2))).add (hval i hi)
  let D := fun n => V n 0 - V n N
  have hDlim : Tendsto D atTop (𝓝 Δ) := by
    convert (hV 0 (by omega)).sub (hV N le_rfl) using 1
    dsimp [Δ]
    ring
  have hlast : Tendsto (fun n => ‖z n (N - 1) - z n N - (t (N - 1) - t N) • v n‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ (by
      simpa using (herr (N - 1) (by omega)).add (herr N le_rfl))
    intro n
    have Heq : z n (N - 1) - z n N - (t (N - 1) - t N) • v n =
        (z n (N - 1) - t (N - 1) • v n) - (z n N - t N • v n) := by module
    rw [Heq]
    exact norm_sub_le _ _
  have hnum := (unit_embedding_limits v (fun n => z n (N - 1) - z n N) hv
    (t (N - 1) - t N) hlast).2
  let R := fun n => ‖z n (N - 1) - z n N‖ ^ 2 / γ ^ 2 / (L * D n)
  have hRlim : Tendsto R atTop (𝓝 (curve N h (μ / L))) := by
    rw [hReq]
    exact (hnum.div_const (γ ^ 2)).div (hDlim.const_mul L) (ne_of_gt (mul_pos hL hΔ))
  have hDpos : ∀ᶠ n in atTop, 0 < D n := hDlim.eventually_const_lt hΔ
  have hRclose : ∀ᶠ n in atTop, curve N h (μ / L) - ε < R n :=
    hRlim.eventually_const_lt (by linarith)
  obtain ⟨n, hnD, hnR⟩ := (hDpos.and hRclose).exists
  let fn := liftF φ (c n) (s n + μ • c n) (v n) (δ n)
  let gn := liftG ψ (c n) (s n + μ • c n) (v n) (δ n)
  let xn := fun i => c n + δ n • z n i
  have hfn : SmoothConvex fn gn L := lift_smooth φ ψ hder hconv L hL hlip
    (c n) (s n + μ • c n) (v n) (δ n) (hδ n) (hv n)
  have hxn : IsPGDTrajectory r gn γ N xn := lift_trajectory r μ γ hμ hγ ψ
    (c n) (s n) (v n) (δ n) (hδ n) N (z n) (hzdom n) (hzmin n)
  have hDec : decrease r fn xn N = δ n ^ 2 * D n := by
    dsimp [decrease, xn, fn]
    rw [lifted_total r μ φ (c n) (s n) (v n) (δ n) (ne_of_gt (hδ n)),
      lifted_total r μ φ (c n) (s n) (v n) (δ n) (ne_of_gt (hδ n))]
    dsimp [D, V, Q, p]
    ring
  have hRes : residualSquared γ xn N = δ n ^ 2 * ‖z n (N - 1) - z n N‖ ^ 2 / γ ^ 2 := by
    have Hvec : xn (N - 1) - xn N = δ n • (z n (N - 1) - z n N) := by dsimp [xn]; module
    rw [residualSquared, Hvec, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hRatio : residualSquared γ xn N / (L * decrease r fn xn N) = R n := by
    rw [hDec, hRes]
    dsimp [R]
    field_simp [ne_of_gt (hδ n)]
    <;> ring
  refine ⟨R n, ?_, hnR⟩
  refine ⟨fn, gn, xn, hfn, hxn, ?_, hRatio.symm⟩
  rw [hDec]
  exact mul_pos (sq_pos_of_pos (hδ n)) hnD
