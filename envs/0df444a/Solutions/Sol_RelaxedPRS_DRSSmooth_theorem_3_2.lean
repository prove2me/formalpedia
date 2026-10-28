-- Prove2me | solution 1 for RelaxedPRS.DRSSmooth.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T15:31:04.548852+00:00
-- url     : https://prove2.me/submissions/60d876d7-ab8a-4108-85fe-e3a6ba92baf7

import Mathlib
import Definitions.Def_RelaxedPRS_DRSSmooth_Setting

-- Complete module: DSProof/SharedBasics.lean
open scoped RealInnerProductSpace
open Filter Topology

-- Complete module: DSProof/MonotoneLittleO.lean

namespace RelaxedPRS.DRSSmooth.DSFresh
open Filter Topology Asymptotics

 theorem antitone_summable_littleO {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (hm : Antitone b) (hs : Summable b) :
    b =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  apply isLittleO_iff.2
  intro ε hε
  have ht := tendsto_sum_nat_add b
  obtain ⟨N, hN⟩ := ((tendsto_order.1 ht).2 (ε / 2) (by positivity)).exists
  filter_upwards [eventually_ge_atTop (2 * N + 1)] with k hk
  have hNk : N ≤ k + 1 := by omega
  have htail : ((k + 1 - N : ℕ) : ℝ) * b k ≤ ∑' i, b (i + N) := by
    calc
      ((k + 1 - N : ℕ) : ℝ) * b k = ∑ i ∈ Finset.range (k + 1 - N), b k := by simp
      _ ≤ ∑ i ∈ Finset.range (k + 1 - N), b (i + N) := by
        apply Finset.sum_le_sum
        intro i hi
        apply hm
        have := Finset.mem_range.1 hi
        omega
      _ ≤ ∑' i, b (i + N) :=
        ((summable_nat_add_iff N).2 hs).sum_le_tsum _ (fun _ _ => hb _)
  have hcount : (k : ℝ) + 1 ≤ 2 * ((k + 1 - N : ℕ) : ℝ) := by
    have hn : k + 1 ≤ 2 * (k + 1 - N) := by omega
    exact_mod_cast hn
  have hprod : ((k : ℝ) + 1) * b k ≤ ε := by
    have hh := mul_le_mul_of_nonneg_right hcount (hb k)
    nlinarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hb k),
    abs_of_nonneg (by positivity : 0 ≤ 1 / ((k : ℝ) + 1))]
  rw [mul_one_div]
  exact (le_div_iff₀ (by positivity : 0 < (k : ℝ) + 1)).2 (by nlinarith)

 theorem dominated_littleO {b e : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (he : ∀ k, 0 ≤ e k) (hb : ∀ k, 0 ≤ b k)
    (hm : Antitone b) (hs : Summable b) (hdom : ∀ k, c * e k ≤ b k) :
    e =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  have hl := antitone_summable_littleO hb hm hs
  apply isLittleO_iff.2
  intro ε hε
  filter_upwards [hl.bound (mul_pos hc hε)] with k hk
  rw [Real.norm_eq_abs, abs_of_nonneg (hb k)] at hk
  rw [Real.norm_eq_abs, abs_of_nonneg (he k)]
  have hd := hdom k
  nlinarith

end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/RunningMinimum.lean

namespace RelaxedPRS.DRSSmooth.DSFresh
open Filter Asymptotics

noncomputable def runningMin (e : ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one e

theorem runningMin_le (e : ℕ → ℝ) {i k : ℕ} (hi : i ≤ k) : runningMin e k ≤ e i := by
  exact Finset.inf'_le _ (Finset.mem_range.2 (by omega))

theorem runningMin_nonneg {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) (k : ℕ) : 0 ≤ runningMin e k := by
  exact Finset.le_inf' _ _ (fun i _ => he i)

theorem runningMin_antitone (e : ℕ → ℝ) : Antitone (runningMin e) := by
  intro i j hij
  apply Finset.le_inf'
  intro k hk
  exact runningMin_le e (by have := Finset.mem_range.1 hk; omega)

theorem runningMin_littleO {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) (hs : Summable e) :
    runningMin e =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  apply antitone_summable_littleO (runningMin_nonneg he) (runningMin_antitone e)
  exact Summable.of_nonneg_of_le (runningMin_nonneg he) (fun k => runningMin_le e le_rfl) hs

end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/SequenceBudgets.lean

namespace RelaxedPRS.DRSSmooth.DSFresh
open Filter Asymptotics

theorem sum_recurrence {e D G : ℕ → ℝ} {c C : ℝ}
    (hstep : ∀ k, c * e k ≤ D k - D (k + 1) + C * G k) (N : ℕ) :
    c * (∑ i ∈ Finset.range N, e i) ≤ D 0 - D N + C * (∑ i ∈ Finset.range N, G i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hh := hstep N
    nlinarith

theorem partial_sum_bound {e D G : ℕ → ℝ} {c C B : ℝ}
    (hc : 0 < c) (hD : ∀ k, 0 ≤ D k) (hC : 0 ≤ C)
    (hstep : ∀ k, c * e k ≤ D k - D (k + 1) + C * G k)
    (hG : ∀ N, (∑ i ∈ Finset.range N, G i) ≤ B) (N : ℕ) :
    (∑ i ∈ Finset.range N, e i) ≤ (D 0 + C * B) / c := by
  apply (le_div_iff₀ hc).2
  have hh := sum_recurrence hstep N
  have hg := mul_le_mul_of_nonneg_left (hG N) hC
  nlinarith [hD N]

theorem partial_sum_nonpos {e D G : ℕ → ℝ} {c C : ℝ}
    (hc : 0 < c) (hD : ∀ k, 0 ≤ D k) (hG : ∀ k, 0 ≤ G k) (hC : C ≤ 0)
    (hstep : ∀ k, c * e k ≤ D k - D (k + 1) + C * G k) (N : ℕ) :
    (∑ i ∈ Finset.range N, e i) ≤ D 0 / c := by
  apply (le_div_iff₀ hc).2
  have hh := sum_recurrence hstep N
  have hg : C * (∑ i ∈ Finset.range N, G i) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hC (Finset.sum_nonneg (fun i _ => hG i))
  nlinarith [hD N]

theorem recurrence_summable {e D G : ℕ → ℝ} {c C B : ℝ}
    (hc : 0 < c) (he : ∀ k, 0 ≤ e k) (hD : ∀ k, 0 ≤ D k) (hG0 : ∀ k, 0 ≤ G k)
    (hstep : ∀ k, c * e k ≤ D k - D (k + 1) + C * G k)
    (hG : ∀ N, (∑ i ∈ Finset.range N, G i) ≤ B) : Summable e := by
  have hstep' : ∀ k, c * e k ≤ D k - D (k + 1) + max C 0 * G k := by
    intro k
    exact (hstep k).trans (add_le_add_right (mul_le_mul_of_nonneg_right (le_max_left C 0) (hG0 k)) _)
  exact summable_of_sum_range_le he (partial_sum_bound hc hD (le_max_right C 0) hstep' hG)

theorem runningMin_bound {e : ℕ → ℝ} {B : ℝ} (hB : ∀ N, (∑ i ∈ Finset.range N, e i) ≤ B)
    (k : ℕ) : runningMin e k ≤ B / ((k : ℝ) + 1) := by
  apply (le_div_iff₀ (by positivity : 0 < (k : ℝ) + 1)).2
  have hm : (∑ _i ∈ Finset.range (k + 1), runningMin e k) ≤
      ∑ i ∈ Finset.range (k + 1), e i := by
    apply Finset.sum_le_sum
    intro i hi
    exact runningMin_le e (by have := Finset.mem_range.1 hi; omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hm
  nlinarith [hB (k + 1)]

theorem antitone_budget_pointwise {b D : ℕ → ℝ}
    (hD : ∀ k, 0 ≤ D k) (hm : Antitone b)
    (hstep : ∀ k, b k ≤ D k - D (k + 1)) (k : ℕ) :
    b k ≤ D 0 / ((k : ℝ) + 1) := by
  have hs : ∀ N, (∑ i ∈ Finset.range N, b i) ≤ D 0 := by
    intro N
    have hh := sum_recurrence (e := b) (D := D) (G := fun _ => 0) (c := 1) (C := 0)
      (by simpa only [one_mul, zero_mul, add_zero] using hstep) N
    simp only [one_mul, zero_mul, add_zero] at hh
    linarith [hD N]
  apply (le_div_iff₀ (by positivity : 0 < (k : ℝ) + 1)).2
  have hh : (∑ _i ∈ Finset.range (k + 1), b k) ≤ ∑ i ∈ Finset.range (k + 1), b i := by
    apply Finset.sum_le_sum
    intro i hi
    apply hm
    have := Finset.mem_range.1 hi
    omega
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hh
  nlinarith [hs (k + 1)]

end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/ScalarRoots.lean

namespace RelaxedPRS.DRSSmooth.DSFresh

theorem rho_quadratic {ρ : ℝ} (hρ : 0 < ρ ∧ ρ ^ 3 - 2 * ρ - 1 = 0) :
    1 < ρ ∧ ρ ^ 2 = ρ + 1 := by
  have hprod : (ρ + 1) * (ρ ^ 2 - ρ - 1) = 0 := by nlinarith [hρ.2]
  have hq : ρ ^ 2 - ρ - 1 = 0 := (mul_eq_zero.mp hprod).resolve_left (by linarith [hρ.1])
  have hr : 1 < ρ := by
    by_contra hn
    have hle : ρ ≤ 1 := le_of_not_gt hn
    have hs := mul_le_mul_of_nonneg_left hle hρ.1.le
    nlinarith
  exact ⟨hr, by linarith⟩

theorem rho_poly_sign {ρ t : ℝ} (hρ : 0 < ρ ∧ ρ ^ 3 - 2 * ρ - 1 = 0)
    (ht : 0 < t) :
    (t ≤ ρ → t ^ 3 - 2 * t - 1 ≤ 0) ∧
    (ρ ≤ t → 0 ≤ t ^ 3 - 2 * t - 1) := by
  obtain ⟨hr, hq⟩ := rho_quadratic hρ
  have he : t ^ 3 - 2 * t - 1 = (t + 1) * ((t - ρ) * (t + ρ - 1)) := by
    nlinarith [congrArg (fun z : ℝ => (t + 1) * z) hq]
  rw [he]
  constructor
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) (by linarith))
  · intro h
    exact mul_nonneg (by linarith) (mul_nonneg (sub_nonneg.2 h) (by linarith))

theorem kappa_gt_one {κ : ℝ} (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) :
    1 < κ := by
  by_contra hn
  have hk : κ ≤ 1 := le_of_not_gt hn
  have hs := mul_le_mul_of_nonneg_left hk hκ.1.le
  have hc := mul_le_mul_of_nonneg_left hk (sq_nonneg κ)
  nlinarith [hκ.2]

theorem kappa_poly_nonpos {κ t : ℝ}
    (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0)
    (ht : 1 ≤ t) (htκ : t ≤ κ) : t ^ 3 + t ^ 2 - 2 * t - 1 ≤ 0 := by
  have hk := kappa_gt_one hκ
  have hpos : 0 ≤ t ^ 2 + t * κ + κ ^ 2 + t + κ - 2 := by
    have htk : 0 ≤ t * κ := mul_nonneg (by linarith) hκ.1.le
    nlinarith [sq_nonneg t, sq_nonneg κ]
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 htκ) hpos
  nlinarith [hκ.2]

end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/ScalarTheta.lean

namespace RelaxedPRS.DRSSmooth.DSFresh

theorem theta_normalized {κ t : ℝ}
    (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0)
    (ht : 0 < t) (htκ : t < κ) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ θ * t ^ 2 ≤ 2 * t - t ^ 3 ∧
      (1 - θ) * t ^ 2 ≤ 1 := by
  by_cases ht1 : t ≤ 1
  · refine ⟨0, le_rfl, by norm_num, ?_, ?_⟩
    · have hs := mul_le_mul_of_nonneg_left ht1 ht.le
      have hc := mul_le_mul_of_nonneg_left ht1 (sq_nonneg t)
      nlinarith
    · have hs := mul_self_le_mul_self ht.le ht1
      nlinarith
  · have ht1' : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    have hs : 0 < t ^ 2 := sq_pos_of_pos ht
    have hs1 : 1 ≤ t ^ 2 := by nlinarith
    have hinv : 1 / t ^ 2 ≤ 1 := (div_le_one hs).2 hs1
    have he : (1 - (1 - 1 / t ^ 2)) * t ^ 2 = 1 := by
      field_simp
      ring
    have hp := kappa_poly_nonpos hκ ht1' htκ.le
    have hinv0 : 0 ≤ 1 / t ^ 2 := by positivity
    refine ⟨1 - 1 / t ^ 2, by linarith, by linarith, ?_, he.le⟩
    have he' : (1 - 1 / t ^ 2) * t ^ 2 = t ^ 2 - 1 := by field_simp
    rw [he']
    linarith

theorem exists_theta {β γ κ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) (hγκ : γ < κ * β) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ θ * γ ^ 2 ≤ 2 * γ * β - γ ^ 3 / β ∧
      (1 - θ) * γ ^ 2 / β ^ 2 ≤ 1 := by
  obtain ⟨θ, hθ0, hθ1, hc, hd⟩ := theta_normalized hκ (div_pos hγ hβ)
    ((div_lt_iff₀ hβ).2 hγκ)
  refine ⟨θ, hθ0, hθ1, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right hc (sq_nonneg β)
    have he1 : θ * (γ / β) ^ 2 * β ^ 2 = θ * γ ^ 2 := by field_simp
    have he2 : (2 * (γ / β) - (γ / β) ^ 3) * β ^ 2 =
        2 * γ * β - γ ^ 3 / β := by field_simp
    rwa [he1, he2] at h
  · simpa only [div_pow, mul_div_assoc] using hd

theorem best_coefficient_sign {β γ ρ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hρ : 0 < ρ ∧ ρ ^ 3 - 2 * ρ - 1 = 0) :
    (γ < ρ * β → γ ^ 3 / β - 2 * γ * β - β ^ 2 ≤ 0) ∧
    (ρ * β ≤ γ → 0 ≤ γ ^ 3 / β - 2 * γ * β - β ^ 2) := by
  have he : ((γ / β) ^ 3 - 2 * (γ / β) - 1) * β ^ 2 =
      γ ^ 3 / β - 2 * γ * β - β ^ 2 := by field_simp
  obtain ⟨hl, hu⟩ := rho_poly_sign hρ (div_pos hγ hβ)
  constructor
  · intro hg
    have hh := mul_nonpos_of_nonpos_of_nonneg (hl ((div_lt_iff₀ hβ).2 hg).le) (sq_nonneg β)
    rwa [he] at hh
  · intro hg
    have hh := mul_nonneg (hu ((le_div_iff₀ hβ).2 hg)) (sq_nonneg β)
    rwa [he] at hh

end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/AbstractRates.lean

namespace RelaxedPRS.DRSSmooth.DSFresh
open Filter Asymptotics

theorem best_rates {e D G : ℕ → ℝ} {β γ ρ Z : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hρ : 0 < ρ ∧ ρ ^ 3 - 2 * ρ - 1 = 0)
    (he : ∀ k, 0 ≤ e k) (hD : ∀ k, 0 ≤ D k) (hG : ∀ k, 0 ≤ G k)
    (hbudget : ∀ N, (∑ i ∈ Finset.range N, G i) ≤ Z / (β ^ 2 + γ ^ 2))
    (hstep : ∀ k, 2 * γ * e k ≤ D k - D (k + 1) +
      (γ ^ 3 / β - 2 * γ * β - β ^ 2) * G k) :
    (γ < ρ * β → ∀ k, runningMin e k ≤ D 0 / (2 * γ * ((k : ℝ) + 1))) ∧
    (ρ * β ≤ γ → ∀ k, runningMin e k ≤
      (D 0 + 1 / (β ^ 2 + γ ^ 2) * (γ ^ 3 / β - 2 * γ * β - β ^ 2) * Z) /
        (2 * γ * ((k : ℝ) + 1))) ∧
    runningMin e =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  have hc : 0 < 2 * γ := by positivity
  obtain ⟨hl, hu⟩ := best_coefficient_sign hβ hγ hρ
  refine ⟨?_, ?_, ?_⟩
  · intro hg k
    have hh := runningMin_bound (partial_sum_nonpos hc hD hG (hl hg) hstep) k
    simpa only [div_div] using hh
  · intro hg k
    have hh := runningMin_bound (partial_sum_bound hc hD (hu hg) hstep hbudget) k
    convert hh using 1
    rw [div_div]
    ring
  · exact runningMin_littleO he (recurrence_summable hc he hD hG hstep hbudget)

theorem pointwise_rates {e b D : ℕ → ℝ} {γ : ℝ}
    (hγ : 0 < γ) (he : ∀ k, 0 ≤ e k) (hb : ∀ k, 0 ≤ b k)
    (hD : ∀ k, 0 ≤ D k) (hm : Antitone b)
    (hstep : ∀ k, b k ≤ D k - D (k + 1)) (hdom : ∀ k, 2 * γ * e k ≤ b k) :
    (∀ k, e k ≤ D 0 / (2 * γ * ((k : ℝ) + 1))) ∧
    e =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
  have hc : 0 < 2 * γ := by positivity
  have hs : Summable b := by
    apply summable_of_sum_range_le hb (c := D 0)
    intro N
    have hh := sum_recurrence (e := b) (D := D) (G := fun _ => 0) (c := 1) (C := 0)
      (by simpa only [one_mul, zero_mul, add_zero] using hstep) N
    simp only [one_mul, zero_mul, add_zero] at hh
    linarith [hD N]
  refine ⟨?_, dominated_littleO hc he hb hm hs hdom⟩
  intro k
  have hh := (hdom k).trans (antitone_budget_pointwise hD hm hstep k)
  have he' : e k ≤ (D 0 / ((k : ℝ) + 1)) / (2 * γ) :=
    (le_div_iff₀ hc).2 (by nlinarith)
  convert he' using 1
  rw [div_div]
  congr 1
  ring

end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/ProxFinite.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma prox_finite {f : H → EReal} (hf : IsProperClosedConvex f) {γ : ℝ} {P : H → H}
    (hP : IsProx γ f P) (z : H) : f (P z) ≠ ⊤ := by
  obtain ⟨u,hu⟩ := hf.2.1
  have h := hP z u
  have ht := EReal.add_lt_top hu (EReal.coe_ne_top (‖u-z‖^2/(2*γ)))
  intro he
  rw [he,EReal.top_add_coe] at h
  exact (not_lt_of_ge h) ht
lemma prox_compare {f : H → EReal} (hf : IsProperClosedConvex f) {γ : ℝ} {P : H → H}
    (hP : IsProx γ f P) (z u : H) (hu : f u ≠ ⊤) :
    (f (P z)).toReal+‖P z-z‖^2/(2*γ) ≤ (f u).toReal+‖u-z‖^2/(2*γ) := by
  have h := hP z u
  rw [← EReal.coe_toReal (prox_finite hf hP z) (hf.1 _),
    ← EReal.coe_toReal hu (hf.1 u),← EReal.coe_add,← EReal.coe_add,EReal.coe_le_coe_iff] at h
  exact h
lemma finite_segment {f : H → EReal} (hf : IsProperClosedConvex f) {p u : H}
    (hp : f p ≠ ⊤) (hu : f u ≠ ⊤) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1-t) • p+t • u) ≤ (((1-t)*(f p).toReal+t*(f u).toReal : ℝ) : EReal) := by
  have h := hf.2.2.2 (x := (p,(f p).toReal)) (y := (u,(f u).toReal))
    (by exact EReal.le_coe_toReal hp) (by exact EReal.le_coe_toReal hu)
    (sub_nonneg.mpr ht1) ht (by ring)
  exact h
lemma prox_support_approx {f : H → EReal} (hf : IsProperClosedConvex f) {γ : ℝ}
    (hγ : 0 < γ) {P : H → H} (hP : IsProx γ f P) (z u : H) (hu : f u ≠ ⊤)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (f (P z)).toReal+inner ℝ (u-P z) (γ⁻¹ • (z-P z)) ≤
      (f u).toReal+t/(2*γ)*‖u-P z‖^2 := by
  let p := P z
  let v := (1-t) • p+t • u
  have hv := finite_segment hf (prox_finite hf hP z) hu ht.le ht1
  have hvf : f v ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hv
  have hc := prox_compare hf hP z v hvf
  have hv' : (f v).toReal ≤ (1-t)*(f p).toReal+t*(f u).toReal := by
    rw [← EReal.coe_toReal hvf (hf.1 v), EReal.coe_le_coe_iff] at hv
    exact hv
  have he : ‖v-z‖^2=‖p-z‖^2+2*t*inner ℝ (p-z) (u-p)+t^2*‖u-p‖^2 := by
    have hh : v-z=(p-z)+t • (u-p) := by dsimp [v]; module
    rw [hh]
    simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right]
    rw [real_inner_comm (u-p) (p-z)]
    ring
  rw [he] at hc
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2*γ by positivity)
  field_simp at hm
  have hv2 := mul_le_mul_of_nonneg_left hv' (show 0 ≤ 2*γ by positivity)
  dsimp [p] at hm hv2
  have hn : 0 ≤ t*(2*γ*((f u).toReal-(f p).toReal)+2*inner ℝ (p-z) (u-p)+t*‖u-p‖^2) := by
    dsimp [p]
    nlinarith only [hm,hv2]
  have hn' := (mul_nonneg_iff_of_pos_left ht).mp hn
  simp only [real_inner_smul_right]
  rw [show z-P z=-(P z-z) by abel,inner_neg_right, ← real_inner_comm (u-P z) (P z-z)]
  dsimp [p] at hn'
  apply (mul_le_mul_iff_right₀ (show 0 < 2*γ by positivity)).mp
  field_simp
  nlinarith only [hn']
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/ProxSubgradient.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma prox_support {f : H → EReal} (hf : IsProperClosedConvex f) {γ : ℝ}
    (hγ : 0 < γ) {P : H → H} (hP : IsProx γ f P) (z u : H) (hu : f u ≠ ⊤) :
    (f (P z)).toReal+inner ℝ (u-P z) (γ⁻¹ • (z-P z)) ≤ (f u).toReal := by
  have ht : Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun k : ℕ => (f u).toReal+(1/((k : ℝ)+1))/(2*γ)*‖u-P z‖^2)
      atTop (𝓝 ((f u).toReal)) := by
    simpa using tendsto_const_nhds.add ((ht.div_const (2*γ)).mul_const (‖u-P z‖^2))
  apply ge_of_tendsto hl
  filter_upwards [] with k
  exact prox_support_approx hf hγ hP z u hu (t := 1/((k : ℝ)+1)) (by positivity)
    ((div_le_one (by positivity : 0 < (k : ℝ)+1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k]))
lemma prox_subgradient {f : H → EReal} (hf : IsProperClosedConvex f) {γ : ℝ}
    (hγ : 0 < γ) {P : H → H} (hP : IsProx γ f P) (z : H) :
    γ⁻¹ • (z-P z) ∈ MoreauProx.Characterization.subgrad f (P z) := by
  refine ⟨hf.1 _,prox_finite hf hP z,fun u => ?_⟩
  by_cases hu : f u=⊤
  · rw [hu]; exact le_top
  · rw [← EReal.coe_toReal (prox_finite hf hP z) (hf.1 _),
      ← EReal.coe_toReal hu (hf.1 u),← EReal.coe_add,EReal.coe_le_coe_iff]
    exact prox_support hf hγ hP z u hu
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/ScalarSmooth.lean
namespace RelaxedPRS.DRSSmooth.DSFresh

theorem scalar_descent (f f' : ℝ → ℝ) (L : ℝ) (hd : ∀ z, HasDerivAt f (f' z) z)
    (hL : ∀ a b, |f' a-f' b| ≤ L*|a-b|) (a b : ℝ) :
    f b ≤ f a + f' a*(b-a) + L/2*(b-a)^2 := by
  let q : ℝ → ℝ := fun z => f z - f a - f' a*(z-a) - L/2*(z-a)^2
  have hq (z : ℝ) : HasDerivAt q (f' z-f' a-L*(z-a)) z := by
    have h := (((hd z).sub_const (f a)).sub (((hasDerivAt_id z).sub_const a).const_mul (f' a))).sub
      ((((hasDerivAt_id z).sub_const a).pow 2).const_mul (L/2)) 
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hc : Continuous q := continuous_iff_continuousAt.mpr fun z => (hq z).continuousAt
  have hdiff : Differentiable ℝ q := fun z => (hq z).differentiableAt
  have hqa : q a = 0 := by simp [q]
  rcases le_total a b with hab | hba
  · have hm : AntitoneOn q (Set.Ici a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have haz : a ≤ z := (interior_subset hz)
      have h := (abs_le.mp (hL z a)).2
      rw [abs_of_nonneg (sub_nonneg.mpr haz)] at h
      linarith
    have h := hm (by simp) hab hab
    rw [hqa] at h
    dsimp [q] at h
    linarith
  · have hm : MonotoneOn q (Set.Iic a) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have hza : z ≤ a := (interior_subset (s := Set.Iic a) hz)
      have h := (abs_le.mp (hL z a)).1
      rw [abs_of_nonpos (sub_nonpos.mpr hza)] at h
      linarith
    have h := hm hba (by simp) hba
    rw [hqa] at h
    dsimp [q] at h
    linarith

end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/SmoothDescent.lean
open scoped RealInnerProductSpace
namespace RelaxedPRS.DRSSmooth.DSFresh
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma smooth_descent (f : H → ℝ) (L : ℝ)
    (hf : Differentiable ℝ f)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x-y‖)
    (x y : H) :
    f y ≤ f x + inner ℝ (gradient f x) (y-x) + L/2*‖y-x‖^2 := by
  let d := y-x
  let g : ℝ → ℝ := fun t => f (x+t • d)
  let g' : ℝ → ℝ := fun t => inner ℝ (gradient f (x+t • d)) d
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    exact ((hf _).hasGradientAt.hasFDerivAt.comp_hasDerivAt t (hd t))
  have hl (s t : ℝ) : |g' s - g' t| ≤ (L*‖d‖^2)*|s-t| := by
    dsimp [g']
    rw [← inner_sub_left]
    calc
      |inner ℝ (gradient f (x+s • d)-gradient f (x+t • d)) d| ≤
          ‖gradient f (x+s • d)-gradient f (x+t • d)‖*‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L*‖(x+s • d)-(x+t • d)‖)*‖d‖ := mul_le_mul_of_nonneg_right (hL _ _) (norm_nonneg _)
      _ = (L*‖d‖^2)*|s-t| := by
        rw [show (x+s • d)-(x+t • d) = (s-t) • d by module]
        rw [norm_smul, Real.norm_eq_abs]
        ring
  have h := scalar_descent g g' (L*‖d‖^2) hg hl 0 1
  simp only [g, g', zero_smul, add_zero, one_smul, sub_zero, one_pow, mul_one] at h
  have he : x + (y-x) = y := by abel
  dsimp [d] at h
  rw [he] at h
  nlinarith [h]
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/ConvexGradient.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma convex_gradient {g : H → ℝ} (hc : ConvexOn ℝ Set.univ g) (hd : Differentiable ℝ g)
    (x y : H) : g x+inner ℝ (gradient g x) (y-x) ≤ g y := by
  let q : ℝ → ℝ := fun t => g (x+t • (y-x))
  have hq : ConvexOn ℝ Set.univ q := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ u v hu hv huv
    have h := hc.2 (Set.mem_univ (x+a • (y-x))) (Set.mem_univ (x+b • (y-x))) hu hv huv
    dsimp [q]
    simp only [smul_eq_mul] at h ⊢
    convert h using 1
    congr 1
    match_scalars
    all_goals nlinarith [huv]
  have hder : HasDerivAt q (inner ℝ (gradient g x) (y-x)) 0 := by
    have hh := (hd (x+(0 : ℝ) • (y-x))).hasGradientAt.hasFDerivAt.comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℝ)).smul_const (y-x)).const_add x)
    simpa only [q, one_smul, id_eq, zero_smul, add_zero, Function.comp_def, InnerProductSpace.toDual_apply_apply] using hh
  have h := hq.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num) hder
  simp only [slope, q, zero_smul, add_zero, one_smul, sub_zero, inv_one, one_smul] at h
  rw [show x+(y-x)=y by abel] at h
  change inner ℝ (gradient g x) (y-x) ≤ g y-g x at h
  linarith
lemma smooth_bregman {g : H → ℝ} {β : ℝ} (hb : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g) (x y : H) :
    β/2*‖gradient g x-gradient g y‖^2 ≤ g x-g y-inner ℝ (gradient g y) (x-y) := by
  let d := gradient g x-gradient g y
  have hu := smooth_descent g β⁻¹ hg.2.1 hg.2.2 x (x-β • d)
  have hl := convex_gradient hg.1 hg.2.1 y (x-β • d)
  have he : x-β • d-x = -β • d := by module
  rw [he] at hu
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at hu
  rw [show x-β • d-y = (x-y)-β • d by module, inner_sub_right, real_inner_smul_right] at hl
  have hi : inner ℝ (gradient g x) d-inner ℝ (gradient g y) d = ‖d‖^2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq d
  have heq : β⁻¹/2*β^2 = β/2 := by field_simp
  have hu' : g (x-β • d) ≤ g x-β*inner ℝ (gradient g x) d+β/2*‖d‖^2 := by
    nlinarith only [hu, congrArg (fun t : ℝ => t*‖d‖^2) heq]
  dsimp [d] at hi hu'
  nlinarith only [hu',hl,congrArg (fun t : ℝ => β*t) hi]
lemma cocoercive {g : H → ℝ} {β : ℝ} (hb : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g) (x y : H) :
    β*‖gradient g x-gradient g y‖^2 ≤ inner ℝ (gradient g x-gradient g y) (x-y) := by
  have h1 := smooth_bregman hb hg x y
  have h2 := smooth_bregman hb hg y x
  rw [norm_sub_rev (gradient g y) (gradient g x), show y-x=-(x-y) by abel,
    inner_neg_right] at h2
  rw [inner_sub_left]
  linarith
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/SmoothProx.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
omit [CompleteSpace H] in
lemma real_proper {g : H → ℝ} (hc : ConvexOn ℝ Set.univ g) (hd : Continuous g) :
    IsProperClosedConvex (gE g) := by
  refine ⟨fun x => EReal.coe_ne_bot _,⟨0,EReal.coe_ne_top _⟩,
    (continuous_coe_real_ereal.comp hd).lowerSemicontinuous,?_⟩
  intro p hp q hq a b ha hb hab
  change (g (a • p.1+b • q.1) : EReal) ≤ ((a*p.2+b*q.2 : ℝ) : EReal)
  apply EReal.coe_le_coe_iff.mpr
  change (g p.1 : EReal) ≤ (p.2 : EReal) at hp
  change (g q.1 : EReal) ≤ (q.2 : EReal) at hq
  have hp' := EReal.coe_le_coe_iff.mp hp
  have hq' := EReal.coe_le_coe_iff.mp hq
  exact (hc.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab).trans
    (add_le_add (mul_le_mul_of_nonneg_left hp' ha) (mul_le_mul_of_nonneg_left hq' hb))
lemma support_eq_gradient {g : H → ℝ} (hd : Differentiable ℝ g) (p v : H)
    (hv : ∀u,g p+inner ℝ (u-p) v ≤ g u) : v=gradient g p := by
  let d := gradient g p-v
  let q : ℝ → ℝ := fun t => g (p+t • d)-t*inner ℝ d v
  have hl : IsLocalMin q 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hv (p+t • d)
    rw [add_sub_cancel_left,real_inner_smul_left] at h
    dsimp [q]
    simp only [zero_smul,add_zero,zero_mul,sub_zero]
    linarith
  have hh := (hd (p+(0:ℝ) • d)).hasGradientAt.hasFDerivAt.comp_hasDerivAt 0
    (((hasDerivAt_id (0:ℝ)).smul_const d).const_add p)
  have hq : HasDerivAt q (inner ℝ (gradient g p) d-inner ℝ d v) 0 := by
    convert hh.sub ((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ d v)) using 1
    all_goals try rfl
    all_goals simp only [one_smul,zero_smul,add_zero,InnerProductSpace.toDual_apply_apply,one_mul]

  have he := hq.deriv.symm.trans hl.deriv_eq_zero
  rw [← real_inner_comm d v,← inner_sub_left] at he
  change inner ℝ d d=0 at he
  have hz := (inner_self_eq_zero).mp he
  dsimp [d] at hz
  exact (sub_eq_zero.mp hz).symm
lemma prox_gradient {g : H → ℝ} {β γ : ℝ} (hg : IsSmoothConvex β g) (hγ : 0 < γ)
    {P : H → H} (hP : IsProx γ (gE g) P) (z : H) :
    γ⁻¹ • (z-P z)=gradient g (P z) := by
  apply support_eq_gradient hg.2.1
  intro u
  have h := prox_support (real_proper hg.1 hg.2.1.continuous) hγ hP z u (EReal.coe_ne_top _)
  simpa only [gE,EReal.toReal_coe] using h
lemma prox_gradient_identity {g : H → ℝ} {β γ : ℝ} (hg : IsSmoothConvex β g) (hγ : 0 < γ)
    {P : H → H} (hP : IsProx γ (gE g) P) (z : H) : z=P z+γ • gradient g (P z) := by
  rw [← prox_gradient hg hγ hP z,smul_smul,mul_inv_cancel₀ hγ.ne',one_smul]
  abel
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/RunIdentities.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates RelaxedPRS.StrongCvx
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
omit [CompleteSpace H] in
lemma run_step {Pf Pg : H → H} {z : ℕ → H} (hz : IsPRSRun Pf Pg (fun _ => 1/2) z) (k : ℕ) :
    z (k+1)=z k+xf Pf Pg (z k)-xg Pg (z k) := by
  rw [hz k]
  simp only [TPRS, RelaxedPRS.StrongCvx.refl, xf, xg]
  module
omit [CompleteSpace H] in
lemma fixed_prox {Pf Pg : H → H} {zs : H} (hzs : TPRS Pf Pg zs=zs) : xf Pf Pg zs=xg Pg zs := by
  unfold TPRS RelaxedPRS.StrongCvx.refl at hzs
  unfold xf xg RelaxedPRS.StrongCvx.refl
  have h := congrArg (fun v : H => (1/2:ℝ) • v) hzs
  linear_combination (norm := module) h
lemma run_identities {g : H → ℝ} {β γ : ℝ} (hg : IsSmoothConvex β g) (hγ : 0 < γ)
    {Pf Pg : H → H} (hPg : IsProx γ (gE g) Pg) {z : ℕ → H}
    (hz : IsPRSRun Pf Pg (fun _ => 1/2) z) (k : ℕ) :
    xf Pf Pg (z k)-xg Pg (z (k+1)) = γ • (gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))) ∧
    xg Pg (z k)-xg Pg (z (k+1)) =
      γ • (gtF γ Pf Pg (z k)+gradient g (xg Pg (z (k+1)))) := by
  have h0 := prox_gradient_identity hg hγ hPg (z k)
  have h1 := prox_gradient_identity hg hγ hPg (z (k+1))
  have hs := run_step hz k
  change z k=xg Pg (z k)+γ • gradient g (xg Pg (z k)) at h0
  change z (k+1)=xg Pg (z (k+1))+γ • gradient g (xg Pg (z (k+1))) at h1
  constructor
  · linear_combination (norm := module) h1-hs-h0
  · change xg Pg (z k)-xg Pg (z (k+1)) = γ •
      (γ⁻¹ • ((2:ℝ) • xg Pg (z k)-z k-xf Pf Pg (z k))+gradient g (xg Pg (z (k+1))))
    simp only [smul_add,smul_smul,mul_inv_cancel₀ hγ.ne',one_smul]
    linear_combination (norm := module) h1-hs
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/Fundamental.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates RelaxedPRS.StrongCvx
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma joint_descent {f : H → EReal} (hf : IsProperClosedConvex f) {g : H → ℝ} {β : ℝ}
    (hg : IsSmoothConvex β g) (x v w q : H) (hx : f x ≠ ⊤)
    (hv : q ∈ MoreauProx.Characterization.subgrad f v) :
    (f v).toReal+g v-((f x).toReal+g x) ≤
      inner ℝ (v-x) (q+gradient g w)+(1/(2*β))*‖w-v‖^2 := by
  have hs := hv.2.2 x
  rw [← EReal.coe_toReal hv.2.1 hv.1,← EReal.coe_toReal hx (hf.1 x),
    ← EReal.coe_add,EReal.coe_le_coe_iff] at hs
  have hu := smooth_descent g β⁻¹ hg.2.1 hg.2.2 w v
  have hl := convex_gradient hg.1 hg.2.1 w x
  have he : inner ℝ (v-x) (q+gradient g w) =
    -inner ℝ (x-v) q+inner ℝ (gradient g w) (v-w)-inner ℝ (gradient g w) (x-w) := by
    simp only [inner_sub_left,inner_sub_right,inner_add_right]
    rw [real_inner_comm v (gradient g w),real_inner_comm x (gradient g w)]
    ring
  rw [he,norm_sub_rev w v]
  have heq : β⁻¹/2=1/(2*β) := by ring
  rw [heq] at hu
  linarith
lemma fundamental {f : H → EReal} (hf : IsProperClosedConvex f) {g : H → ℝ} {β γ : ℝ}
    (hb : 0 < β) (hg : IsSmoothConvex β g) (hγ : 0 < γ) {Pf Pg : H → H}
    (hPf : IsProx γ f Pf) (hPg : IsProx γ (gE g) Pg) {z : ℕ → H}
    (hz : IsPRSRun Pf Pg (fun _ => 1/2) z) (k : ℕ) (x : H) (hx : f x ≠ ⊤) :
    2*γ*((f (xf Pf Pg (z k))).toReal+g (xf Pf Pg (z k))-((f x).toReal+g x))+
      (2*γ*β-γ^3/β)*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖^2+
      ‖xg Pg (z (k+1))-x‖^2+‖xg Pg (z (k+1))-xg Pg (z k)‖^2 ≤ ‖xg Pg (z k)-x‖^2 := by
  let u := xg Pg (z k)
  let v := xf Pf Pg (z k)
  let w := xg Pg (z (k+1))
  let d := gradient g w-gradient g u
  let q := gtF γ Pf Pg (z k)
  obtain ⟨hvw,huw⟩ := run_identities hg hγ hPg hz k
  change v-w=γ • d at hvw
  change u-w=γ • (q+gradient g w) at huw
  have hs : q ∈ MoreauProx.Characterization.subgrad f v :=
    prox_subgradient hf hγ hPf (RelaxedPRS.StrongCvx.refl Pg (z k))
  have hj := mul_le_mul_of_nonneg_left (joint_descent hf hg x v w q hx hs) (show 0 ≤ 2*γ by positivity)
  have hn : ‖w-v‖^2=γ^2*‖d‖^2 := by
    rw [norm_sub_rev w v,hvw,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [hn] at hj
  have hi : 2*γ*inner ℝ (v-x) (q+gradient g w)=2*inner ℝ (v-x) (u-w) := by
    rw [huw,real_inner_smul_right]
    ring
  have hc := cocoercive hb hg w u
  change β*‖d‖^2 ≤ inner ℝ d (w-u) at hc
  have he : 2*inner ℝ (v-x) (u-w) =
      ‖u-x‖^2-‖w-x‖^2-‖w-u‖^2-2*γ*inner ℝ d (w-u) := by
    have hv' : v=w+γ • d := by linear_combination (norm := module) hvw
    rw [hv']
    simp only [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
      inner_add_left,real_inner_smul_left]
    rw [real_inner_comm u w,real_inner_comm u x,real_inner_comm w x]
    ring
  have hcoef : 2*γ*(1/(2*β))*γ^2=γ^3/β := by field_simp
  have hj' : 2*γ*((f v).toReal+g v-((f x).toReal+g x)) ≤
      2*inner ℝ (v-x) (u-w)+(γ^3/β)*‖d‖^2 := by
    nlinarith only [hj,hi,congrArg (fun t : ℝ => t*‖d‖^2) hcoef]
  rw [he] at hj'
  have hcc := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*γ by positivity)
  change 2*γ*((f v).toReal+g v-((f x).toReal+g x))+
    (2*γ*β-γ^3/β)*‖d‖^2+‖w-x‖^2+‖w-u‖^2 ≤ ‖u-x‖^2
  nlinarith only [hj',hcc]
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/ProxFirm.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma prox_firm {f : H → EReal} (hf : IsProperClosedConvex f) {γ : ℝ}
    (hγ : 0 < γ) {P : H → H} (hP : IsProx γ f P) (z w : H) :
    ‖P z-P w‖^2 ≤ inner ℝ (z-w) (P z-P w) := by
  have h1 := prox_support hf hγ hP z (P w) (prox_finite hf hP w)
  have h2 := prox_support hf hγ hP w (P z) (prox_finite hf hP z)
  have hh : inner ℝ (P w-P z) (γ⁻¹ • (z-P z))+
      inner ℝ (P z-P w) (γ⁻¹ • (w-P w)) =
      γ⁻¹*(‖P z-P w‖^2-inner ℝ (z-w) (P z-P w)) := by
    simp only [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,real_inner_smul_right]
    rw [real_inner_comm (P z) z,real_inner_comm (P w) z,
      real_inner_comm (P z) w,real_inner_comm (P w) w,real_inner_comm (P w) (P z)]
    ring
  have hn : γ⁻¹*(‖P z-P w‖^2-inner ℝ (z-w) (P z-P w)) ≤ 0 := by linarith
  nlinarith [inv_pos.mpr hγ]
lemma reflected_distance {f : H → EReal} (hf : IsProperClosedConvex f) {γ : ℝ}
    (hγ : 0 < γ) {P : H → H} (hP : IsProx γ f P) (z w : H) :
    ‖RelaxedPRS.StrongCvx.refl P z-RelaxedPRS.StrongCvx.refl P w‖ ≤ ‖z-w‖ := by
  have hf' := prox_firm hf hγ hP z w
  have he : ‖RelaxedPRS.StrongCvx.refl P z-RelaxedPRS.StrongCvx.refl P w‖^2 =
      ‖z-w‖^2+4*(‖P z-P w‖^2-inner ℝ (z-w) (P z-P w)) := by
    unfold RelaxedPRS.StrongCvx.refl
    simp only [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
      real_inner_smul_left,real_inner_smul_right]
    rw [real_inner_comm (P z) z,real_inner_comm (P w) z,
      real_inner_comm (P z) w,real_inner_comm (P w) w,real_inner_comm (P w) (P z),real_inner_comm w z]
    ring
  nlinarith [norm_nonneg (RelaxedPRS.StrongCvx.refl P z-RelaxedPRS.StrongCvx.refl P w),norm_nonneg (z-w)]
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/RunFejer.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates RelaxedPRS.StrongCvx
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
lemma run_fejer {f : H → EReal} (hf : IsProperClosedConvex f) {g : H → ℝ} {β γ : ℝ}
    (hg : IsSmoothConvex β g) (hγ : 0 < γ) {Pf Pg : H → H}
    (hPf : IsProx γ f Pf) (hPg : IsProx γ (gE g) Pg) {z : ℕ → H}
    (hz : IsPRSRun Pf Pg (fun _ => 1/2) z) (zs : H) (hzs : TPRS Pf Pg zs=zs) (k : ℕ) :
    ‖z (k+1)-zs‖^2+‖z (k+1)-z k‖^2 ≤ ‖z k-zs‖^2 := by
  have h1 := reflected_distance hf hγ hPf (RelaxedPRS.StrongCvx.refl Pg (z k)) (RelaxedPRS.StrongCvx.refl Pg zs)
  have h2 := reflected_distance (real_proper hg.1 hg.2.1.continuous) hγ hPg (z k) zs
  have hh : ‖TPRS Pf Pg (z k)-zs‖ ≤ ‖z k-zs‖ := by
    have ht : ‖TPRS Pf Pg (z k)-TPRS Pf Pg zs‖ ≤ ‖z k-zs‖ := h1.trans h2
    simpa only [hzs] using ht
  have he : ‖z (k+1)-zs‖^2+‖z (k+1)-z k‖^2 =
      (‖z k-zs‖^2+‖TPRS Pf Pg (z k)-zs‖^2)/2 := by
    rw [hz k]
    simp only [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
      inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
    ring
  rw [he]
  nlinarith [norm_nonneg (TPRS Pf Pg (z k)-zs),norm_nonneg (z k-zs)]
lemma gradient_prox_bound {g : H → ℝ} {β γ : ℝ} (hb : 0 < β)
    (hg : IsSmoothConvex β g) (hγ : 0 < γ) {P : H → H}
    (hP : IsProx γ (gE g) P) (z w : H) :
    (β^2+γ^2)*‖gradient g (P z)-gradient g (P w)‖^2 ≤ ‖z-w‖^2 := by
  let d := gradient g (P z)-gradient g (P w)
  have h0 := prox_gradient_identity hg hγ hP z
  have h1 := prox_gradient_identity hg hγ hP w
  have he : z-w=(P z-P w)+γ • d := by
    dsimp [d]
    linear_combination (norm := module) h0-h1
  have hn : ‖z-w‖^2=‖P z-P w‖^2+2*γ*inner ℝ d (P z-P w)+γ^2*‖d‖^2 := by
    rw [he]
    simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right]
    rw [real_inner_comm d (P z-P w)]
    ring
  have hc := cocoercive hb hg (P z) (P w)
  have hl := hg.2.2 (P z) (P w)
  have hl' : β*‖d‖ ≤ ‖P z-P w‖ := by
    have hh := mul_le_mul_of_nonneg_left hl hb.le
    dsimp [d]
    simpa only [← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul] using hh
  change (β^2+γ^2)*‖d‖^2 ≤ ‖z-w‖^2
  change β*‖d‖^2 ≤ inner ℝ d (P z-P w) at hc
  have hi0 : 0 ≤ inner ℝ d (P z-P w) := le_trans (by positivity) hc
  have hi : 0 ≤ 2*γ*inner ℝ d (P z-P w) := by positivity
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ β*‖d‖) hl'
  nlinarith only [hn,hsq,hi]
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/NativeBudgets.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates RelaxedPRS.StrongCvx
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → EReal} {g : H → ℝ} {β γ : ℝ} {Pf Pg : H → H} {z : ℕ → H}
omit [CompleteSpace H] in
lemma fixed_finite (hf : IsProperClosedConvex f) (hPf : IsProx γ f Pf) (zs : H)
    (hzs : TPRS Pf Pg zs=zs) : f (xg Pg zs) ≠ ⊤ := by
  rw [← fixed_prox hzs]
  exact prox_finite hf hPf (RelaxedPRS.StrongCvx.refl Pg zs)
lemma fixed_subgradient (hg : IsSmoothConvex β g) (hγ : 0 < γ)
    (hPg : IsProx γ (gE g) Pg) (zs : H) (hzs : TPRS Pf Pg zs=zs) :
    gtF γ Pf Pg zs = -gradient g (xg Pg zs) := by
  have he := prox_gradient hg hγ hPg zs
  unfold gtF
  rw [fixed_prox hzs]
  unfold RelaxedPRS.StrongCvx.refl xg at *
  rw [show (2:ℝ) • Pg zs-zs-Pg zs=-(zs-Pg zs) by module,smul_neg,he]
lemma fixed_minimum (hf : IsProperClosedConvex f) (hg : IsSmoothConvex β g) (hγ : 0 < γ)
    (hPf : IsProx γ f Pf) (hPg : IsProx γ (gE g) Pg) (zs : H)
    (hzs : TPRS Pf Pg zs=zs) (u : H) (hu : f u ≠ ⊤) :
    (f (xg Pg zs)).toReal+g (xg Pg zs) ≤ (f u).toReal+g u := by
  have hs := prox_support hf hγ hPf (RelaxedPRS.StrongCvx.refl Pg zs) u hu
  change (f (xf Pf Pg zs)).toReal+inner ℝ (u-xf Pf Pg zs) (gtF γ Pf Pg zs) ≤ (f u).toReal at hs
  rw [fixed_prox hzs,fixed_subgradient hg hγ hPg zs hzs,inner_neg_right] at hs
  have hg' := convex_gradient hg.1 hg.2.1 (xg Pg zs) u
  rw [real_inner_comm (u-xg Pg zs) (gradient g (xg Pg zs))] at hg'
  linarith
lemma native_error_nonneg (hf : IsProperClosedConvex f) (_hb : 0 < β)
    (hg : IsSmoothConvex β g) (hγ : 0 < γ) (hPf : IsProx γ f Pf)
    (hPg : IsProx γ (gE g) Pg) (_hz : IsPRSRun Pf Pg (fun _ => 1/2) z)
    (zs : H) (hzs : TPRS Pf Pg zs=zs) (k : ℕ) : 0 ≤ errF f g Pf Pg z zs k := by
  have h := fixed_minimum hf hg hγ hPf hPg zs hzs (xf Pf Pg (z k))
    (prox_finite hf hPf (RelaxedPRS.StrongCvx.refl Pg (z k)))
  unfold errF
  linarith
lemma native_gradient_budget (hf : IsProperClosedConvex f) (hb : 0 < β)
    (hg : IsSmoothConvex β g) (hγ : 0 < γ) (hPf : IsProx γ f Pf)
    (hPg : IsProx γ (gE g) Pg) (hz : IsPRSRun Pf Pg (fun _ => 1/2) z)
    (zs : H) (hzs : TPRS Pf Pg zs=zs) (N : ℕ) :
    ∑ i ∈ Finset.range N, ‖gradient g (xg Pg (z (i+1)))-gradient g (xg Pg (z i))‖^2 ≤
      ‖z 0-zs‖^2/(β^2+γ^2) := by
  have hc : 0 < β^2+γ^2 := by positivity
  have htel : ∀N, (β^2+γ^2)*(∑ i ∈ Finset.range N,
      ‖gradient g (xg Pg (z (i+1)))-gradient g (xg Pg (z i))‖^2)+‖z N-zs‖^2 ≤ ‖z 0-zs‖^2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hg' := gradient_prox_bound hb hg hγ hPg (z (N+1)) (z N)
      have hf' := run_fejer hf hg hγ hPf hPg hz zs hzs N
      change (β^2+γ^2)*‖gradient g (xg Pg (z (N+1)))-gradient g (xg Pg (z N))‖^2 ≤ ‖z (N+1)-z N‖^2 at hg'
      nlinarith only [ih,hg',hf']
  apply (le_div_iff₀ hc).mpr
  have h := htel N
  nlinarith [sq_nonneg ‖z N-zs‖]
lemma native_error_recurrence (hf : IsProperClosedConvex f) (hb : 0 < β)
    (hg : IsSmoothConvex β g) (hγ : 0 < γ) (hPf : IsProx γ f Pf)
    (hPg : IsProx γ (gE g) Pg) (hz : IsPRSRun Pf Pg (fun _ => 1/2) z)
    (zs : H) (hzs : TPRS Pf Pg zs=zs) (k : ℕ) :
    2*γ*errF f g Pf Pg z zs k ≤ ‖xg Pg (z k)-xg Pg zs‖^2-‖xg Pg (z (k+1))-xg Pg zs‖^2+
      (γ^3/β-2*γ*β-β^2)*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖^2 := by
  have h := fundamental hf hb hg hγ hPf hPg hz k (xg Pg zs) (fixed_finite hf hPf zs hzs)
  have hl := hg.2.2 (xg Pg (z (k+1))) (xg Pg (z k))
  have hl' := mul_le_mul_of_nonneg_left hl hb.le
  simp only [← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul] at hl'
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ β*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖) hl'
  unfold errF
  nlinarith only [h,hs]
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/NativeSmallBudget.lean
namespace RelaxedPRS.DRSSmooth.DSFresh
open ThreeOpSplitting.ConvexRates RelaxedPRS.StrongCvx
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → EReal} {g : H → ℝ} {β γ : ℝ} {Pf Pg : H → H} {z : ℕ → H}
lemma native_seqB_properties (hf : IsProperClosedConvex f) (hb : 0 < β)
    (hg : IsSmoothConvex β g) (hγ : 0 < γ) (hPf : IsProx γ f Pf)
    (hPg : IsProx γ (gE g) Pg) (hz : IsPRSRun Pf Pg (fun _ => 1/2) z)
    (zs : H) (hzs : TPRS Pf Pg zs=zs) (θ : ℝ) (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1)
    (htg : θ*γ^2 ≤ 2*γ*β-γ^3/β) (htu : (1-θ)*γ^2/β^2 ≤ 1) :
    (∀k,2*γ*errF f g Pf Pg z zs k ≤ seqB f g Pf Pg z zs γ β θ k) ∧
    Antitone (seqB f g Pf Pg z zs γ β θ) ∧
    ∀k,seqB f g Pf Pg z zs γ β θ k ≤
      ‖xg Pg (z k)-xg Pg zs‖^2-‖xg Pg (z (k+1))-xg Pg zs‖^2 := by
  have hη : 0 ≤ (1-θ)*γ^2/β^2 := by positivity
  have hθ : 0 ≤ θ*γ^2 := by positivity
  refine ⟨?_,?_,?_⟩
  · intro k
    unfold seqB
    have h1 : 0 ≤ θ*γ^2*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖^2 := by positivity
    have h2 : 0 ≤ (1-θ)*γ^2/β^2*‖xg Pg (z (k+1))-xg Pg (z k)‖^2 := by positivity
    linarith
  · apply antitone_nat_of_succ_le
    intro k
    have h := fundamental hf hb hg hγ hPf hPg hz (k+1) (xf Pf Pg (z k))
      (prox_finite hf hPf (RelaxedPRS.StrongCvx.refl Pg (z k)))
    have hi := (run_identities hg hγ hPg hz k).1
    have hn : ‖xg Pg (z (k+1))-xf Pf Pg (z k)‖^2 =
        γ^2*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖^2 := by
      rw [norm_sub_rev,hi,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    rw [hn] at h
    have hl := hg.2.2 (xg Pg (z (k+1))) (xg Pg (z k))
    have hl' := mul_le_mul_of_nonneg_left hl hb.le
    simp only [← mul_assoc,mul_inv_cancel₀ hb.ne',one_mul] at hl'
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ β*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖) hl'
    have hr := mul_le_mul_of_nonneg_left hs hη
    have hc : ((1-θ)*γ^2/β^2)*β^2=(1-θ)*γ^2 := by field_simp
    have hr' : γ^2*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖^2 ≤
        θ*γ^2*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖^2+
        (1-θ)*γ^2/β^2*‖xg Pg (z (k+1))-xg Pg (z k)‖^2 := by
      nlinarith only [hr,congrArg (fun t : ℝ => t*‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖^2) hc]
    have hcg := mul_le_mul_of_nonneg_right htg (sq_nonneg ‖gradient g (xg Pg (z (k+1+1)))-gradient g (xg Pg (z (k+1)))‖)
    have hcu := mul_le_mul_of_nonneg_right htu (sq_nonneg ‖xg Pg (z (k+1+1))-xg Pg (z (k+1))‖)
    have hd := sq_nonneg ‖xg Pg (z (k+1+1))-xf Pf Pg (z k)‖
    unfold seqB errF
    nlinarith only [h,hr',hcg,hcu,hd]
  · intro k
    have h := fundamental hf hb hg hγ hPf hPg hz k (xg Pg zs) (fixed_finite hf hPf zs hzs)
    have hcg := mul_le_mul_of_nonneg_right htg (sq_nonneg ‖gradient g (xg Pg (z (k+1)))-gradient g (xg Pg (z k))‖)
    have hcu := mul_le_mul_of_nonneg_right htu (sq_nonneg ‖xg Pg (z (k+1))-xg Pg (z k)‖)
    unfold seqB errF
    nlinarith only [h,hcg,hcu]
end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/NativeConclusion.lean

namespace RelaxedPRS.DRSSmooth.DSFresh
open InnerProductSpace Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem native_theorem_3_2 (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg (fun _ => 1 / 2) z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ^ 3 - 2 * ρ - 1 = 0)
    (κ : ℝ) (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) :
    (γ < ρ * β → ∀ k : ℕ,
      (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one) (errF f g Pf Pg z zs) ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 / (2 * γ * ((k : ℝ) + 1))) ∧
    (ρ * β ≤ γ → ∀ k : ℕ,
      (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one) (errF f g Pf Pg z zs) ≤
        (‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 +
          1 / (β ^ 2 + γ ^ 2) *
            (γ ^ 3 / β - 2 * γ * β - β ^ 2) * ‖z 0 - zs‖ ^ 2) /
            (2 * γ * ((k : ℝ) + 1))) ∧
    (fun k : ℕ => (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one)
      (errF f g Pf Pg z zs)) =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) ∧
    (γ < κ * β →
      (∀ k : ℕ, errF f g Pf Pg z zs k ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 / (2 * γ * ((k : ℝ) + 1))) ∧
      (errF f g Pf Pg z zs) =o[atTop]
        (fun k : ℕ => 1 / ((k : ℝ) + 1))) := by
  let e : ℕ → ℝ := errF f g Pf Pg z zs
  let D : ℕ → ℝ := fun k => ‖RelaxedPRS.StrongCvx.xg Pg (z k) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2
  let G : ℕ → ℝ := fun k => ‖gradient g (RelaxedPRS.StrongCvx.xg Pg (z (k + 1))) -
    gradient g (RelaxedPRS.StrongCvx.xg Pg (z k))‖ ^ 2
  have he : ∀ k, 0 ≤ e k := native_error_nonneg hf hβ hg hγ hPf hPg hz zs hzs
  have hD : ∀ k, 0 ≤ D k := fun _ => sq_nonneg _
  have hG : ∀ k, 0 ≤ G k := fun _ => sq_nonneg _
  have hb := native_gradient_budget hf hβ hg hγ hPf hPg hz zs hzs
  have hr := native_error_recurrence hf hβ hg hγ hPf hPg hz zs hzs
  have hbest := best_rates (e := e) (D := D) (G := G) hβ hγ hρ he hD hG hb hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [runningMin, e, D] using hbest.1
  · simpa only [runningMin, e, D] using hbest.2.1
  · exact hbest.2.2
  · intro hγκ
    obtain ⟨θ, hθ0, hθ1, hθG, hθD⟩ := exists_theta hβ hγ hκ hγκ
    obtain ⟨hdom, hmono, hstep⟩ :=
      native_seqB_properties hf hβ hg hγ hPf hPg hz zs hzs θ hθ0 hθ1 hθG hθD
    have hnonneg : ∀ k, 0 ≤ seqB f g Pf Pg z zs γ β θ k := by
      intro k
      exact (mul_nonneg (by positivity : 0 ≤ 2 * γ) (he k)).trans (hdom k)
    have hpoint := pointwise_rates (e := e) (D := D) hγ he hnonneg hD hmono hstep hdom
    simpa only [e, D] using hpoint

end RelaxedPRS.DRSSmooth.DSFresh

-- Complete module: DSProof/FinalRoot.lean
open Filter
namespace RelaxedPRS.DRSSmooth

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 3.2, p. 12: best-iterate and nonergodic DRS objective rates.

Corrected threshold: the page defines ρ as the positive root of x³ − 2x² − 1 (ρ ≈ 2.2056), but the
proof (display (3.2)) needs γ³/β − 2γβ − β² ≤ 0, i.e. t³ − 2t − 1 ≤ 0 with t = γ/β, whose positive
root is the golden ratio (≈ 1.618). With the printed ρ the first case is false: f = 0,
g(x) = x²/(2β) on ℝ, γ = 2β, k = 0 gives an error twice the bound. Here ρ is the positive root of
x³ − 2x − 1. -/
theorem theorem_3_2 (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg (fun _ => 1 / 2) z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ^ 3 - 2 * ρ - 1 = 0)
    (κ : ℝ) (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) :
    (γ < ρ * β → ∀ k : ℕ,
      (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one) (errF f g Pf Pg z zs) ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 / (2 * γ * ((k : ℝ) + 1))) ∧
    (ρ * β ≤ γ → ∀ k : ℕ,
      (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one) (errF f g Pf Pg z zs) ≤
        (‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 +
          1 / (β ^ 2 + γ ^ 2) *
            (γ ^ 3 / β - 2 * γ * β - β ^ 2) * ‖z 0 - zs‖ ^ 2) /
            (2 * γ * ((k : ℝ) + 1))) ∧
    (fun k : ℕ => (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one)
      (errF f g Pf Pg z zs)) =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) ∧
    (γ < κ * β →
      (∀ k : ℕ, errF f g Pf Pg z zs k ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 / (2 * γ * ((k : ℝ) + 1))) ∧
      (errF f g Pf Pg z zs) =o[atTop]
        (fun k : ℕ => 1 / ((k : ℝ) + 1))) := by
  exact DSFresh.native_theorem_3_2 f hf g β hβ hg γ hγ Pf Pg hPf hPg z hz zs hzs ρ hρ κ hκ

end RelaxedPRS.DRSSmooth


open RelaxedPRS.DRSSmooth
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
theorem solution (f : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (g : H → ℝ) (β : ℝ) (hβ : 0 < β)
    (hg : ThreeOpSplitting.ConvexRates.IsSmoothConvex β g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ (gE g) Pg)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg (fun _ => 1 / 2) z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (ρ : ℝ) (hρ : 0 < ρ ∧ ρ ^ 3 - 2 * ρ - 1 = 0)
    (κ : ℝ) (hκ : 0 < κ ∧ κ ^ 3 + κ ^ 2 - 2 * κ - 1 = 0) :
    (γ < ρ * β → ∀ k : ℕ,
      (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one) (errF f g Pf Pg z zs) ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 / (2 * γ * ((k : ℝ) + 1))) ∧
    (ρ * β ≤ γ → ∀ k : ℕ,
      (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one) (errF f g Pf Pg z zs) ≤
        (‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 +
          1 / (β ^ 2 + γ ^ 2) *
            (γ ^ 3 / β - 2 * γ * β - β ^ 2) * ‖z 0 - zs‖ ^ 2) /
            (2 * γ * ((k : ℝ) + 1))) ∧
    (fun k : ℕ => (Finset.range (k + 1)).inf' (Finset.nonempty_range_add_one)
      (errF f g Pf Pg z zs)) =o[atTop] (fun k : ℕ => 1 / ((k : ℝ) + 1)) ∧
    (γ < κ * β →
      (∀ k : ℕ, errF f g Pf Pg z zs k ≤
        ‖RelaxedPRS.StrongCvx.xg Pg (z 0) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 / (2 * γ * ((k : ℝ) + 1))) ∧
      (errF f g Pf Pg z zs) =o[atTop]
        (fun k : ℕ => 1 / ((k : ℝ) + 1))) := by
  exact RelaxedPRS.DRSSmooth.theorem_3_2 f hf g β hβ hg γ hγ Pf Pg hPf hPg z hz zs hzs ρ hρ κ hκ
