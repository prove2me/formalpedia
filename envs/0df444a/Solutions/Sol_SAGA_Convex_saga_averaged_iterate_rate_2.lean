-- Prove2me | solution 2 for SAGA.Convex.saga_averaged_iterate_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:10:52.995067+00:00
-- url     : https://prove2.me/submissions/0c808c52-4500-484a-bf8c-d6c6fc0f2426

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaStep
import Definitions.Def_SAGA_Convex_lyapunov
import Definitions.Def_SAGA_Convex_sagaRun
import Theorems.Thm_SAGA_Convex_lyapunov_one_step

-- carved verbatim out of submission 8e0f76de-8819-4bbc-a920-e0938f4a1398, lines 1026-1043

section
open scoped RealInnerProductSpace
open SAGA
open SAGA.Convex

lemma sg_line {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (g' : EuclideanSpace ℝ (Fin d))
    (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) (hg : HasGradientAt g g' (x + t • v)) :
    HasDerivAt (fun s : ℝ => g (x + s • v)) ⟪g', v⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have := hg.hasFDerivAt.comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at this
  exact this

lemma sg_strong_lower {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (μ : ℝ)
    (g' : EuclideanSpace ℝ (Fin d)) (x w : EuclideanSpace ℝ (Fin d))
    (hconv : StrongConvexOn Set.univ μ g) (hgrad : HasGradientAt g g' x) :
    g x + ⟪g', w - x⟫ + μ / 2 * ‖w - x‖ ^ 2 ≤ g w := by
  set r := w - x with hr
  have hφ := strongConvexOn_iff_convex.mp hconv
  set ψ : ℝ → ℝ := fun s => g (x + s • r) - μ / 2 * (‖x‖ ^ 2 + 2 * s * ⟪x, r⟫ + s ^ 2 * ‖r‖ ^ 2)
    with hψ
  have hψeq : ∀ s : ℝ, ψ s = g (x + s • r) - μ / (2:ℝ) * ‖x + s • r‖ ^ 2 := by
    intro s
    simp only [hψ]
    rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hψconv : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ p q hp hq hpq
    have e : x + (p • a + q • b) • r = p • (x + a • r) + q • (x + b • r) := by
      obtain rfl : q = 1 - p := by linarith
      simp only [smul_eq_mul]
      module
    rw [hψeq, hψeq, hψeq, e]
    exact hφ.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
  have hd1 : HasDerivAt (fun s : ℝ => g (x + s • r)) ⟪g', r⟫ 0 :=
    sg_line g g' x r 0 (by simpa using hgrad)
  have hd2 : HasDerivAt (fun s : ℝ => μ / 2 * (‖x‖ ^ 2 + 2 * s * ⟪x, r⟫ + s ^ 2 * ‖r‖ ^ 2))
      (μ / 2 * (2 * ⟪x, r⟫ + 2 * 0 * ‖r‖ ^ 2)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * s * ⟪x, r⟫) (2 * ⟪x, r⟫) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const ⟪x, r⟫
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * ‖r‖ ^ 2) (2 * 0 * ‖r‖ ^ 2) 0 := by
      simpa using (hasDerivAt_pow 2 (0:ℝ)).mul_const (‖r‖ ^ 2)
    exact (((hasDerivAt_const (0:ℝ) (‖x‖ ^ 2)).add h1).add h2).const_mul (μ / 2) |>.congr_deriv
      (by ring)
  have hd : HasDerivAt ψ (⟪g', r⟫ - μ / 2 * (2 * ⟪x, r⟫ + 2 * 0 * ‖r‖ ^ 2)) 0 := hd1.sub hd2
  have hs := hψconv.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    zero_lt_one hd
  rw [slope_def_field] at hs
  simp only [hψ] at hs
  have e1 : x + (1:ℝ) • r = w := by simp [hr]
  have e0 : x + (0:ℝ) • r = x := by simp
  rw [e1, e0] at hs
  norm_num at hs
  nlinarith

lemma sg_grad_ineq {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (g' : EuclideanSpace ℝ (Fin d)) (x w : EuclideanSpace ℝ (Fin d))
    (hconv : ConvexOn ℝ Set.univ g) (hgrad : HasGradientAt g g' x) :
    g x + ⟪g', w - x⟫ ≤ g w := by
  have := sg_strong_lower g 0 g' x w (strongConvexOn_zero.mpr hconv) hgrad
  simpa using this

lemma sg_avg_lower {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x y : EuclideanSpace ℝ (Fin d)) (c : ℝ)
    (hi : ∀ i, f i x + ⟪f' i x, y - x⟫ + c ≤ f i y) :
    fAvg f x + ⟪gradAvg f' x, y - x⟫ + c ≤ fAvg f y := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  unfold fAvg gradAvg
  rw [inner_smul_left, sum_inner, RCLike.conj_to_real]
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1 / n)
  have e : 1 / (n:ℝ) * (n * c) = c := by field_simp
  nlinarith

lemma sg_lyap {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (xs : EuclideanSpace ℝ (Fin d)) (a : ℝ)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d))) :
    lyapunov f f' xs a s = (1 / (n:ℝ)) * ∑ i, (f i (s.2 i) - f i xs - ⟪f' i xs, s.2 i - xs⟫)
      + a * ‖s.1 - xs‖ ^ 2 := by
  unfold lyapunov fAvg
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

lemma sg_ofFn_snoc {α : Type*} {t : ℕ} (l : Fin t → α) (j : α) :
    List.ofFn (Fin.snoc l j : Fin (t + 1) → α) = List.ofFn l ++ [j] := by
  rw [List.ofFn_succ']
  simp

lemma sg_sum_snoc {n t : ℕ} (G : (Fin (t + 1) → Fin n) → ℝ) :
    ∑ g, G g = ∑ l : Fin t → Fin n, ∑ j, G (Fin.snoc l j) := by
  rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma sg_take_sum {n : ℕ} (G : List (Fin n) → ℝ) (t : ℕ) :
    ∀ k, t ≤ k → ∑ js : Fin k → Fin n, G ((List.ofFn js).take t) =
      (n:ℝ) ^ (k - t) * ∑ l : Fin t → Fin n, G (List.ofFn l) := by
  intro k hk
  induction k with
  | zero =>
    obtain rfl : t = 0 := by omega
    simp
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · subst h
      have e : ∀ js : Fin (k + 1) → Fin n, (List.ofFn js).take (k + 1) = List.ofFn js :=
        fun js => List.take_of_length_le (by simp)
      simp only [e, Nat.sub_self, pow_zero, one_mul]
    · have hk' : t ≤ k := by omega
      rw [sg_sum_snoc]
      have e : ∀ (l : Fin k → Fin n) (j : Fin n),
          G ((List.ofFn (Fin.snoc l j : Fin (k + 1) → Fin n)).take t) = G ((List.ofFn l).take t) := by
        intro l j
        rw [sg_ofFn_snoc, List.take_append_of_le_length (by simp; omega)]
      simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum, ih hk', ← mul_assoc, ← pow_succ']
      congr 2
      omega

lemma sg_run_snoc {d n : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) {t : ℕ} (l : Fin t → Fin n) (j : Fin n) :
    sagaRun f' P γ x0 (List.ofFn (Fin.snoc l j : Fin (t + 1) → Fin n)) =
      sagaStep f' P γ (sagaRun f' P γ x0 (List.ofFn l)) j := by
  rw [sg_ofFn_snoc]
  simp [sagaRun, List.foldl_append]

lemma sg_jensen {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (k : ℕ) (hk : 1 ≤ k) (x : ℕ → EuclideanSpace ℝ (Fin d)) :
    g ((1 / (k:ℝ)) • ∑ t ∈ Finset.range k, x t) ≤ (1 / (k:ℝ)) * ∑ t ∈ Finset.range k, g (x t) := by
  have hK : (0:ℝ) < k := by exact_mod_cast hk
  rw [Finset.smul_sum, Finset.mul_sum]
  have := hg.map_sum_le (t := Finset.range k) (w := fun _ => 1 / (k:ℝ)) (p := x)
    (fun _ _ => by positivity) (by simp; field_simp) (fun _ _ => Set.mem_univ _)
  simpa using this

lemma sg_fAvg_jensen {d n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (k : ℕ) (hk : 1 ≤ k) (x : ℕ → EuclideanSpace ℝ (Fin d)) :
    fAvg f ((1 / (k:ℝ)) • ∑ t ∈ Finset.range k, x t) ≤
      (1 / (k:ℝ)) * ∑ t ∈ Finset.range k, fAvg f (x t) := by
  unfold fAvg
  have h1 : ∑ i, f i ((1 / (k:ℝ)) • ∑ t ∈ Finset.range k, x t) ≤
      ∑ i, (1 / (k:ℝ)) * ∑ t ∈ Finset.range k, f i (x t) :=
    Finset.sum_le_sum (fun i _ => sg_jensen (f i) (hconv i) k hk x)
  have e : ∑ i, (1 / (k:ℝ)) * ∑ t ∈ Finset.range k, f i (x t) =
      (1 / (k:ℝ)) * ∑ t ∈ Finset.range k, ∑ i, f i (x t) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [e] at h1
  calc 1 / (n:ℝ) * ∑ i, f i ((1 / (k:ℝ)) • ∑ t ∈ Finset.range k, x t)
      ≤ 1 / (n:ℝ) * (1 / ↑k * ∑ t ∈ Finset.range k, ∑ i, f i (x t)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / ↑k * ∑ t ∈ Finset.range k, (1 / ↑n * ∑ i, f i (x t)) := by
        rw [← Finset.mul_sum]; ring

theorem goal_core {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) (hk : 1 ≤ k) :
    expectIdx n k (fun js => fAvg f (avgIterate f' P (1 / (3 * L)) x0 js)
        + h (avgIterate f' P (1 / (3 * L)) x0 js))
      - (fAvg f xs + h xs) ≤
      4 * n / k * (2 * L / n * ‖x0 - xs‖ ^ 2 + fAvg f x0 - ⟪gradAvg f' xs, x0 - xs⟫
        - fAvg f xs) := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hK : (0:ℝ) < k := by exact_mod_cast hk
  set γ := 1 / (3 * L) with hγ
  set a := 3 * L / (2 * n) + 3 * L / (8 * n) with ha
  set Fs := fAvg f xs + h xs with hFs
  let T : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ :=
    fun s => lyapunov f f' xs a s
  let F' : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ :=
    fun s => fAvg f s.1 + h s.1 - Fs
  let R : (t : ℕ) → (EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ) → ℝ :=
    fun t H => ∑ l : Fin t → Fin n, H (sagaRun f' P γ x0 (List.ofFn l))
  -- T nonnegative
  have hT0 : ∀ s, 0 ≤ T s := by
    intro s
    show 0 ≤ lyapunov f f' xs a s
    rw [sg_lyap]
    have h1 : 0 ≤ ∑ i, (f i (s.2 i) - f i xs - ⟪f' i xs, s.2 i - xs⟫) := by
      apply Finset.sum_nonneg; intro i _
      have := sg_grad_ineq (f i) (f' i xs) xs (s.2 i) (hconv i) (hgrad i xs)
      linarith
    have : 0 ≤ a := by positivity
    positivity
  -- one step in sum form
  have hstep : ∀ s, ∑ j, T (sagaStep f' P γ s j) ≤
      n * T s - 1 / (4 * n) * ∑ j, F' (sagaStep f' P γ s j) := by
    intro s
    have := SAGA.Convex.lyapunov_one_step hn hL f f' hgrad hLip hconv h hh P hP xs hopt s
    have e1 := mul_le_mul_of_nonneg_left this hN.le
    have e2 : (n:ℝ) * ((1 / (n:ℝ)) * ∑ j, T (sagaStep f' P γ s j) - T s) =
        ∑ j, T (sagaStep f' P γ s j) - n * T s := by field_simp
    have e3 : (n:ℝ) * (-(1 / (4 * (n : ℝ))) * ((1 / (n : ℝ)) * ∑ j, F' (sagaStep f' P γ s j))) =
        - (1 / (4 * n) * ∑ j, F' (sagaStep f' P γ s j)) := by field_simp
    simp only [T, F'] at e2 e3 ⊢
    linarith
  have hRsucc : ∀ t (H : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ),
      R (t + 1) H = ∑ l : Fin t → Fin n, ∑ j, H (sagaStep f' P γ (sagaRun f' P γ x0 (List.ofFn l)) j) := by
    intro t H
    simp only [R]
    rw [sg_sum_snoc]
    simp only [sg_run_snoc]
  have hRstep : ∀ t, R (t + 1) T ≤ n * R t T - 1 / (4 * n) * R (t + 1) F' := by
    intro t
    rw [hRsucc, hRsucc]
    have := Finset.sum_le_sum (fun (l : Fin t → Fin n) (_ : l ∈ Finset.univ) =>
      hstep (sagaRun f' P γ x0 (List.ofFn l)))
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at this
    exact this
  have hR0 : R 0 T = T (x0, fun _ => x0) := by
    simp [R, sagaRun]
  -- telescoping
  have htel : ∀ m, R m T / (n:ℝ) ^ m + 1 / (4 * n) * ∑ t ∈ Finset.range m,
      R (t + 1) F' / (n:ℝ) ^ (t + 1) ≤ T (x0, fun _ => x0) := by
    intro m
    induction m with
    | zero => simp [hR0]
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hs := hRstep m
      have hpos : (0:ℝ) < (n:ℝ) ^ (m + 1) := by positivity
      have e : R (m + 1) T / (n:ℝ) ^ (m + 1) ≤ R m T / (n:ℝ) ^ m
          - 1 / (4 * n) * (R (m + 1) F' / (n:ℝ) ^ (m + 1)) := by
        rw [div_le_iff₀ hpos]
        have e2 : (R m T / (n:ℝ) ^ m - 1 / (4 * n) * (R (m + 1) F' / (n:ℝ) ^ (m + 1)))
            * (n:ℝ) ^ (m + 1) = n * R m T - 1 / (4 * n) * R (m + 1) F' := by
          field_simp; ring
        rw [e2]; exact hs
      nlinarith
  have hRk : 0 ≤ R k T / (n:ℝ) ^ k :=
    div_nonneg (Finset.sum_nonneg (fun l _ => hT0 _)) (by positivity)
  have hsumF : ∑ t ∈ Finset.range k, R (t + 1) F' / (n:ℝ) ^ (t + 1) ≤
      4 * n * T (x0, fun _ => x0) := by
    have := htel k
    have h4 : 0 < 1 / (4 * (n:ℝ)) := by positivity
    have : 1 / (4 * (n:ℝ)) * ∑ t ∈ Finset.range k, R (t + 1) F' / (n:ℝ) ^ (t + 1) ≤
        T (x0, fun _ => x0) := by linarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at this
    linarith
  -- expectation of iterate t+1
  have hEt : ∀ t ∈ Finset.range k, (1 / (n:ℝ) ^ k) * ∑ js : Fin k → Fin n,
      F' (sagaRun f' P γ x0 ((List.ofFn js).take (t + 1))) = R (t + 1) F' / (n:ℝ) ^ (t + 1) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [sg_take_sum (fun l => F' (sagaRun f' P γ x0 l)) (t + 1) k (by omega)]
    have hpow : (n:ℝ) ^ k = (n:ℝ) ^ (k - (t + 1)) * (n:ℝ) ^ (t + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    have : (0:ℝ) < (n:ℝ) ^ (k - (t + 1)) := by positivity
    have : (0:ℝ) < (n:ℝ) ^ (t + 1) := by positivity
    field_simp
    rfl
  -- pointwise Jensen
  have hpt : ∀ js : Fin k → Fin n,
      fAvg f (avgIterate f' P γ x0 js) + h (avgIterate f' P γ x0 js) - Fs ≤
        (1 / (k:ℝ)) * ∑ t ∈ Finset.range k,
          F' (sagaRun f' P γ x0 ((List.ofFn js).take (t + 1))) := by
    intro js
    have j1 := sg_fAvg_jensen f hconv k hk (fun t => sagaIterate f' P γ x0 js (t + 1))
    have j2 := sg_jensen h hh k hk (fun t => sagaIterate f' P γ x0 js (t + 1))
    unfold avgIterate sagaIterate
    simp only [F', Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    have e : (1 / (k:ℝ)) * (∑ t ∈ Finset.range k, fAvg f (sagaIterate f' P γ x0 js (t + 1))
        + ∑ t ∈ Finset.range k, h (sagaIterate f' P γ x0 js (t + 1)) - k * Fs) =
        (1 / (k:ℝ)) * ∑ t ∈ Finset.range k, fAvg f (sagaIterate f' P γ x0 js (t + 1))
        + (1 / (k:ℝ)) * ∑ t ∈ Finset.range k, h (sagaIterate f' P γ x0 js (t + 1)) - Fs := by
      field_simp
    unfold sagaIterate at e j1 j2
    rw [e]
    linarith
  -- assemble
  have hE : expectIdx n k (fun js => fAvg f (avgIterate f' P γ x0 js)
        + h (avgIterate f' P γ x0 js)) - Fs =
      (1 / (n:ℝ) ^ k) * ∑ js : Fin k → Fin n,
        (fAvg f (avgIterate f' P γ x0 js) + h (avgIterate f' P γ x0 js) - Fs) := by
    unfold expectIdx
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have : (0:ℝ) < (n:ℝ) ^ k := by positivity
    push_cast
    field_simp
  rw [hE]
  have hle := Finset.sum_le_sum (fun js (_ : js ∈ Finset.univ) => hpt js)
  rw [← Finset.mul_sum, Finset.sum_comm] at hle
  have hle2 := mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ 1 / (n:ℝ) ^ k)
  have e4 : 1 / (n:ℝ) ^ k * (1 / (k:ℝ) * ∑ t ∈ Finset.range k, ∑ js : Fin k → Fin n,
      F' (sagaRun f' P γ x0 ((List.ofFn js).take (t + 1)))) =
      1 / (k:ℝ) * ∑ t ∈ Finset.range k, R (t + 1) F' / (n:ℝ) ^ (t + 1) := by
    rw [← Finset.sum_congr rfl hEt, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [e4] at hle2
  have hT : T (x0, fun _ => x0) = fAvg f x0 - fAvg f xs - ⟪gradAvg f' xs, x0 - xs⟫
      + a * ‖x0 - xs‖ ^ 2 := by
    show lyapunov f f' xs a (x0, fun _ => x0) = _
    rw [sg_lyap]
    simp only [Finset.sum_sub_distrib, fAvg, gradAvg, inner_smul_left, sum_inner,
      RCLike.conj_to_real]
    ring
  have hfin : 1 / (k:ℝ) * ∑ t ∈ Finset.range k, R (t + 1) F' / (n:ℝ) ^ (t + 1) ≤
      1 / (k:ℝ) * (4 * n * T (x0, fun _ => x0)) :=
    mul_le_mul_of_nonneg_left hsumF (by positivity)
  have hBr : 0 ≤ fAvg f x0 - fAvg f xs - ⟪gradAvg f' xs, x0 - xs⟫ := by
    have := sg_avg_lower hn f f' xs x0 0
      (fun i => by simpa using sg_grad_ineq (f i) (f' i xs) xs x0 (hconv i) (hgrad i xs))
    linarith
  have ha2 : a ≤ 2 * L / n := by
    rw [ha]; rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) hN]
    nlinarith [mul_pos (mul_pos hL hN) hN]
  have hlast : 1 / (k:ℝ) * (4 * n * T (x0, fun _ => x0)) ≤ 4 * n / k * (2 * L / n * ‖x0 - xs‖ ^ 2
      + fAvg f x0 - ⟪gradAvg f' xs, x0 - xs⟫ - fAvg f xs) := by
    rw [hT]
    have e : 1 / (k:ℝ) * (4 * n * (fAvg f x0 - fAvg f xs - ⟪gradAvg f' xs, x0 - xs⟫
        + a * ‖x0 - xs‖ ^ 2)) = 4 * n / k * (a * ‖x0 - xs‖ ^ 2
        + fAvg f x0 - ⟪gradAvg f' xs, x0 - xs⟫ - fAvg f xs) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_nonneg ‖x0 - xs‖]
  linarith

end

section
open scoped RealInnerProductSpace
open SAGA.Convex

theorem solution {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hgrad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hLip : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ y, IsProxPoint h (1 / (3 * L)) y (P y))
    (xs : EuclideanSpace ℝ (Fin d)) (hopt : ∀ y, fAvg f xs + h xs ≤ fAvg f y + h y)
    (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) (hk : 1 ≤ k) :
    expectIdx n k (fun js => fAvg f (avgIterate f' P (1 / (3 * L)) x0 js)
        + h (avgIterate f' P (1 / (3 * L)) x0 js))
      - (fAvg f xs + h xs) ≤
      4 * n / k * (2 * L / n * ‖x0 - xs‖ ^ 2 + fAvg f x0 - ⟪gradAvg f' xs, x0 - xs⟫
        - fAvg f xs) := by
  exact goal_core hn hL f f' hgrad hLip hconv h hh P hP xs hopt x0 k hk

end
