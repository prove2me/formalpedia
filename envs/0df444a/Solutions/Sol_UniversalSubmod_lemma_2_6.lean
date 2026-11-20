-- Prove2me | solution 1 for UniversalSubmod.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:10:06.572245+00:00
-- url     : https://prove2.me/submissions/fcb01995-8ca4-47b9-80a0-b7bc25e27458

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_UniversalSubmod_threshSet

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Lemma26

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared

section Comb

variable {n : ℕ}

lemma marginal_mono (f : Finset (Fin n) → ℝ) (hf : Submodular f) {S T : Finset (Fin n)}
    (hST : S ⊆ T) {i : Fin n} (hi : i ∉ T) :
    f (insert i T) - f T ≤ f (insert i S) - f S := by
  have h := hf (insert i S) T
  have h1 : insert i S ∪ T = insert i T := by
    ext x; simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hST h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  have h2 : insert i S ∩ T = S := by
    ext x; simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, hx⟩
      · exact absurd (h ▸ hx) hi
      · exact h
    · intro h; exact ⟨Or.inr h, hST h⟩
  rw [h1, h2] at h
  linarith

/-- Prefix sets for a permutation `σ`. -/
def pre (σ : Equiv.Perm (Fin n)) (l : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ((σ.symm i : Fin n) : ℕ) < l)

/-- marginal weights -/
def wt (f : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  f (pre σ ((σ.symm i : Fin n) + 1)) - f (pre σ (σ.symm i : Fin n))

lemma pre_zero (σ : Equiv.Perm (Fin n)) : pre σ 0 = ∅ := by
  simp [pre]

lemma pre_succ (σ : Equiv.Perm (Fin n)) {l : ℕ} (hl : l < n) :
    pre σ (l + 1) = insert (σ ⟨l, hl⟩) (pre σ l) := by
  ext i
  simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    by_cases h' : ((σ.symm i : Fin n) : ℕ) = l
    · left; apply σ.symm.injective; simp; ext; simpa using h'
    · right; omega
  · rintro (h | h)
    · subst h; simp
    · omega

lemma pre_n (σ : Equiv.Perm (Fin n)) : pre σ n = Finset.univ := by
  ext i; simp [pre]

lemma sum_pre (f : Finset (Fin n) → ℝ) (σ : Equiv.Perm (Fin n)) :
    ∀ l, l ≤ n → ∑ i ∈ pre σ l, wt f σ i = f (pre σ l) - f ∅ := by
  intro l
  induction l with
  | zero => intro _; simp [pre_zero]
  | succ l ih =>
    intro hl
    have hl' : l < n := hl
    rw [pre_succ σ hl']
    have hnot : σ ⟨l, hl'⟩ ∉ pre σ l := by simp [pre]
    rw [Finset.sum_insert hnot, ih hl'.le]
    have : wt f σ (σ ⟨l, hl'⟩) = f (insert (σ ⟨l, hl'⟩) (pre σ l)) - f (pre σ l) := by
      unfold wt
      simp only [Equiv.symm_apply_apply]
      rw [← pre_succ σ hl']
    rw [this]; ring

lemma sum_le (f : Finset (Fin n) → ℝ) (hf : Submodular f) (σ : Equiv.Perm (Fin n))
    (A : Finset (Fin n)) : ∑ i ∈ A, wt f σ i ≤ f A - f ∅ := by
  induction A using Finset.induction_on_max_value (fun i => ((σ.symm i : Fin n) : ℕ)) with
  | empty => simp
  | insert a s ha hmax ih =>
    rw [Finset.sum_insert ha]
    have hsub : s ⊆ pre σ ((σ.symm a : Fin n) : ℕ) := by
      intro x hx
      simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 := hmax x hx
      have h2 : x ≠ a := fun h => ha (h ▸ hx)
      have : ((σ.symm x : Fin n) : ℕ) ≠ ((σ.symm a : Fin n) : ℕ) := by
        intro h; apply h2; apply σ.symm.injective; exact Fin.ext h
      omega
    have hnot : a ∉ pre σ ((σ.symm a : Fin n) : ℕ) := by simp [pre]
    have hm := marginal_mono f hf hsub hnot
    have e : insert a (pre σ ((σ.symm a : Fin n) : ℕ)) = pre σ ((σ.symm a : Fin n) + 1) := by
      ext i
      simp only [pre, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (h | h)
        · subst h; omega
        · omega
      · intro h
        by_cases h' : ((σ.symm i : Fin n) : ℕ) = ((σ.symm a : Fin n) : ℕ)
        · left; apply σ.symm.injective; exact Fin.ext h'
        · right; omega
    rw [e] at hm
    have hw : wt f σ a ≤ f (insert a s) - f s := by unfold wt; exact hm
    linarith

lemma comb (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (a : Fin n → ℝ) :
    ∃ w : Fin n → ℝ, (∀ A, ∑ i ∈ A, w i ≤ f A - f ∅) ∧
      (∀ t, f (Finset.univ.filter (fun i => t ≤ a i)) - f ∅ =
        ∑ i ∈ Finset.univ.filter (fun i => t ≤ a i), w i) ∧
      ∑ i, |w i| ≤ 2 * OPT f := by
  set σ : Equiv.Perm (Fin n) := Tuple.sort (fun i => - a i) with hσ
  have hmono : Monotone ((fun i => - a i) ∘ σ) := Tuple.monotone_sort _
  have hanti : ∀ m m' : Fin n, m ≤ m' → a (σ m') ≤ a (σ m) := by
    intro m m' h; have := hmono h; simp at this; linarith
  refine ⟨wt f σ, sum_le f hf σ, ?_, ?_⟩
  · intro t
    -- the threshold set is a prefix
    have : ∃ l, l ≤ n ∧ Finset.univ.filter (fun i => t ≤ a i) = pre σ l := by
      by_cases hex : ∃ m : Fin n, ¬ t ≤ a (σ m)
      · classical
        let m0 := Nat.find (p := fun m => ∃ h : m < n, ¬ t ≤ a (σ ⟨m, h⟩))
          (by obtain ⟨m, hm⟩ := hex; exact ⟨m.1, m.2, hm⟩)
        have hm0 : ∃ h : m0 < n, ¬ t ≤ a (σ ⟨m0, h⟩) := Nat.find_spec
          (p := fun m => ∃ h : m < n, ¬ t ≤ a (σ ⟨m, h⟩)) (by obtain ⟨m, hm⟩ := hex; exact ⟨m.1, m.2, hm⟩)
        obtain ⟨hlt, hfail⟩ := hm0
        refine ⟨m0, hlt.le, ?_⟩
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, pre]
        set r := σ.symm i
        have hi : σ r = i := by simp [r]
        constructor
        · intro hti
          by_contra hge
          push Not at hge
          apply hfail
          have := hanti ⟨m0, hlt⟩ r (by rw [Fin.le_def]; simpa using hge)
          rw [hi] at this
          linarith
        · intro hr
          by_contra hti
          have hmin := Nat.find_min (p := fun m => ∃ h : m < n, ¬ t ≤ a (σ ⟨m, h⟩))
            (by obtain ⟨m, hm⟩ := hex; exact ⟨m.1, m.2, hm⟩) (m := r.1) hr
          apply hmin
          refine ⟨r.2, ?_⟩
          simpa [hi] using hti
      · push Not at hex
        refine ⟨n, le_rfl, ?_⟩
        rw [pre_n]
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        have := hex (σ.symm i); simpa using this
    obtain ⟨l, hl, hEq⟩ := this
    rw [hEq]
    exact (sum_pre f σ l hl).symm
  · have h1 := sum_pre f σ n le_rfl
    rw [pre_n] at h1
    have h2 := sum_le f hf σ (Finset.univ.filter (fun i => 0 ≤ wt f σ i))
    have hA : f (Finset.univ.filter (fun i => 0 ≤ wt f σ i)) ≤ OPT f :=
      Finset.le_sup' f (Finset.mem_univ _)
    have hB : f Finset.univ ≥ 0 := hf0 _
    have hC := hf0 ∅
    have habs : ∑ i, |wt f σ i| = 2 * ∑ i ∈ Finset.univ.filter (fun i => 0 ≤ wt f σ i), wt f σ i
        - ∑ i, wt f σ i := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : 0 ≤ wt f σ i
      · simp [h, abs_of_nonneg h]; ring
      · push Not at h; simp [not_le.mpr h, abs_of_neg h]
    rw [habs]
    linarith

end Comb


section Taylor

lemma taylor_lower (g q : ℝ → ℝ) (L : ℝ) (hg : ∀ t, HasDerivAt g (q t) t)
    (hq : ∀ x y, |q x - q y| ≤ L * |x - y|) (a s : ℝ) :
    g a + s * q a - L * s ^ 2 / 2 ≤ g (a + s) := by
  set ψ : ℝ → ℝ := fun s => g (a + s) - g a - s * q a + L * s ^ 2 / 2 with hψ
  have hd : ∀ s, HasDerivAt ψ (q (a + s) - q a + L * s) s := by
    intro s
    have h1 : HasDerivAt (fun s => g (a + s)) (q (a + s)) s := (hg (a + s)).comp_const_add a s
    have h2 := ((h1.sub_const (g a)).sub ((hasDerivAt_id' s).mul_const (q a))).add
      (((hasDerivAt_pow 2 s).const_mul L).div_const 2)
    refine h2.congr_deriv ?_
    simp; ring
  have hdiff : Differentiable ℝ ψ := fun s => (hd s).differentiableAt
  have hderiv : ∀ s, deriv ψ s = q (a + s) - q a + L * s := fun s => (hd s).deriv
  have h0 : ψ 0 = 0 := by simp [hψ]
  have key : 0 ≤ ψ s := by
    rcases le_total 0 s with hs | hs
    · have hm : MonotoneOn ψ (Set.Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hdiff.continuous.continuousOn
          hdiff.differentiableOn
        intro x hx
        rw [interior_Ici] at hx
        have hx' : 0 < x := hx
        rw [hderiv]
        have := hq (a + x) a
        have h3 := (abs_le.mp this).1
        rw [show a + x - a = x by ring, abs_of_pos hx'] at h3
        linarith
      have := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
      linarith
    · have hm : AntitoneOn ψ (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hdiff.continuous.continuousOn
          hdiff.differentiableOn
        intro x hx
        rw [interior_Iic] at hx
        have hx' : x < 0 := hx
        rw [hderiv]
        have := hq (a + x) a
        have h3 := (abs_le.mp this).2
        rw [show a + x - a = x by ring, abs_of_neg hx'] at h3
        linarith
      have := hm (Set.mem_Iic.mpr hs) (Set.mem_Iic.mpr le_rfl) hs
      linarith
  simp only [hψ] at key
  linarith

lemma taylor_abs (g q : ℝ → ℝ) (L : ℝ) (hg : ∀ t, HasDerivAt g (q t) t)
    (hq : ∀ x y, |q x - q y| ≤ L * |x - y|) (a s : ℝ) :
    |g (a + s) - g a - s * q a| ≤ L * s ^ 2 / 2 := by
  have h1 := taylor_lower g q L hg hq a s
  have h2 := taylor_lower (fun t => - g t) (fun t => - q t) L
    (fun t => (hg t).neg) (by intro x y; have := hq x y; rwa [show -q x - -q y = -(q x - q y) by ring, abs_neg]) a s
  beta_reduce at h2
  rw [abs_le]; constructor <;> linarith

end Taylor


section Cdf

lemma G_sub_of_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ → ℝ) (hp : Continuous p)
    (hp0 : ∀ t, 0 ≤ p t) (hμ : μ = volume.withDensity (fun t => ENNReal.ofReal (p t)))
    {a b : ℝ} (hab : a ≤ b) :
    μ.real (Set.Iic b) - μ.real (Set.Iic a) = ∫ x in a..b, p x := by
  have hU : Set.Iic b = Set.Iic a ∪ Set.Ioc a b := (Set.Iic_union_Ioc_eq_Iic hab).symm
  have hdisj : Disjoint (Set.Iic a) (Set.Ioc a b) := Set.disjoint_left.mpr
    (fun x hx hx' => absurd hx'.1 (not_lt.mpr hx))
  have h1 : μ (Set.Iic b) = μ (Set.Iic a) + μ (Set.Ioc a b) := by
    rw [hU, measure_union hdisj measurableSet_Ioc]
  have h2 : μ (Set.Ioc a b) = ENNReal.ofReal (∫ x in a..b, p x) := by
    rw [hμ, withDensity_apply _ measurableSet_Ioc, intervalIntegral.integral_of_le hab,
      ofReal_integral_eq_lintegral_ofReal]
    · exact hp.integrableOn_Ioc
    · exact Filter.Eventually.of_forall hp0
  have h3 : 0 ≤ ∫ x in a..b, p x := intervalIntegral.integral_nonneg hab (fun x _ => hp0 x)
  have h4 : μ.real (Set.Iic b) = μ.real (Set.Iic a) + ∫ x in a..b, p x := by
    simp only [Measure.real]
    rw [h1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h2,
      ENNReal.toReal_ofReal h3]
  linarith

lemma G_sub (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ → ℝ) (hp : Continuous p)
    (hp0 : ∀ t, 0 ≤ p t) (hμ : μ = volume.withDensity (fun t => ENNReal.ofReal (p t)))
    (a b : ℝ) :
    μ.real (Set.Iic b) - μ.real (Set.Iic a) = ∫ x in a..b, p x := by
  rcases le_total a b with h | h
  · exact G_sub_of_le μ p hp hp0 hμ h
  · have := G_sub_of_le μ p hp hp0 hμ h
    rw [intervalIntegral.integral_symm]; linarith

lemma G_hasDerivAt (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ → ℝ) (hp : Continuous p)
    (hp0 : ∀ t, 0 ≤ p t) (hμ : μ = volume.withDensity (fun t => ENNReal.ofReal (p t)))
    (t : ℝ) : HasDerivAt (fun u => μ.real (Set.Iic u)) (p t) t := by
  have h := ((hp.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (μ.real (Set.Iic 0))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => ?_))
  have := G_sub μ p hp hp0 hμ 0 u
  simp only; linarith

lemma p_lip (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) (L : ℝ) (hL : ∀ t, |deriv p t| ≤ L)
    (x y : ℝ) : |p x - p y| ≤ L * |x - y| := by
  have hd : ∀ t ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ p t :=
    fun t _ => (hp.differentiable (by norm_num)) t
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := p) (C := L) hd
    (fun t _ => by simpa using hL t) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

end Cdf


section Moments

open scoped RealInnerProductSpace

lemma inner_eq_sum {k : ℕ} (v y : EuclideanSpace ℝ (Fin k)) :
    ⟪v, y⟫ = ∑ j, v j * y j := by
  simp [PiLp.inner_apply, mul_comm]

lemma moments {k : ℕ} (v : EuclideanSpace ℝ (Fin k)) (hv : ‖v‖ = 1)
    (z : EuclideanSpace ℝ (Fin k)) (δ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → EuclideanSpace ℝ (Fin k))
    (hYind : iIndepFun (fun j ω => Y ω j) P)
    (hY2 : ∀ j, MemLp (fun ω => Y ω j) 2 P)
    (hYmean : ∀ j, ∫ ω, Y ω j ∂P = z j)
    (hYvar : ∀ j, ∫ ω, (Y ω j - z j) ^ 2 ∂P ≤ δ) :
    MemLp (fun ω => ⟪v, Y ω - z⟫) 2 P ∧ ∫ ω, ⟪v, Y ω - z⟫ ∂P = 0 ∧
      ∫ ω, ⟪v, Y ω - z⟫ ^ 2 ∂P ≤ δ := by
  set X : Fin k → Ω → ℝ := fun j ω => v j * Y ω j with hX
  have hXm : ∀ j, MemLp (X j) 2 P := fun j => (hY2 j).const_mul (v j)
  have hS : (fun ω => ⟪v, Y ω⟫) = ∑ j, X j := by
    ext ω; simp [inner_eq_sum, hX]
  have hSm : MemLp (∑ j, X j) 2 P := memLp_finsetSum' _ (fun j _ => hXm j)
  have hSint : ∫ ω, (∑ j, X j) ω ∂P = ⟪v, z⟫ := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun j _ => (hXm j).integrable one_le_two)]
    rw [inner_eq_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hX]
    rw [integral_const_mul, hYmean]
  have hcenter : (fun ω => ⟪v, Y ω - z⟫) = fun ω => (∑ j, X j) ω - ⟪v, z⟫ := by
    ext ω; rw [inner_sub_right, ← hS]
  have hconst : MemLp (fun _ : Ω => ⟪v, z⟫) 2 P := memLp_const _
  refine ⟨?_, ?_, ?_⟩
  · rw [hcenter]; exact hSm.sub hconst
  · rw [hcenter, integral_sub (hSm.integrable one_le_two) (integrable_const _), hSint]; simp
  · have hvar : variance (∑ j, X j) P = ∑ j, variance (X j) P := by
      refine IndepFun.variance_sum (s := Finset.univ) (fun j _ => hXm j) ?_
      intro i _ j _ hij
      have h1 := hYind.indepFun hij
      exact h1.comp (measurable_const_mul (v i)) (measurable_const_mul (v j))
    have hvarY : ∀ j, variance (X j) P ≤ v j ^ 2 * δ := by
      intro j
      have : X j = fun ω => v j * Y ω j := rfl
      rw [this]
      have := variance_const_mul (v j) (fun ω => Y ω j) P
      rw [show (fun ω => v j * Y ω j) = (fun ω => v j * (fun ω => Y ω j) ω) from rfl, this]
      gcongr
      rw [variance_eq_integral (hY2 j).aemeasurable]
      simp only [hYmean]
      exact hYvar j
    have hnorm : ∑ j, v j ^ 2 = 1 := by
      have := EuclideanSpace.norm_eq v
      rw [hv] at this
      have h2 : (1:ℝ) = Real.sqrt (∑ j, v j ^ 2) := by simpa using this
      have h3 : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
      have := Real.sq_sqrt h3
      rw [← h2] at this; linarith
    have hv2 : ∫ ω, ((∑ j, X j) ω - ⟪v, z⟫) ^ 2 ∂P = variance (∑ j, X j) P := by
      rw [variance_eq_integral hSm.aemeasurable, hSint]
    have hc2 : ∫ ω, ⟪v, Y ω - z⟫ ^ 2 ∂P = ∫ ω, ((∑ j, X j) ω - ⟪v, z⟫) ^ 2 ∂P := by
      have := congrFun hcenter
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [this ω]
    rw [hc2]
    calc ∫ ω, ((∑ j, X j) ω - ⟪v, z⟫) ^ 2 ∂P = variance (∑ j, X j) P := hv2
      _ = ∑ j, variance (X j) P := hvar
      _ ≤ ∑ j, v j ^ 2 * δ := Finset.sum_le_sum (fun j _ => hvarY j)
      _ = δ := by rw [← Finset.sum_mul, hnorm, one_mul]

end Moments


section Prob

open scoped RealInnerProductSpace

variable {n k : ℕ}

lemma meas_inner (v : EuclideanSpace ℝ (Fin k)) : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ⟪v, y⟫) :=
  (continuous_const.inner continuous_id).measurable

lemma meas_f {Ω : Type*} [MeasurableSpace Ω] (f : Finset (Fin n) → ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (Y : Ω → EuclideanSpace ℝ (Fin k)) (hY : Measurable Y)
    (τ : Ω → ℝ) (hτ : Measurable τ) :
    Measurable (fun ω => f (UniversalSubmod.threshSet v (Y ω) (τ ω))) := by
  classical
  have h1 : (fun ω => f (UniversalSubmod.threshSet v (Y ω) (τ ω))) =
      fun ω => ∑ T : Finset (Fin n), if UniversalSubmod.threshSet v (Y ω) (τ ω) = T then f T else 0 := by
    ext ω; simp
  rw [h1]
  refine Finset.measurable_sum _ (fun T _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {ω | UniversalSubmod.threshSet v (Y ω) (τ ω) = T} =
      ⋂ i : Fin n, {ω | (τ ω ≤ ⟪v i, Y ω⟫) ↔ i ∈ T} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff, UniversalSubmod.threshSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
  rw [this]
  refine MeasurableSet.iInter (fun i => ?_)
  have hm : MeasurableSet {ω | τ ω ≤ ⟪v i, Y ω⟫} :=
    measurableSet_le hτ ((meas_inner (v i)).comp hY)
  by_cases hi : i ∈ T
  · convert hm using 1
    ext ω; simp [hi]
  · convert hm.compl using 1
    ext ω; simp [hi]

lemma indep_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → EuclideanSpace ℝ (Fin k)) (hY : Measurable Y) (τ : Ω → ℝ) (hτ : Measurable τ)
    (hind : IndepFun Y τ P) (u : EuclideanSpace ℝ (Fin k)) :
    P.real {ω | τ ω ≤ ⟪u, Y ω⟫} = ∫ ω, (P.map τ).real (Set.Iic (⟪u, Y ω⟫)) ∂P := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hτ.aemeasurable).mp hind
  have hS : MeasurableSet {q : EuclideanSpace ℝ (Fin k) × ℝ | q.2 ≤ ⟪u, q.1⟫} :=
    measurableSet_le measurable_snd ((meas_inner u).comp measurable_fst)
  have hpre : {ω | τ ω ≤ ⟪u, Y ω⟫} = (fun ω => (Y ω, τ ω)) ⁻¹' {q | q.2 ≤ ⟪u, q.1⟫} := rfl
  have : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  have hmeas : Measurable (fun y : EuclideanSpace ℝ (Fin k) => (P.map τ) (Set.Iic (⟪u, y⟫))) :=
    measurable_measure_prodMk_left (ν := P.map τ) hS
  have h1 : P {ω | τ ω ≤ ⟪u, Y ω⟫} =
      ∫⁻ ω, (P.map τ) (Set.Iic (⟪u, Y ω⟫)) ∂P := by
    calc P {ω | τ ω ≤ ⟪u, Y ω⟫} = (P.map (fun ω => (Y ω, τ ω))) {q | q.2 ≤ ⟪u, q.1⟫} := by
          rw [Measure.map_apply (hY.prodMk hτ) hS]; rfl
      _ = ((P.map Y).prod (P.map τ)) {q | q.2 ≤ ⟪u, q.1⟫} := by rw [hprod]
      _ = ∫⁻ y, (P.map τ) (Set.Iic (⟪u, y⟫)) ∂(P.map Y) := Measure.prod_apply hS
      _ = ∫⁻ ω, (P.map τ) (Set.Iic (⟪u, Y ω⟫)) ∂P := lintegral_map hmeas hY
  have h2 : ∫ ω, (P.map τ).real (Set.Iic (⟪u, Y ω⟫)) ∂P =
      (∫⁻ ω, (P.map τ) (Set.Iic (⟪u, Y ω⟫)) ∂P).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => measureReal_nonneg))
      (hmeas.comp hY |>.ennreal_toReal.aestronglyMeasurable)]
    congr 1
    refine lintegral_congr (fun ω => ?_)
    simp [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [h2, ← h1]; rfl



lemma taylor_exp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → EuclideanSpace ℝ (Fin k)) (hY : Measurable Y)
    (hYind : iIndepFun (fun j ω => Y ω j) P)
    (hY2 : ∀ j, MemLp (fun ω => Y ω j) 2 P)
    (z : EuclideanSpace ℝ (Fin k)) (δ : ℝ)
    (hYmean : ∀ j, ∫ ω, Y ω j ∂P = z j)
    (hYvar : ∀ j, ∫ ω, (Y ω j - z j) ^ 2 ∂P ≤ δ)
    (G p : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hG : ∀ t, HasDerivAt G (p t) t)
    (hq : ∀ x y, |p x - p y| ≤ L * |x - y|) (hG0 : ∀ t, 0 ≤ G t) (hG1 : ∀ t, G t ≤ 1)
    (u : EuclideanSpace ℝ (Fin k)) (hu : ‖u‖ = 1) :
    |∫ ω, G (⟪u, Y ω⟫) ∂P - G (⟪u, z⟫)| ≤ L * δ / 2 := by
  obtain ⟨hm2, hm0, hm⟩ := moments u hu z δ P Y hYind hY2 hYmean hYvar
  set a := ⟪u, z⟫ with ha
  set h : Ω → ℝ := fun ω => ⟪u, Y ω - z⟫ with hh
  have hX : ∀ ω, ⟪u, Y ω⟫ = a + h ω := by
    intro ω; simp only [hh, ha, inner_sub_right]; ring
  have hGc : Continuous G := continuous_iff_continuousAt.mpr (fun t => (hG t).continuousAt)
  have hXm : Measurable (fun ω => ⟪u, Y ω⟫) := (meas_inner u).comp hY
  have hGint : Integrable (fun ω => G (⟪u, Y ω⟫)) P :=
    Integrable.of_bound (C := 1) ((hGc.measurable.comp hXm).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hG0 _)]; exact hG1 _))
  have hhint : Integrable h P := hm2.integrable one_le_two
  have hh2int : Integrable (fun ω => h ω ^ 2) P := hm2.integrable_sq
  have hpt : ∀ ω, ‖G (⟪u, Y ω⟫) - G a - h ω * p a‖ ≤ L * h ω ^ 2 / 2 := by
    intro ω
    have := taylor_abs G p L hG hq a (h ω)
    rw [Real.norm_eq_abs, hX ω]; exact this
  have hF : Integrable (fun ω => G (⟪u, Y ω⟫) - G a - h ω * p a) P :=
    (hGint.sub (integrable_const _)).sub (hhint.mul_const _)
  have i1 : Integrable (fun ω => G (⟪u, Y ω⟫) - G a) P := hGint.sub (integrable_const _)
  have i2 : Integrable (fun ω => h ω * p a) P := hhint.mul_const _
  have hFint : ∫ ω, (G (⟪u, Y ω⟫) - G a - h ω * p a) ∂P = ∫ ω, G (⟪u, Y ω⟫) ∂P - G a := by
    rw [integral_sub i1 i2, integral_sub hGint (integrable_const _), integral_mul_const]
    have : ∫ ω, h ω ∂P = 0 := hm0
    simp [this]
  have hg : Integrable (fun ω => L * h ω ^ 2 / 2) P := by
    have := hh2int.const_mul (L / 2)
    convert this using 2; ring
  have hbound := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)
  rw [hFint, Real.norm_eq_abs] at hbound
  have hc : ∫ ω, L * h ω ^ 2 / 2 ∂P = L / 2 * ∫ ω, h ω ^ 2 ∂P := by
    rw [← integral_const_mul]; congr 1; ext ω; ring
  have : L / 2 * ∫ ω, h ω ^ 2 ∂P ≤ L / 2 * δ := by gcongr
  linarith



lemma meas_set {Ω : Type*} [MeasurableSpace Ω] (v : EuclideanSpace ℝ (Fin k))
    (X : Ω → EuclideanSpace ℝ (Fin k)) (hX : Measurable X) (τ : Ω → ℝ) (hτ : Measurable τ) :
    MeasurableSet {ω | τ ω ≤ ⟪v, X ω⟫} :=
  measurableSet_le hτ ((meas_inner v).comp hX)

lemma int_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (X : Ω → EuclideanSpace ℝ (Fin k)) (hX : Measurable X)
    (τ : Ω → ℝ) (hτ : Measurable τ) (w : Fin n → ℝ) :
    ∫ ω, ∑ i, w i * ({ω | τ ω ≤ ⟪v i, X ω⟫}.indicator (1 : Ω → ℝ) ω) ∂P =
      ∑ i, w i * P.real {ω | τ ω ≤ ⟪v i, X ω⟫} := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, integral_indicator_one (meas_set (v i) X hX τ hτ)]
  · intro i _
    exact ((integrable_const (1 : ℝ)).indicator (meas_set (v i) X hX τ hτ)).const_mul _

lemma pt_sum {Ω : Type*} (w : Fin n → ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (X : Ω → EuclideanSpace ℝ (Fin k)) (τ : Ω → ℝ) (ω : Ω) :
    ∑ i ∈ UniversalSubmod.threshSet v (X ω) (τ ω), w i =
      ∑ i, w i * ({ω | τ ω ≤ ⟪v i, X ω⟫}.indicator (1 : Ω → ℝ) ω) := by
  classical
  unfold UniversalSubmod.threshSet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : τ ω ≤ ⟪v i, X ω⟫ <;> simp [h]

end Prob

end UniversalSubmod.Dev.Lemma26

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

theorem chk_lemma_2_6 {n k : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (z : EuclideanSpace ℝ (Fin k)) (δ : ℝ) (hδ : 0 ≤ δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → EuclideanSpace ℝ (Fin k)) (hY : Measurable Y)
    (hYind : iIndepFun (fun j ω => Y ω j) P)
    (hY2 : ∀ j, MemLp (fun ω => Y ω j) 2 P)
    (hYmean : ∀ j, ∫ ω, Y ω j ∂P = z j)
    (hYvar : ∀ j, ∫ ω, (Y ω j - z j) ^ 2 ∂P ≤ δ)
    (τ : Ω → ℝ) (hτ : Measurable τ) (hind : IndepFun Y τ P)
    (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) (hp0 : ∀ t, 0 ≤ p t)
    (hlaw : P.map τ = volume.withDensity (fun t => ENNReal.ofReal (p t)))
    (L : ℝ) (hL : ∀ t, |deriv p t| ≤ L) :
    ∫ ω, f (threshSet v z (τ ω)) ∂P - OPT f * L * δ ≤
      ∫ ω, f (threshSet v (Y ω) (τ ω)) ∂P := by
  classical
  have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hL 0)
  have hμprob : IsProbabilityMeasure (P.map τ) := Measure.isProbabilityMeasure_map hτ.aemeasurable
  set G : ℝ → ℝ := fun t => (P.map τ).real (Set.Iic t) with hGdef
  have hGd : ∀ t, HasDerivAt G (p t) t :=
    UniversalSubmod.Dev.Lemma26.G_hasDerivAt (P.map τ) p hp.continuous hp0 hlaw
  have hq := UniversalSubmod.Dev.Lemma26.p_lip p hp L hL
  have hG0 : ∀ t, 0 ≤ G t := fun t => measureReal_nonneg
  have hG1 : ∀ t, G t ≤ 1 := fun t => by
    simp only [hGdef]; exact measureReal_le_one
  obtain ⟨w, hw1, hw2, hw3⟩ := UniversalSubmod.Dev.Lemma26.comb f hf0 hf (fun i => ⟪v i, z⟫)
  have hfb : ∀ S, |f S| ≤ OPT f := fun S => by
    rw [abs_of_nonneg (hf0 S)]; exact Finset.le_sup' f (Finset.mem_univ S)
  have hmY := UniversalSubmod.Dev.Lemma26.meas_f f v Y hY τ hτ
  have hint : Integrable (fun ω => f (threshSet v (Y ω) (τ ω))) P :=
    Integrable.of_bound (C := OPT f) hmY.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hfb _))
  -- the z-side
  have hz : ∫ ω, f (threshSet v z (τ ω)) ∂P = f ∅ + ∑ i, w i * G (⟪v i, z⟫) := by
    have h1 : ∀ ω, f (threshSet v z (τ ω)) = f ∅ +
        ∑ i, w i * ({ω | τ ω ≤ ⟪v i, (fun _ => z) ω⟫}.indicator (1 : Ω → ℝ) ω) := by
      intro ω
      rw [← UniversalSubmod.Dev.Lemma26.pt_sum w v (fun _ => z) τ ω]
      have := hw2 (τ ω)
      unfold threshSet
      linarith
    have hI : ∀ i, Integrable ({ω | τ ω ≤ ⟪v i, (fun _ : Ω => z) ω⟫}.indicator (1 : Ω → ℝ)) P :=
      fun i => (integrable_const (1 : ℝ)).indicator
        (UniversalSubmod.Dev.Lemma26.meas_set (v i) (fun _ => z) measurable_const τ hτ)
    rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_add (integrable_const _),
      UniversalSubmod.Dev.Lemma26.int_sum P v (fun _ => z) measurable_const τ hτ w]
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      congr 1
      simp only [hGdef]
      rw [Measure.real, Measure.real, Measure.map_apply hτ measurableSet_Iic]
      rfl
    · exact integrable_finset_sum _ (fun i _ => (hI i).const_mul _)
  -- the Y-side
  have hI : ∀ i, Integrable ({ω | τ ω ≤ ⟪v i, Y ω⟫}.indicator (1 : Ω → ℝ)) P :=
    fun i => (integrable_const (1 : ℝ)).indicator
      (UniversalSubmod.Dev.Lemma26.meas_set (v i) Y hY τ hτ)
  have hlow : ∫ ω, (f ∅ + ∑ i, w i * ({ω | τ ω ≤ ⟪v i, Y ω⟫}.indicator (1 : Ω → ℝ) ω)) ∂P ≤
      ∫ ω, f (threshSet v (Y ω) (τ ω)) ∂P := by
    refine integral_mono ((integrable_const _).add
      (integrable_finset_sum _ (fun i _ => (hI i).const_mul _))) hint (fun ω => ?_)
    rw [← UniversalSubmod.Dev.Lemma26.pt_sum w v Y τ ω]
    have := hw1 (threshSet v (Y ω) (τ ω))
    linarith
  rw [integral_add (integrable_const _)
    (integrable_finset_sum _ (fun i _ => (hI i).const_mul _)),
    UniversalSubmod.Dev.Lemma26.int_sum P v Y hY τ hτ w] at hlow
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlow
  have hE : ∀ i, |∫ ω, G (⟪v i, Y ω⟫) ∂P - G (⟪v i, z⟫)| ≤ L * δ / 2 := fun i =>
    UniversalSubmod.Dev.Lemma26.taylor_exp P Y hY hYind hY2 z δ hYmean hYvar G p L hL0 hGd hq
      hG0 hG1 (v i) (hv i)
  have hterm : ∀ i, w i * G (⟪v i, z⟫) - |w i| * (L * δ / 2) ≤
      w i * P.real {ω | τ ω ≤ ⟪v i, Y ω⟫} := by
    intro i
    rw [UniversalSubmod.Dev.Lemma26.indep_prob P Y hY τ hτ hind (v i)]
    have h1 := neg_abs_le (w i * (∫ ω, G (⟪v i, Y ω⟫) ∂P - G (⟪v i, z⟫)))
    rw [abs_mul] at h1
    have h2 : |w i| * |∫ ω, G (⟪v i, Y ω⟫) ∂P - G (⟪v i, z⟫)| ≤ |w i| * (L * δ / 2) :=
      mul_le_mul_of_nonneg_left (hE i) (abs_nonneg _)
    have h3 : w i * (∫ ω, G (⟪v i, Y ω⟫) ∂P - G (⟪v i, z⟫)) =
      w i * (∫ ω, G (⟪v i, Y ω⟫) ∂P) - w i * G (⟪v i, z⟫) := by ring
    simp only [hGdef] at h3 ⊢
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  have hLd : 0 ≤ L * δ / 2 := by positivity
  have hfin : (∑ i, |w i|) * (L * δ / 2) ≤ 2 * OPT f * (L * δ / 2) :=
    mul_le_mul_of_nonneg_right hw3 hLd
  rw [hz]
  nlinarith [hsum, hfin, hlow]

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_lemma_2_6 := @UniversalSubmod.chk_lemma_2_6
