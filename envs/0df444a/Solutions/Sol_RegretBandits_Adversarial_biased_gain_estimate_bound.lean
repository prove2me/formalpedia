-- Prove2me | solution 1 for RegretBandits.Adversarial.biased_gain_estimate_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:27:39.136207+00:00
-- url     : https://prove2.me/submissions/495d7d16-8c74-4d8c-881d-f2476d95e7a7

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol

open MeasureTheory
open RegretBandits.Adversarial
open scoped ENNReal

namespace L31Aux

/-- `exp x ≤ 1 + x + x²` for `x ≤ 1`. -/
lemma exp_le_quad {x : ℝ} (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x ^ 2 := by
  by_cases h : -1 ≤ x
  · have h1 : |x| ≤ 1 := abs_le.2 ⟨h, hx⟩
    have := Real.abs_exp_sub_one_sub_id_le h1
    rw [abs_le] at this
    linarith [this.2]
  · push_neg at h
    have h1 : Real.exp x < 1 := Real.exp_lt_one_iff.2 (by linarith)
    nlinarith

/-- The one-step bound of Lemma 3.1 in two-point form. -/
lemma two_point {q G β : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hG0 : 0 ≤ G) (hG1 : G ≤ 1)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    q * Real.exp (β * (G - (G + β) / q)) + (1 - q) * Real.exp (β * (G - β / q)) ≤ 1 := by
  set u := β ^ 2 / q with hu
  set y0 := β * G with hy0
  set y1 := β * G - β * G / q with hy1
  have e0 : β * (G - β / q) = y0 - u := by rw [hy0, hu]; field_simp
  have e1 : β * (G - (G + β) / q) = y1 - u := by rw [hy1, hu]; field_simp; ring
  clear_value u y0 y1
  rw [e0, e1, Real.exp_sub, Real.exp_sub]
  have hy0le : y0 ≤ 1 := by rw [hy0]; nlinarith
  have hy1le : y1 ≤ 1 := by
    have : 0 ≤ β * G / q := by positivity
    linarith
  have h0 := exp_le_quad hy0le
  have h1 := exp_le_quad hy1le
  have hsum1 : q * y1 + (1 - q) * y0 = 0 := by rw [hy1, hy0]; field_simp; ring
  have hsum2 : q * y1 ^ 2 + (1 - q) * y0 ^ 2 = (β * G) ^ 2 * (1 / q - 1) := by
    rw [hy1, hy0]; field_simp; ring
  have hGsq : (β * G) ^ 2 * (1 / q - 1) ≤ u := by
    have h2 : (β * G) ^ 2 ≤ β ^ 2 := by
      rw [mul_pow]; have : G ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg β]
    have h3 : 0 ≤ 1 / q - 1 := by rw [sub_nonneg, le_div_iff₀ hq0]; linarith
    have h4 : (β * G) ^ 2 * (1 / q - 1) ≤ β ^ 2 * (1 / q - 1) := mul_le_mul_of_nonneg_right h2 h3
    have h5 : β ^ 2 * (1 / q - 1) ≤ u := by
      rw [hu]; have : 0 ≤ β ^ 2 := sq_nonneg β
      have : β ^ 2 * (1 / q - 1) = β ^ 2 / q - β ^ 2 := by field_simp
      linarith
    linarith
  have hS : q * Real.exp y1 + (1 - q) * Real.exp y0 ≤ 1 + u := by
    have a1 : q * Real.exp y1 ≤ q * (1 + y1 + y1 ^ 2) := mul_le_mul_of_nonneg_left h1 hq0.le
    have a2 : (1 - q) * Real.exp y0 ≤ (1 - q) * (1 + y0 + y0 ^ 2) :=
      mul_le_mul_of_nonneg_left h0 (by linarith)
    nlinarith
  have hexpu : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hpos : 0 < Real.exp u := Real.exp_pos u
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have : q * (Real.exp y1 * (Real.exp u)⁻¹) + (1 - q) * (Real.exp y0 * (Real.exp u)⁻¹) =
      (q * Real.exp y1 + (1 - q) * Real.exp y0) * (Real.exp u)⁻¹ := by ring
  rw [this]
  rw [← div_eq_mul_inv, div_le_one hpos]
  linarith

/-- The one-step bound: `∑_a q_a exp(β(G - (G 𝟙{a=i} + β)/q_i)) ≤ 1`. -/
lemma one_step {K : ℕ} (q : Fin K → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (i : Fin K)
    (hqi : 0 < q i) {G β : ℝ} (hG0 : 0 ≤ G) (hG1 : G ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∑ a, q a * Real.exp (β * (G - (G * (if a = i then 1 else 0) + β) / q i)) ≤ 1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : ∀ a ∈ Finset.univ.erase i,
      q a * Real.exp (β * (G - (G * (if a = i then 1 else 0) + β) / q i)) =
        q a * Real.exp (β * (G - β / q i)) := by
    intro a ha
    have : a ≠ i := Finset.ne_of_mem_erase ha
    simp [this]
  rw [Finset.sum_congr rfl hrest, ← Finset.sum_mul]
  have hs : ∑ a ∈ Finset.univ.erase i, q a = 1 - q i := by
    rw [← hq1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
  rw [hs]
  simp only [if_true, mul_one]
  have hqi1 : q i ≤ 1 := by
    rw [← hq1]
    exact Finset.single_le_sum (fun a _ => hq0 a) (Finset.mem_univ i)
  have := two_point hqi hqi1 hG0 hG1 hβ0 hβ1
  linarith

section cyl
variable {K : ℕ} (d : Fin K) {Ω : Type*} [MeasurableSpace Ω] (I : ℕ → Ω → Fin K)

/-- Extend a tuple of the first `m` actions to an action sequence. -/
def ext (m : ℕ) (c : Fin m → Fin K) : ℕ → Fin K :=
  fun s => if h : 1 ≤ s ∧ s ≤ m then c ⟨s - 1, by omega⟩ else d

/-- The cylinder `{I_1 = c_0, …, I_m = c_{m-1}}`. -/
def cyl (m : ℕ) (c : Fin m → Fin K) : Set Ω := {ω | ∀ j : Fin m, I (j.val + 1) ω = c j}

lemma ext_apply (m : ℕ) (c : Fin m → Fin K) (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ m) :
    ext d m c s = c ⟨s - 1, by omega⟩ := dif_pos ⟨h1, h2⟩

lemma cyl_meas (hI : ∀ t, Measurable (I t)) (m : ℕ) (c : Fin m → Fin K) :
    MeasurableSet (cyl I m c) := by
  have : cyl I m c = ⋂ j : Fin m, I (j.val + 1) ⁻¹' {c j} := by
    ext ω; simp [cyl]
  rw [this]
  exact MeasurableSet.iInter (fun j => hI _ (measurableSet_singleton _))

lemma ext_omega (m : ℕ) (ω : Ω) (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ m) :
    ext d m (fun j : Fin m => I (j.val + 1) ω) s = I s ω := by
  rw [ext_apply d m _ s h1 h2]
  show I (s - 1 + 1) ω = I s ω
  congr 1; omega

lemma mem_cyl_self (m : ℕ) (ω : Ω) : ω ∈ cyl I m (fun j : Fin m => I (j.val + 1) ω) :=
  fun _ => rfl

lemma eq_of_mem_cyl (m : ℕ) (ω : Ω) (c : Fin m → Fin K) (h : ω ∈ cyl I m c) :
    c = fun j : Fin m => I (j.val + 1) ω := by
  funext j; exact (h j).symm

lemma pointwise (m : ℕ) (F : (ℕ → Fin K) → ℝ≥0∞)
    (hF : ∀ h h' : ℕ → Fin K, (∀ s, 1 ≤ s → s ≤ m → h s = h' s) → F h = F h') (ω : Ω) :
    F (fun s => I s ω) = ∑ c : Fin m → Fin K, (cyl I m c).indicator (fun _ => F (ext d m c)) ω := by
  rw [Finset.sum_eq_single (fun j : Fin m => I (j.val + 1) ω)]
  · rw [Set.indicator_of_mem (mem_cyl_self I m ω)]
    apply hF
    intro s h1 h2
    exact (ext_omega d I m ω s h1 h2).symm
  · intro c _ hc
    rw [Set.indicator_of_notMem]
    intro hmem
    exact hc (eq_of_mem_cyl I m ω c hmem)
  · intro h; exact absurd (Finset.mem_univ _) h

include d in
lemma meas_dep (hI : ∀ t, Measurable (I t)) (m : ℕ) (F : (ℕ → Fin K) → ℝ≥0∞)
    (hF : ∀ h h' : ℕ → Fin K, (∀ s, 1 ≤ s → s ≤ m → h s = h' s) → F h = F h') :
    Measurable (fun ω => F (fun s => I s ω)) := by
  have : (fun ω => F (fun s => I s ω)) =
      fun ω => ∑ c : Fin m → Fin K, (cyl I m c).indicator (fun _ => F (ext d m c)) ω := by
    funext ω; exact pointwise d I m F hF ω
  rw [this]
  exact Finset.measurable_sum _ (fun c _ => measurable_const.indicator (cyl_meas I hI m c))

lemma lintegral_dep (P : Measure Ω) (hI : ∀ t, Measurable (I t)) (m : ℕ)
    (F : (ℕ → Fin K) → ℝ≥0∞)
    (hF : ∀ h h' : ℕ → Fin K, (∀ s, 1 ≤ s → s ≤ m → h s = h' s) → F h = F h') :
    ∫⁻ ω, F (fun s => I s ω) ∂P = ∑ c : Fin m → Fin K, F (ext d m c) * P (cyl I m c) := by
  simp_rw [pointwise d I m F hF]
  rw [lintegral_finsetSum _ (fun c _ => measurable_const.indicator (cyl_meas I hI m c))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  exact lintegral_indicator_const (cyl_meas I hI m c) _

lemma ext_snoc (m : ℕ) (c : Fin m → Fin K) (a : Fin K) (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ m) :
    ext d (m + 1) (Fin.snoc c a) s = ext d m c s := by
  rw [ext_apply d (m + 1) _ s h1 (by omega), ext_apply d m c s h1 h2]
  have hlt : s - 1 < m := by omega
  simp [Fin.snoc, hlt]

lemma ext_snoc_last (m : ℕ) (c : Fin m → Fin K) (a : Fin K) :
    ext d (m + 1) (Fin.snoc c a) (m + 1) = a := by
  rw [ext_apply d (m + 1) _ (m + 1) (by omega) le_rfl]
  simp [Fin.snoc]

lemma cyl_snoc (P : Measure Ω) (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hI : IsRun P p I) (m : ℕ)
    (c : Fin m → Fin K) (a : Fin K) :
    P (cyl I (m + 1) (Fin.snoc c a)) =
      P (cyl I m c) * ENNReal.ofReal (p (m + 1) (ext d (m + 1) (Fin.snoc c a)) a) := by
  have h := hI.2 (m + 1) (by omega) (ext d (m + 1) (Fin.snoc c a))
  rw [ext_snoc_last] at h
  have e1 : {ω | ∀ s, 1 ≤ s → s ≤ m + 1 → I s ω = ext d (m + 1) (Fin.snoc c a) s} =
      cyl I (m + 1) (Fin.snoc c a) := by
    ext ω
    simp only [Set.mem_setOf_eq, cyl]
    constructor
    · intro H j
      have := H (j.val + 1) (by omega) (by omega)
      rw [this, ext_apply d (m + 1) _ _ (by omega) (by omega)]
      congr 1
    · intro H s h1 h2
      rw [ext_apply d (m + 1) _ s h1 h2]
      have := H ⟨s - 1, by omega⟩
      simp only at this
      have hs : s - 1 + 1 = s := by omega
      rw [hs] at this
      exact this
  have e2 : {ω | ∀ s, 1 ≤ s → s < m + 1 → I s ω = ext d (m + 1) (Fin.snoc c a) s} =
      cyl I m c := by
    ext ω
    simp only [Set.mem_setOf_eq, cyl]
    constructor
    · intro H j
      have := H (j.val + 1) (by omega) (by omega)
      rw [this, ext_snoc d m c a _ (by omega) (by omega), ext_apply d m c _ (by omega) (by omega)]
      congr 1
    · intro H s h1 h2
      rw [ext_snoc d m c a s h1 (by omega), ext_apply d m c s h1 (by omega)]
      have := H ⟨s - 1, by omega⟩
      simp only at this
      have hs : s - 1 + 1 = s := by omega
      rw [hs] at this
      exact this
  rw [e1, e2] at h
  exact h

include d in
/-- Tower property for one round of a run. -/
lemma tower (P : Measure Ω) (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hrule : IsForecasterRule p)
    (hI : IsRun P p I) (m : ℕ) (A : (ℕ → Fin K) → ℝ≥0∞)
    (hA : ∀ h h' : ℕ → Fin K, (∀ s, 1 ≤ s → s ≤ m → h s = h' s) → A h = A h')
    (f : (ℕ → Fin K) → Fin K → ℝ≥0∞)
    (hf : ∀ h h' : ℕ → Fin K, (∀ s, 1 ≤ s → s ≤ m → h s = h' s) → f h = f h') :
    ∫⁻ ω, A (fun s => I s ω) * f (fun s => I s ω) (I (m + 1) ω) ∂P =
      ∫⁻ ω, A (fun s => I s ω) *
        ∑ a, ENNReal.ofReal (p (m + 1) (fun s => I s ω) a) * f (fun s => I s ω) a ∂P := by
  have L := lintegral_dep d I P hI.1 (m + 1) (fun h => A h * f h (h (m + 1))) (by
    intro h h' hh
    rw [hA h h' (fun s h1 h2 => hh s h1 (by omega)), hf h h' (fun s h1 h2 => hh s h1 (by omega)),
      hh (m + 1) (by omega) le_rfl])
  have R := lintegral_dep d I P hI.1 m
    (fun h => A h * ∑ a, ENNReal.ofReal (p (m + 1) h a) * f h a) (by
    intro h h' hh
    rw [hA h h' hh, hf h h' hh, hrule.2.2 (m + 1) h h' (fun s h1 h2 => hh s h1 (by omega))])
  rw [L, R]
  rw [← (Fin.snocEquiv (fun _ => Fin K)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [show (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin K)) (a, c) = Fin.snoc c a from rfl]
  have hag : ∀ s, 1 ≤ s → s ≤ m → ext d (m + 1) (Fin.snoc c a) s = ext d m c s :=
    fun s h1 h2 => ext_snoc d m c a s h1 h2
  rw [cyl_snoc d I P p hI m c a, ext_snoc_last, hA _ _ hag, hf _ _ hag,
    hrule.2.2 (m + 1) _ (ext d m c) (fun s h1 h2 => hag s h1 (by omega))]
  ring

end cyl

end L31Aux

open L31Aux in
theorem solution {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (g : Adversary K)
    (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hp : IsForecasterRule p) (i : Fin K)
    (hpos : ∀ t h, 0 < p t h i) (β δ : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K) (hI : IsRun P p I) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i ≤
        ∑ t ∈ Finset.Icc 1 n,
            (g.val t (fun s => I s ω) i * (if I t ω = i then 1 else 0) + β) /
              p t (fun s => I s ω) i +
          Real.log δ⁻¹ / β} := by
  let d : Fin K := ⟨0, by omega⟩
  let D : ℕ → (ℕ → Fin K) → ℝ := fun t h =>
    β * (g.val t h i - (g.val t h i * (if h t = i then 1 else 0) + β) / p t h i)
  let M : ℕ → (ℕ → Fin K) → ℝ := fun m h => ∑ t ∈ Finset.Icc 1 m, D t h
  have hMdep : ∀ m (h h' : ℕ → Fin K), (∀ s, 1 ≤ s → s ≤ m → h s = h' s) → M m h = M m h' := by
    intro m h h' hh
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have ht' : 1 ≤ t ∧ t ≤ m := by simpa using ht
    have hab : AgreeBefore t h h' := fun s h1 h2 => hh s h1 (by omega)
    show β * (g.val t h i - (g.val t h i * (if h t = i then 1 else 0) + β) / p t h i) =
      β * (g.val t h' i - (g.val t h' i * (if h' t = i then 1 else 0) + β) / p t h' i)
    rw [g.nonanticipating t h h' hab, hp.2.2 t h h' hab, hh t ht'.1 ht'.2]
  have claim : ∀ m, ∫⁻ ω, ENNReal.ofReal (Real.exp (M m (fun s => I s ω))) ∂P ≤ 1 := by
    intro m
    induction m with
    | zero =>
      have : ∀ h, M 0 h = 0 := fun h => by simp [M]
      simp [this]
    | succ m ih =>
      let A : (ℕ → Fin K) → ℝ≥0∞ := fun h => ENNReal.ofReal (Real.exp (M m h))
      let f : (ℕ → Fin K) → Fin K → ℝ≥0∞ := fun h a => ENNReal.ofReal (Real.exp
        (β * (g.val (m + 1) h i - (g.val (m + 1) h i * (if a = i then 1 else 0) + β) /
          p (m + 1) h i)))
      have hsplit : ∀ ω, ENNReal.ofReal (Real.exp (M (m + 1) (fun s => I s ω))) =
          A (fun s => I s ω) * f (fun s => I s ω) (I (m + 1) ω) := by
        intro ω
        have : M (m + 1) (fun s => I s ω) = M m (fun s => I s ω) + D (m + 1) (fun s => I s ω) := by
          simp only [M]
          rw [Finset.sum_Icc_succ_top (by omega)]
        rw [this, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      have hA : ∀ h h' : ℕ → Fin K, (∀ s, 1 ≤ s → s ≤ m → h s = h' s) → A h = A h' := by
        intro h h' hh; simp only [A]; rw [hMdep m h h' hh]
      have hf : ∀ h h' : ℕ → Fin K, (∀ s, 1 ≤ s → s ≤ m → h s = h' s) → f h = f h' := by
        intro h h' hh
        have hab : AgreeBefore (m + 1) h h' := fun s h1 h2 => hh s h1 (by omega)
        funext a
        simp only [f]
        rw [g.nonanticipating (m + 1) h h' hab, hp.2.2 (m + 1) h h' hab]
      simp_rw [hsplit]
      rw [tower d I P p hp hI m A hA f hf]
      have hbound : ∀ h, ∑ a, ENNReal.ofReal (p (m + 1) h a) * f h a ≤ 1 := by
        intro h
        have hnn : ∀ a ∈ Finset.univ, 0 ≤ p (m + 1) h a * Real.exp
            (β * (g.val (m + 1) h i - (g.val (m + 1) h i * (if a = i then 1 else 0) + β) /
              p (m + 1) h i)) := fun a _ => mul_nonneg (hp.1 _ _ _) (Real.exp_pos _).le
        have : ∑ a, ENNReal.ofReal (p (m + 1) h a) * f h a =
            ENNReal.ofReal (∑ a, p (m + 1) h a * Real.exp
              (β * (g.val (m + 1) h i - (g.val (m + 1) h i * (if a = i then 1 else 0) + β) /
                p (m + 1) h i))) := by
          rw [ENNReal.ofReal_sum_of_nonneg hnn]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          simp only [f]
          rw [ENNReal.ofReal_mul (hp.1 _ _ _)]
        rw [this, ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        exact one_step (p (m + 1) h) (hp.1 _ _) (hp.2.1 _ _) i (hpos _ _)
          (g.val_mem _ _ _).1 (g.val_mem _ _ _).2 hβ0 hβ1
      calc ∫⁻ ω, A (fun s => I s ω) *
            ∑ a, ENNReal.ofReal (p (m + 1) (fun s => I s ω) a) * f (fun s => I s ω) a ∂P
          ≤ ∫⁻ ω, A (fun s => I s ω) * 1 ∂P :=
            lintegral_mono (fun ω => by gcongr; exact hbound _)
        _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (M m (fun s => I s ω))) ∂P := by simp [A]
        _ ≤ 1 := ih
  -- Markov
  set L := Real.log δ⁻¹ with hL
  have hexpL : Real.exp L = δ⁻¹ := Real.exp_log (inv_pos.2 hδ0)
  set T := {ω | ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i ≤
        ∑ t ∈ Finset.Icc 1 n,
            (g.val t (fun s => I s ω) i * (if I t ω = i then 1 else 0) + β) /
              p t (fun s => I s ω) i + L / β} with hT
  have hsub : Tᶜ ⊆ {ω | ENNReal.ofReal δ⁻¹ ≤ ENNReal.ofReal (Real.exp (M n (fun s => I s ω)))} := by
    intro ω hω
    simp only [hT, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    simp only [Set.mem_setOf_eq]
    apply ENNReal.ofReal_le_ofReal
    rw [← hexpL]
    apply Real.exp_le_exp.2
    have hM : M n (fun s => I s ω) = β * (∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i -
        ∑ t ∈ Finset.Icc 1 n,
            (g.val t (fun s => I s ω) i * (if I t ω = i then 1 else 0) + β) /
              p t (fun s => I s ω) i) := by
      simp only [M, D]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hM]
    have : L / β < ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i -
        ∑ t ∈ Finset.Icc 1 n,
            (g.val t (fun s => I s ω) i * (if I t ω = i then 1 else 0) + β) /
              p t (fun s => I s ω) i := by linarith
    rw [div_lt_iff₀ hβ0] at this
    linarith
  have hmeas : Measurable (fun ω => ENNReal.ofReal (Real.exp (M n (fun s => I s ω)))) :=
    meas_dep d I hI.1 n (fun h => ENNReal.ofReal (Real.exp (M n h)))
      (fun h h' hh => by rw [hMdep n h h' hh])
  have hmk := mul_meas_ge_le_lintegral₀ hmeas.aemeasurable (μ := P) (ENNReal.ofReal δ⁻¹)
  have hTc : P Tᶜ ≤ ENNReal.ofReal δ := by
    have h1 : ENNReal.ofReal δ⁻¹ * P Tᶜ ≤ 1 :=
      (by gcongr : ENNReal.ofReal δ⁻¹ * P Tᶜ ≤ _).trans (hmk.trans (claim n))
    have hδinv : ENNReal.ofReal δ⁻¹ = (ENNReal.ofReal δ)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hδ0]
    rw [hδinv] at h1
    have hδne : ENNReal.ofReal δ ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; exact hδ0
    calc P Tᶜ = ENNReal.ofReal δ * ((ENNReal.ofReal δ)⁻¹ * P Tᶜ) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hδne ENNReal.ofReal_ne_top, one_mul]
      _ ≤ ENNReal.ofReal δ * 1 := by gcongr
      _ = ENNReal.ofReal δ := mul_one _
  have hun : (1 : ℝ≥0∞) ≤ P T + P Tᶜ := by
    calc (1 : ℝ≥0∞) = P (T ∪ Tᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ P T + P Tᶜ := measure_union_le _ _
  rw [ENNReal.ofReal_sub _ hδ0.le, ENNReal.ofReal_one]
  calc 1 - ENNReal.ofReal δ ≤ 1 - P Tᶜ := tsub_le_tsub_left hTc _
    _ ≤ P T := tsub_le_iff_right.2 hun
