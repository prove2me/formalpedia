-- Prove2me | solution 1 for UnderstandingML.rlm_oracle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T16:55:43.301538+00:00
-- url     : https://prove2.me/submissions/b610b8db-df31-46b0-88f4-a65efc125b76

import Definitions.Def_UnderstandingML_Convex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

namespace UMLStab

variable {Z : Type*} [MeasurableSpace Z]

/-- Replace-one swap: `(S, z') ↦ (S⁽ⁱ⁾, zᵢ)`. -/
def swapAt {m : ℕ} (i : Fin m) (p : (Fin m → Z) × Z) : (Fin m → Z) × Z :=
  (Function.update p.1 i p.2, p.1 i)

lemma measurable_swapAt {m : ℕ} (i : Fin m) : Measurable (swapAt (Z := Z) i) := by
  classical
  unfold swapAt
  exact (measurable_update' (a := i)).prodMk ((measurable_pi_apply i).comp measurable_fst)

/-- The replace-one swap preserves the law `D^m ⊗ D`. -/
theorem measurePreserving_swapAt (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (i : Fin m) :
    MeasurePreserving (swapAt i) ((iidLaw D m).prod D) ((iidLaw D m).prod D) := by
  classical
  refine ⟨measurable_swapAt i, ?_⟩
  have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  set C : Set (Set ((Fin m → Z) × Z)) :=
    Set.image2 (· ×ˢ ·) (Set.pi Set.univ '' Set.pi Set.univ fun _ ↦ {s : Set Z | MeasurableSet s})
      {t : Set Z | MeasurableSet t}
  refine ext_of_generate_finite C ?_ ?_ ?_ ?_
  · refine (generateFrom_eq_prod generateFrom_pi MeasurableSpace.generateFrom_measurableSet ?_
      isCountablySpanning_measurableSet).symm
    refine ⟨fun _ ↦ Set.univ.pi fun _ ↦ Set.univ, fun _ ↦ ⟨fun _ ↦ Set.univ,
      fun _ _ ↦ MeasurableSet.univ, rfl⟩, ?_⟩
    simp only [Set.pi_univ, Set.iUnion_const]
  · exact isPiSystem_pi.prod MeasurableSpace.isPiSystem_measurableSet
  · rintro _ ⟨_, ⟨s, hs, rfl⟩, t, ht, rfl⟩
    have hsi : ∀ j, MeasurableSet (s j) := fun j ↦ hs j (Set.mem_univ j)
    have hpre : swapAt i ⁻¹' (Set.univ.pi s ×ˢ t) =
        Set.univ.pi (Function.update s i t) ×ˢ s i := by
      ext ⟨S, z⟩
      simp only [swapAt, Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun j ↦ ?_, by simpa using h1 i⟩
        by_cases hj : j = i
        · subst hj; simpa using h2
        · simpa [Function.update_of_ne hj] using h1 j
      · rintro ⟨h1, h2⟩
        refine ⟨fun j ↦ ?_, by simpa using h1 i⟩
        by_cases hj : j = i
        · subst hj; simpa using h2
        · simpa [Function.update_of_ne hj] using h1 j
    have hmeasC : MeasurableSet (Set.univ.pi s ×ˢ t) :=
      (MeasurableSet.univ_pi hsi).prod ht
    rw [Measure.map_apply (measurable_swapAt i) hmeasC, hpre]
    unfold iidLaw
    rw [Measure.prod_prod, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
    have hupd : (fun j ↦ D (Function.update s i t j)) =
        Function.update (fun j ↦ D (s j)) i (D t) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [hupd, Finset.prod_update_of_mem (Finset.mem_univ i)]
    rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ D (s j)) (Finset.mem_univ i),
      Finset.sdiff_singleton_eq_erase]
    ring
  · rw [Measure.map_apply (measurable_swapAt i) MeasurableSet.univ, Set.preimage_univ]


lemma isProbabilityMeasure_iidLaw (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) :
    IsProbabilityMeasure (iidLaw D m) := by
  unfold iidLaw; infer_instance

lemma integral_comp_swapAt (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (i : Fin m)
    (g : (Fin m → Z) × Z → ℝ) (hg : AEStronglyMeasurable g ((iidLaw D m).prod D)) :
    ∫ p, g (swapAt i p) ∂((iidLaw D m).prod D) = ∫ p, g p ∂((iidLaw D m).prod D) := by
  have h := measurePreserving_swapAt D i
  have hg' : AEStronglyMeasurable g (Measure.map (swapAt i) ((iidLaw D m).prod D)) := by
    rw [h.map_eq]; exact hg
  rw [← integral_map h.measurable.aemeasurable hg', h.map_eq]

/-- Integral over `D^m ⊗ D` of a function of the first coordinate. -/
lemma integral_prod_fst (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ}
    (f : (Fin m → Z) → ℝ) :
    ∫ p, f p.1 ∂((iidLaw D m).prod D) = ∫ S, f S ∂(iidLaw D m) := by
  have := isProbabilityMeasure_iidLaw D m
  rw [integral_fun_fst]
  simp

/-- **General stability identity** (Theorem 13.2) for an algorithm on samples of size `m`
whose losses are bounded on its outputs. -/
theorem stability_identity_gen {d : ℕ} (loss : Vec d → Z → ℝ)
    (hmeas : Measurable (Function.uncurry loss)) {m : ℕ} (hm : 0 < m)
    (alg : (Fin m → Z) → Vec d) (halg : Measurable alg) {K : ℝ}
    (hK : ∀ S z, |loss (alg S) z| ≤ K) (D : Measure Z) [IsProbabilityMeasure D] :
    ∫ S, (risk loss D (alg S) - empRisk loss S (alg S)) ∂(iidLaw D m) =
      (∑ i, ∫ p : (Fin m → Z) × Z,
          (loss (alg (Function.update p.1 i p.2)) (p.1 i) - loss (alg p.1) (p.1 i))
            ∂((iidLaw D m).prod D)) / m := by
  have := isProbabilityMeasure_iidLaw D m
  set P := (iidLaw D m).prod D
  set g : (Fin m → Z) × Z → ℝ := fun p ↦ loss (alg p.1) p.2 with hg_def
  have hgm : Measurable g := hmeas.comp ((halg.comp measurable_fst).prodMk measurable_snd)
  have hgint : Integrable g P :=
    Integrable.of_bound hgm.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun p ↦ by simpa [Real.norm_eq_abs] using hK p.1 p.2)
  -- measurability of the pieces
  have hBm : ∀ i : Fin m, Measurable fun S : Fin m → Z ↦ loss (alg S) (S i) := fun i ↦
    hmeas.comp (halg.prodMk (measurable_pi_apply i))
  have hBint : ∀ i : Fin m, Integrable (fun S : Fin m → Z ↦ loss (alg S) (S i)) (iidLaw D m) :=
    fun i ↦ Integrable.of_bound (hBm i).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun S ↦ by simpa [Real.norm_eq_abs] using hK S (S i))
  have hBint' : ∀ i : Fin m, Integrable (fun p : (Fin m → Z) × Z ↦ loss (alg p.1) (p.1 i)) P :=
    fun i ↦ Integrable.of_bound ((hBm i).comp measurable_fst).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun p ↦ by simpa [Real.norm_eq_abs] using hK p.1 (p.1 i))
  have hAint : ∀ i : Fin m, Integrable
      (fun p : (Fin m → Z) × Z ↦ loss (alg (Function.update p.1 i p.2)) (p.1 i)) P := by
    intro i
    have : (fun p : (Fin m → Z) × Z ↦ loss (alg (Function.update p.1 i p.2)) (p.1 i)) =
        g ∘ swapAt i := rfl
    rw [this]
    exact Integrable.of_bound (hgm.comp (measurable_swapAt i)).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun p ↦ by
        simpa [Real.norm_eq_abs, g, swapAt] using hK (Function.update p.1 i p.2) (p.1 i))
  have hRm : StronglyMeasurable fun S : Fin m → Z ↦ risk loss D (alg S) :=
    hgm.stronglyMeasurable.integral_prod_right'
  have hRint : Integrable (fun S : Fin m → Z ↦ risk loss D (alg S)) (iidLaw D m) := by
    refine Integrable.of_bound hRm.aestronglyMeasurable K
      (Filter.Eventually.of_forall fun S ↦ ?_)
    unfold risk
    refine (norm_integral_le_of_norm_le_const (C := K) ?_).trans (by simp)
    exact Filter.Eventually.of_forall fun z ↦ by simpa [Real.norm_eq_abs] using hK S z
  have hEint : Integrable (fun S : Fin m → Z ↦ empRisk loss S (alg S)) (iidLaw D m) := by
    unfold empRisk
    exact (integrable_finset_sum _ fun i _ ↦ hBint i).div_const _
  -- (a) the risk term
  have hrisk : ∫ S, risk loss D (alg S) ∂(iidLaw D m) = ∫ p, g p ∂P := by
    rw [integral_prod _ hgint]; rfl
  -- (b) swapping
  have hswap : ∀ i : Fin m,
      ∫ p, loss (alg (Function.update p.1 i p.2)) (p.1 i) ∂P = ∫ p, g p ∂P := fun i ↦
    integral_comp_swapAt D i g hgm.aestronglyMeasurable
  -- (c) the empirical risk term
  have hemp : ∫ S, empRisk loss S (alg S) ∂(iidLaw D m) =
      (∑ i, ∫ p, loss (alg p.1) (p.1 i) ∂P) / m := by
    unfold empRisk
    rw [integral_div, integral_finset_sum _ fun i _ ↦ hBint i]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact (integral_prod_fst D (fun S ↦ loss (alg S) (S i))).symm
  rw [integral_sub hRint hEint, hrisk, hemp]
  have hsum : (∑ i, ∫ p : (Fin m → Z) × Z,
      (loss (alg (Function.update p.1 i p.2)) (p.1 i) - loss (alg p.1) (p.1 i)) ∂P) =
      ∑ i : Fin m, (∫ p, g p ∂P - ∫ p, loss (alg p.1) (p.1 i) ∂P) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_sub (hAint i) (hBint' i), hswap i]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma integrable_risk_comp {d : ℕ} (loss : Vec d → Z → ℝ)
    (hmeas : Measurable (Function.uncurry loss)) {m : ℕ}
    (alg : (Fin m → Z) → Vec d) (halg : Measurable alg) {K : ℝ}
    (hK : ∀ S z, |loss (alg S) z| ≤ K) (D : Measure Z) [IsProbabilityMeasure D] :
    Integrable (fun S ↦ risk loss D (alg S)) (iidLaw D m) := by
  have := isProbabilityMeasure_iidLaw D m
  have hgm : Measurable fun p : (Fin m → Z) × Z ↦ loss (alg p.1) p.2 :=
    hmeas.comp ((halg.comp measurable_fst).prodMk measurable_snd)
  have hRm : StronglyMeasurable fun S : Fin m → Z ↦ risk loss D (alg S) :=
    hgm.stronglyMeasurable.integral_prod_right'
  refine Integrable.of_bound hRm.aestronglyMeasurable K
    (Filter.Eventually.of_forall fun S ↦ ?_)
  unfold risk
  refine (norm_integral_le_of_norm_le_const (C := K) ?_).trans (by simp)
  exact Filter.Eventually.of_forall fun z ↦ by simpa [Real.norm_eq_abs] using hK S z

lemma integrable_empRisk_comp {d : ℕ} (loss : Vec d → Z → ℝ)
    (hmeas : Measurable (Function.uncurry loss)) {m : ℕ}
    (alg : (Fin m → Z) → Vec d) (halg : Measurable alg) {K : ℝ}
    (hK : ∀ S z, |loss (alg S) z| ≤ K) (D : Measure Z) [IsProbabilityMeasure D] :
    Integrable (fun S ↦ empRisk loss S (alg S)) (iidLaw D m) := by
  have := isProbabilityMeasure_iidLaw D m
  unfold empRisk
  refine (integrable_finset_sum _ fun i _ ↦ ?_).div_const _
  exact Integrable.of_bound (hmeas.comp (halg.prodMk (measurable_pi_apply i))).aestronglyMeasurable
    K (Filter.Eventually.of_forall fun S ↦ by simpa [Real.norm_eq_abs] using hK S (S i))

end UMLStab

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

namespace UMLStab

variable {Z : Type*} [MeasurableSpace Z] {d : ℕ}

/-- Growth of a strongly convex function away from a minimizer (Lemma 13.5 (3)). -/
lemma strong_min_growth {lam : ℝ} {f : Vec d → ℝ} {u : Vec d}
    (hf : StrongConvexOn Set.univ lam f) (hmin : ∀ w, f u ≤ f w) (w : Vec d) :
    lam / 2 * ‖w - u‖ ^ 2 ≤ f w - f u := by
  set r := ‖w - u‖ ^ 2 with hr
  have hX : 0 ≤ f w - f u := sub_nonneg.2 (hmin w)
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → (1 - t) * (lam / 2 * r) ≤ f w - f u := by
    intro t ht0 ht1
    have h := hf.2 (Set.mem_univ w) (Set.mem_univ u) ht0.le (sub_nonneg.2 ht1)
      (by ring : t + (1 - t) = 1)
    have hu := hmin (t • w + (1 - t) • u)
    simp only [smul_eq_mul] at h
    have : t * ((1 - t) * (lam / 2 * r)) ≤ t * (f w - f u) := by
      rw [hr]; nlinarith
    exact le_of_mul_le_mul_left this ht0
  by_contra hcon'
  have hcon := lt_of_not_ge hcon'
  have hY : 0 < lam / 2 * r := lt_of_le_of_lt hX hcon
  set Y := lam / 2 * r
  set X := f w - f u
  have ht0 : 0 < (Y - X) / (2 * Y) := div_pos (by linarith) (by linarith)
  have ht1 : (Y - X) / (2 * Y) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have := key _ ht0 ht1
  have e : (1 - (Y - X) / (2 * Y)) * Y = (X + Y) / 2 := by
    field_simp; ring
  rw [e] at this
  linarith

lemma convexOn_empRisk (loss : Vec d → Z → ℝ) (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z))
    {m : ℕ} (S : Fin m → Z) : ConvexOn ℝ Set.univ (fun w ↦ empRisk loss S w) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have h : ∀ i, loss (a • x + b • y) (S i) ≤ a * loss x (S i) + b * loss y (S i) := fun i ↦ by
    simpa [smul_eq_mul] using (hconv (S i)).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul]
  unfold empRisk
  rw [mul_div_assoc', mul_div_assoc', ← add_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ ↦ h i) (Nat.cast_nonneg _)

/-- The RLM objective is `2λ`-strongly convex. -/
lemma strongConvexOn_rlmObjective (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) (lam : ℝ) {m : ℕ} (S : Fin m → Z) :
    StrongConvexOn Set.univ (2 * lam) (fun w ↦ rlmObjective loss lam S w) := by
  rw [strongConvexOn_iff_convex]
  have : (fun x : Vec d ↦ rlmObjective loss lam S x - 2 * lam / 2 * ‖x‖ ^ 2) =
      fun w ↦ empRisk loss S w := by
    funext x; unfold rlmObjective; ring
  rw [this]
  exact convexOn_empRisk loss hconv S

/-- Strong-convexity growth for an RLM output: `λ‖v − u‖² ≤ f_S(v) − f_S(u)`. -/
lemma rlm_growth (loss : Vec d → Z → ℝ) (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z))
    {lam : ℝ} {m : ℕ} {S : Fin m → Z} {u : Vec d} (hu : IsRLM loss lam S u) (v : Vec d) :
    lam * ‖v - u‖ ^ 2 ≤ rlmObjective loss lam S v - rlmObjective loss lam S u := by
  have := strong_min_growth (strongConvexOn_rlmObjective loss hconv lam S) hu v
  linarith

/-- Effect of replacing one example on the empirical risk. -/
lemma empRisk_update (loss : Vec d → Z → ℝ) {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z)
    (w : Vec d) :
    empRisk loss S w - empRisk loss (Function.update S i z') w =
      (loss w (S i) - loss w z') / m := by
  classical
  unfold empRisk
  rw [← sub_div]
  congr 1
  have h1 : (fun j ↦ loss w (Function.update S i z' j)) =
      Function.update (fun j ↦ loss w (S j)) i (loss w z') := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [h1, Finset.sum_update_of_mem (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ (fun j ↦ loss w (S j)) (Finset.mem_univ i),
    Finset.sdiff_singleton_eq_erase]
  ring

/-- The replace-one inequality: with `u = A(S)` and `v = A(S⁽ⁱ⁾)`,
`λ‖v − u‖² ≤ (ℓ(v, zᵢ) − ℓ(u, zᵢ) + ℓ(u, z') − ℓ(v, z')) / m`. -/
lemma rlm_replace_one (loss : Vec d → Z → ℝ) (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z))
    {lam : ℝ} {m : ℕ} {S : Fin m → Z} {i : Fin m} {z' : Z} {u v : Vec d}
    (hu : IsRLM loss lam S u) (hv : IsRLM loss lam (Function.update S i z') v) :
    lam * ‖v - u‖ ^ 2 ≤
      (loss v (S i) - loss u (S i) + loss u z' - loss v z') / m := by
  have h1 := rlm_growth loss hconv hu v
  have h2 := hv u
  have e1 := empRisk_update loss S i z' v
  have e2 := empRisk_update loss S i z' u
  unfold rlmObjective at h1 h2
  have : (loss v (S i) - loss u (S i) + loss u z' - loss v z') / m =
      (loss v (S i) - loss v z') / m - (loss u (S i) - loss u z') / m := by ring
  rw [this, ← e1, ← e2]
  linarith

/-- **Pointwise replace-one stability for Lipschitz losses** (Corollary 13.6). -/
lemma rlm_lipschitz_pointwise (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) {ρ : ℝ} (hlip : IsLipschitzLoss ρ loss)
    {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 0 < m) {S : Fin m → Z} {i : Fin m} {z' : Z}
    {u v : Vec d} (hu : IsRLM loss lam S u) (hv : IsRLM loss lam (Function.update S i z') v) :
    loss v (S i) - loss u (S i) ≤ 2 * ρ ^ 2 / (lam * m) := by
  have key := rlm_replace_one loss hconv hu hv
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set r := ‖v - u‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have l1 : loss v (S i) - loss u (S i) ≤ ρ * r := (le_abs_self _).trans (hlip (S i) v u)
  have l2 : loss u z' - loss v z' ≤ ρ * r := by
    have := hlip z' u v
    rw [norm_sub_rev] at this
    exact (le_abs_self _).trans this
  have hρr : 0 ≤ ρ * r := (abs_nonneg _).trans (hlip (S i) v u)
  have hc : 0 ≤ 2 * ρ ^ 2 / (lam * m) := by positivity
  rcases hr0.eq_or_lt with h0 | hpos
  · -- `v = u`
    have : loss v (S i) - loss u (S i) ≤ 0 := by
      have := hlip (S i) v u
      rw [← hr, ← h0, mul_zero] at this
      exact (le_abs_self _).trans this
    linarith
  · have hρ : 0 ≤ ρ := by
      by_contra hneg
      have : ρ * r < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
      linarith
    -- `λ r² ≤ 2ρ r / m`, so `r ≤ 2ρ/(λ m)`
    have h1 : lam * r ^ 2 ≤ 2 * ρ * r / m := by
      calc lam * r ^ 2 ≤ (loss v (S i) - loss u (S i) + loss u z' - loss v z') / m := key
        _ ≤ 2 * ρ * r / m := by
          apply div_le_div_of_nonneg_right _ hmR.le
          linarith
    have h2 : r ≤ 2 * ρ / (lam * m) := by
      rw [le_div_iff₀ (by positivity)]
      have : lam * r ^ 2 * m ≤ 2 * ρ * r := by
        rw [le_div_iff₀ hmR] at h1; linarith
      nlinarith
    calc loss v (S i) - loss u (S i) ≤ ρ * r := l1
      _ ≤ ρ * (2 * ρ / (lam * m)) := mul_le_mul_of_nonneg_left h2 hρ
      _ = 2 * ρ ^ 2 / (lam * m) := by ring

/-- Outputs of RLM with a nonnegative loss bounded by `C` at the origin satisfy
`λ‖A(S)‖² ≤ C`. -/
lemma rlm_norm_sq_le (loss : Vec d → Z → ℝ) (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ}
    (hC : ∀ z, loss 0 z ≤ C) {lam : ℝ} {m : ℕ} (hm : 0 < m) {S : Fin m → Z} {u : Vec d}
    (hu : IsRLM loss lam S u) : lam * ‖u‖ ^ 2 ≤ C := by
  have h := hu 0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold rlmObjective at h
  have hL0 : empRisk loss S 0 ≤ C := by
    unfold empRisk
    rw [div_le_iff₀ hmR]
    calc ∑ i, loss 0 (S i) ≤ ∑ _i : Fin m, C := Finset.sum_le_sum fun i _ ↦ hC (S i)
      _ = C * m := by simp [mul_comm]
  have hLu : 0 ≤ empRisk loss S u := by
    unfold empRisk
    exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hnonneg u (S i)) hmR.le
  simp at h
  linarith

lemma rlm_norm_le (loss : Vec d → Z → ℝ) (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ}
    (hC : ∀ z, loss 0 z ≤ C) {lam : ℝ} (hlam : 0 < lam) {m : ℕ} (hm : 0 < m) {S : Fin m → Z}
    {u : Vec d} (hu : IsRLM loss lam S u) : ‖u‖ ≤ Real.sqrt (C / lam) := by
  have h := rlm_norm_sq_le loss hnonneg hC hm hu
  rw [← Real.sqrt_sq (norm_nonneg u)]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ hlam]; linarith

/-- A Lipschitz loss is bounded on the outputs of RLM. -/
lemma rlm_lipschitz_loss_bound (loss : Vec d → Z → ℝ) (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ}
    (hC : ∀ z, loss 0 z ≤ C) {ρ : ℝ} (hlip : IsLipschitzLoss ρ loss) {lam : ℝ} (hlam : 0 < lam)
    {m : ℕ} (hm : 0 < m) {S : Fin m → Z} {u : Vec d} (hu : IsRLM loss lam S u) (z : Z) :
    |loss u z| ≤ C + |ρ| * Real.sqrt (C / lam) := by
  rw [abs_of_nonneg (hnonneg u z)]
  have h1 := hlip z u 0
  rw [sub_zero] at h1
  have h2 := rlm_norm_le loss hnonneg hC hlam hm hu
  have h3 : loss u z - loss 0 z ≤ |ρ| * ‖u‖ :=
    (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self ρ) (norm_nonneg _)))
  have h4 : |ρ| * ‖u‖ ≤ |ρ| * Real.sqrt (C / lam) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  linarith [hC z]

/-- If `f ≤ c` pointwise and `c ≥ 0`, then `∫ f ≤ c` for a probability measure (whether or not
`f` is integrable). -/
lemma integral_le_of_forall_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : α → ℝ} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x, f x ≤ c) :
    ∫ x, f x ∂μ ≤ c := by
  by_cases hint : Integrable f μ
  · calc ∫ x, f x ∂μ ≤ ∫ _x, c ∂μ := integral_mono hint (integrable_const c) hf
      _ = c := by simp
  · rw [integral_undef hint]; exact hc

/-- The replace-one average is at most `c` when each replace-one difference is. -/
lemma replace_one_avg_le {m : ℕ} (hm : 0 < m) (D : Measure Z) [IsProbabilityMeasure D]
    (F : Fin m → (Fin m → Z) × Z → ℝ) {c : ℝ} (hc : 0 ≤ c) (hF : ∀ i p, F i p ≤ c) :
    (∑ i, ∫ p, F i p ∂((iidLaw D m).prod D)) / m ≤ c := by
  have := isProbabilityMeasure_iidLaw D m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hmR]
  calc (∑ i, ∫ p, F i p ∂((iidLaw D m).prod D)) ≤ ∑ _i : Fin m, c :=
        Finset.sum_le_sum fun i _ ↦ integral_le_of_forall_le _ hc (hF i)
    _ = c * m := by simp [mul_comm]

/-- `E_S[L_S(w)] = L_D(w)` for a fixed hypothesis. -/
lemma integral_empRisk_const (loss : Vec d → Z → ℝ) (hmeas : Measurable (Function.uncurry loss))
    (D : Measure Z) [IsProbabilityMeasure D] {m : ℕ} (hm : 0 < m) (w : Vec d)
    (hint : Integrable (fun z ↦ loss w z) D) :
    ∫ S, empRisk loss S w ∂(iidLaw D m) = risk loss D w := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hw : Measurable fun z ↦ loss w z := hmeas.comp (measurable_const.prodMk measurable_id)
  unfold empRisk iidLaw
  rw [integral_div]
  have : ∀ i : Fin m, ∫ S : Fin m → Z, loss w (S i) ∂Measure.pi (fun _ ↦ D) = risk loss D w :=
    fun i ↦ integral_comp_eval (μ := fun _ ↦ D) (f := fun z ↦ loss w z) hw.aestronglyMeasurable
  rw [integral_finset_sum _ fun i _ ↦ integrable_comp_eval (μ := fun _ ↦ D) (i := i) hint]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end UMLStab

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

namespace UMLStab

variable {Z : Type*} [MeasurableSpace Z] {d : ℕ}

/-- Expected generalization gap of RLM with a convex Lipschitz loss (Corollary 13.6),
for a fixed sample size. -/
theorem lip_gap_bound (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) {ρ : ℝ}
    (hlip : IsLipschitzLoss ρ loss) {lam : ℝ} (hlam : 0 < lam)
    (hmeas : Measurable (Function.uncurry loss)) (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ}
    (hC : ∀ z, loss 0 z ≤ C) {m : ℕ} (hm : 0 < m) (alg : (Fin m → Z) → Vec d)
    (hA : ∀ S, IsRLM loss lam S (alg S)) (halg : Measurable alg)
    (D : Measure Z) [IsProbabilityMeasure D] :
    ∫ S, (risk loss D (alg S) - empRisk loss S (alg S)) ∂(iidLaw D m) ≤
      2 * ρ ^ 2 / (lam * m) := by
  rw [stability_identity_gen loss hmeas hm alg halg
    (fun S z ↦ rlm_lipschitz_loss_bound loss hnonneg hC hlip hlam hm (hA S) z) D]
  exact replace_one_avg_le hm D _ (by positivity) fun i p ↦
    rlm_lipschitz_pointwise loss hconv hlip hlam hm (hA p.1) (hA _)

/-- **Oracle inequality** (Corollary 13.8), for a fixed sample size. -/
theorem lip_oracle (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) {ρ : ℝ}
    (hlip : IsLipschitzLoss ρ loss) {lam : ℝ} (hlam : 0 < lam)
    (hmeas : Measurable (Function.uncurry loss)) (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ}
    (hC : ∀ z, loss 0 z ≤ C) {m : ℕ} (hm : 0 < m) (alg : (Fin m → Z) → Vec d)
    (hA : ∀ S, IsRLM loss lam S (alg S)) (halg : Measurable alg)
    (D : Measure Z) [IsProbabilityMeasure D] (wstar : Vec d) :
    ∫ S, risk loss D (alg S) ∂(iidLaw D m) ≤
      risk loss D wstar + lam * ‖wstar‖ ^ 2 + 2 * ρ ^ 2 / (lam * m) := by
  have := isProbabilityMeasure_iidLaw D m
  have hK := fun S z ↦ rlm_lipschitz_loss_bound loss hnonneg hC hlip hlam hm (hA S) z
  have hR := integrable_risk_comp loss hmeas alg halg hK D
  have hE := integrable_empRisk_comp loss hmeas alg halg hK D
  have hgap := lip_gap_bound loss hconv hlip hlam hmeas hnonneg hC hm alg hA halg D
  -- the fixed hypothesis `wstar`
  have hKw : ∀ (S : Fin m → Z) z, |loss ((fun _ ↦ wstar) S) z| ≤ C + |ρ| * ‖wstar‖ := by
    intro S z
    rw [abs_of_nonneg (hnonneg _ z)]
    have h1 := hlip z wstar 0
    rw [sub_zero] at h1
    have : loss wstar z - loss 0 z ≤ |ρ| * ‖wstar‖ :=
      (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self ρ) (norm_nonneg _)))
    linarith [hC z]
  have hEw := integrable_empRisk_comp loss hmeas (fun _ ↦ wstar) measurable_const hKw D
  have hwint : Integrable (fun z ↦ loss wstar z) D :=
    Integrable.of_bound (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (C + |ρ| * ‖wstar‖) (Filter.Eventually.of_forall fun z ↦ by
        simpa [Real.norm_eq_abs] using hKw (fun _ ↦ z) z)
  have hLS : ∫ S, empRisk loss S (alg S) ∂(iidLaw D m) ≤ risk loss D wstar + lam * ‖wstar‖ ^ 2 := by
    calc ∫ S, empRisk loss S (alg S) ∂(iidLaw D m)
        ≤ ∫ S, (empRisk loss S wstar + lam * ‖wstar‖ ^ 2) ∂(iidLaw D m) := by
          refine integral_mono hE (hEw.add (integrable_const _)) fun S ↦ ?_
          have h1 := hA S wstar
          unfold rlmObjective at h1
          have : 0 ≤ lam * ‖alg S‖ ^ 2 := by positivity
          simp only
          linarith
      _ = risk loss D wstar + lam * ‖wstar‖ ^ 2 := by
          rw [integral_add hEw (integrable_const _), integral_const,
            integral_empRisk_const loss hmeas D hm wstar hwint]
          simp
  have hsplit : ∫ S, risk loss D (alg S) ∂(iidLaw D m) =
      ∫ S, (risk loss D (alg S) - empRisk loss S (alg S)) ∂(iidLaw D m) +
        ∫ S, empRisk loss S (alg S) ∂(iidLaw D m) := by
    rw [integral_sub hR hE]; ring
  rw [hsplit]
  linarith

end UMLStab

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) {ρ : ℝ}
    (hlip : IsLipschitzLoss ρ loss) {lam : ℝ} (hlam : 0 < lam) (A : Learner Z (Vec d))
    (hA : IsRLMLearner loss lam A) (hmeas : Measurable (Function.uncurry loss))
    (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ} (hC : ∀ z, loss 0 z ≤ C)
    (hAmeas : ∀ m, Measurable (A m)) (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ)
    (hm : 0 < m) (wstar : Vec d) :
    ∫ S, risk loss D (A m S) ∂(iidLaw D m) ≤
      risk loss D wstar + lam * ‖wstar‖ ^ 2 + 2 * ρ ^ 2 / (lam * m) :=
  UMLStab.lip_oracle loss hconv hlip hlam hmeas hnonneg hC hm (A m) (hA m) (hAmeas m) D wstar
