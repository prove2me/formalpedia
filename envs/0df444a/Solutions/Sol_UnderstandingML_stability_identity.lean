-- Prove2me | solution 1 for UnderstandingML.stability_identity
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T16:48:05.637212+00:00
-- url     : https://prove2.me/submissions/6926f7d0-7b2f-4fec-bcb2-de3888a91ce3

import Definitions.Def_UnderstandingML_Convex
import Mathlib.MeasureTheory.Integral.Prod

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

end UMLStab

open MeasureTheory
open scoped InnerProductSpace
open UnderstandingML

theorem solution {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hmeas : Measurable (Function.uncurry loss)) {C : ℝ} (hbdd : ∀ w z, |loss w z| ≤ C)
    (A : Learner Z (Vec d)) (hA : ∀ m, Measurable (A m)) (D : Measure Z)
    [IsProbabilityMeasure D] (m : ℕ) (hm : 0 < m) :
    ∫ S, (risk loss D (A m S) - empRisk loss S (A m S)) ∂(iidLaw D m) =
      (∑ i, ∫ p : (Fin m → Z) × Z,
          (loss (A m (Function.update p.1 i p.2)) (p.1 i) - loss (A m p.1) (p.1 i))
            ∂((iidLaw D m).prod D)) / m :=
  UMLStab.stability_identity_gen loss hmeas hm (A m) (hA m) (fun S z ↦ hbdd (A m S) z) D
