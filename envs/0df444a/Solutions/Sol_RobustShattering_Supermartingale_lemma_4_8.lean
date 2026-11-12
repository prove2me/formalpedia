-- Prove2me | solution 1 for RobustShattering.Supermartingale.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:35:57.729907+00:00
-- url     : https://prove2.me/submissions/0ffe7575-0336-4223-84f4-8c7bcf183679

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_Shatterable

section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace RobustShattering.Dev.L48

open ProbabilityTheory

theorem lint_mul_of_disjoint {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ u, MeasurableSpace (α u)] (ν : ∀ u, Measure (α u)) [∀ u, IsProbabilityMeasure (ν u)]
    (x0 : ∀ u, α u) (A A' : Finset ι) (hd : Disjoint A A') (g h : (∀ u, α u) → ℝ≥0∞)
    (hg : Measurable g) (hh : Measurable h)
    (hgd : ∀ x y : ∀ u, α u, (∀ u ∈ A, x u = y u) → g x = g y)
    (hhd : ∀ x y : ∀ u, α u, (∀ u ∈ A', x u = y u) → h x = h y) :
    ∫⁻ x, g x * h x ∂(Measure.pi ν) = (∫⁻ x, g x ∂(Measure.pi ν)) * ∫⁻ x, h x ∂(Measure.pi ν) := by
  classical
  have hind : iIndepFun (fun (u : ι) (x : ∀ u, α u) => (id : α u → α u) (x u)) (Measure.pi ν) :=
    iIndepFun_pi (fun u => measurable_id.aemeasurable)
  have hI := hind.indepFun_finset A A' hd (fun u => measurable_pi_apply u)
  let ex : ∀ (B : Finset ι), (∀ i : B, α i) → ∀ u, α u :=
    fun B z u => if hu : u ∈ B then z ⟨u, hu⟩ else x0 u
  have hex : ∀ B : Finset ι, Measurable (ex B) := by
    intro B
    refine measurable_pi_iff.2 fun u => ?_
    by_cases hu : u ∈ B
    · simp only [ex, hu, dite_true]
      exact measurable_pi_apply _
    · simp only [ex, hu, dite_false]
      exact measurable_const
  have e1 : ∀ x : ∀ u, α u, g x = g (ex A (fun i : A => x i)) := by
    intro x
    apply hgd
    intro u hu
    simp [ex, hu]
  have e2 : ∀ x : ∀ u, α u, h x = h (ex A' (fun i : A' => x i)) := by
    intro x
    apply hhd
    intro u hu
    simp [ex, hu]
  have hX : Measurable (fun (x : ∀ u, α u) (i : A) => x i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hY : Measurable (fun (x : ∀ u, α u) (i : A') => x i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hI' := hI.comp (hg.comp (hex A)) (hh.comp (hex A'))
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    ((hg.comp (hex A)).comp hX) ((hh.comp (hex A')).comp hY) hI'
  simp only [Pi.mul_apply, Function.comp_def] at this
  simp only [← e1, ← e2] at this
  exact this

theorem lint_prod_disjoint {ι κ : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ u, MeasurableSpace (α u)] (ν : ∀ u, Measure (α u)) [∀ u, IsProbabilityMeasure (ν u)]
    (x0 : ∀ u, α u) (S : Finset κ) (A : κ → Finset ι) (hA : (S : Set κ).PairwiseDisjoint A)
    (f : κ → (∀ u, α u) → ℝ≥0∞) (hf : ∀ v, Measurable (f v))
    (hfd : ∀ v, ∀ x y : ∀ u, α u, (∀ u ∈ A v, x u = y u) → f v x = f v y) :
    ∫⁻ x, ∏ v ∈ S, f v x ∂(Measure.pi ν) = ∏ v ∈ S, ∫⁻ x, f v x ∂(Measure.pi ν) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hA' : (S : Set κ).PairwiseDisjoint A := hA.subset (by simp)
    simp only [Finset.prod_insert ha]
    rw [lint_mul_of_disjoint ν x0 (A a) (S.biUnion A) ?_ (f a) (fun x => ∏ v ∈ S, f v x)
      (hf a) (Finset.measurable_prod _ (fun v _ => hf v)) (hfd a) ?_, ih hA']
    · rw [Finset.disjoint_biUnion_right]
      intro v hv
      exact hA (by simp) (by simp [hv]) (fun h => ha (h ▸ hv))
    · intro x y hxy
      apply Finset.prod_congr rfl
      intro v hv
      exact hfd v x y (fun u hu => hxy u (Finset.mem_biUnion.2 ⟨v, hv, hu⟩))

end RobustShattering.Dev.L48

namespace RobustShattering.Supermartingale

theorem chk_lemma_4_8 {V : Type} [Fintype V] (G : SimpleGraph V) {T : ℕ}
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (c : ℕ) (X Y : ℝ≥0) (hY : 0 < Y) (B : Randomness Ω → Set V)
    (γ : V → ℕ → Randomness Ω → ℝ≥0) (hγ : IsShatteringCost G c X Y μ B γ)
    (S : Finset V) (hS : LocalLLL.Main.separated G (2 * c) (S : Set V))
    (i : ℕ) (hi : i < T) (ω : Randomness Ω) :
    ∫⁻ η, ∏ v ∈ S, (γ v (i + 1) (Function.update ω ⟨i, hi⟩ η) : ℝ≥0∞)
        ∂(Measure.pi (fun u : V => μ u ⟨i, hi⟩)) ≤ ∏ v ∈ S, (γ v i ω : ℝ≥0∞) := by
  classical
  have hk : (⟨i, hi⟩ : Fin T) = ⟨i, hi⟩ := rfl
  let A : V → Finset V := fun v => Finset.univ.filter (fun u => u ∈ LocalLLL.Main.ball G v c)
  have hAdisj : (S : Set V).PairwiseDisjoint A := by
    intro v hv w hw hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu1 hu2
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
    have h1 : G.edist v u ≤ c := hu1
    have h2 : G.edist w u ≤ c := hu2
    have h3 : G.edist v w ≤ ((2 * c : ℕ) : ℕ∞) := by
      calc G.edist v w ≤ G.edist v u + G.edist u w := SimpleGraph.edist_triangle
        _ = G.edist v u + G.edist w u := by rw [SimpleGraph.edist_comm (u := u) (v := w)]
        _ ≤ (c : ℕ∞) + c := add_le_add h1 h2
        _ = ((2 * c : ℕ) : ℕ∞) := by push_cast; ring
    exact hS v hv w hw hvw ⟨hvw, h3⟩
  have hmeas : ∀ v, Measurable (fun η : (∀ u, Ω u ⟨i, hi⟩) =>
      (γ v (i + 1) (Function.update ω ⟨i, hi⟩ η) : ℝ≥0∞)) := by
    intro v
    exact measurable_coe_nnreal_ennreal.comp
      ((hγ.measurable v (i + 1) hi).comp (measurable_update'.comp (measurable_const.prodMk measurable_id)))
  have hdep : ∀ v, ∀ x y : (∀ u, Ω u ⟨i, hi⟩), (∀ u ∈ A v, x u = y u) →
      (γ v (i + 1) (Function.update ω ⟨i, hi⟩ x) : ℝ≥0∞) =
        γ v (i + 1) (Function.update ω ⟨i, hi⟩ y) := by
    intro v x y hxy
    congr 1
    apply hγ.local_dep v (i + 1) hi
    intro k u hku
    by_cases hkk : k = ⟨i, hi⟩
    · subst hkk
      have hu : u ∈ LocalLLL.Main.ball G v c := by
        rcases hku with h | ⟨_, h⟩
        · simp at h
        · exact h
      have := hxy u (by simpa [A] using hu)
      simp [this]
    · rw [Function.update_of_ne hkk, Function.update_of_ne hkk]
  have h1 := RobustShattering.Dev.L48.lint_prod_disjoint
    (fun u : V => μ u ⟨i, hi⟩) (fun u => ω ⟨i, hi⟩ u) S A hAdisj _ hmeas hdep
  rw [h1]
  apply Finset.prod_le_prod' 
  intro v _
  exact hγ.local_supermartingale v i hi ω

end RobustShattering.Supermartingale
end

theorem solution : type_of% @RobustShattering.Supermartingale.chk_lemma_4_8 := @RobustShattering.Supermartingale.chk_lemma_4_8
