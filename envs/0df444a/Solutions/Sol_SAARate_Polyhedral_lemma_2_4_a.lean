-- Prove2me | solution 1 for SAARate.Polyhedral.lemma_2_4_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:19:26.738476+00:00
-- url     : https://prove2.me/submissions/466da270-a639-4661-8eb4-fac0b8332231

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting
import Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential

open MeasureTheory ProbabilityTheory ShorNonsmooth.Subdiff Filter Topology

namespace SAA3A

open SAARate.Sharp

/-- For a convex function, subgradients are characterized by local increments. -/
lemma mem_subdiff_iff_local {m : ℕ} (g : E m → ℝ) (hg : ConvexOn ℝ Set.univ g) (x v : E m) :
    v ∈ subdifferential Set.univ g x ↔
      ∀ d : E m, ∀ᶠ t in 𝓝[>] (0 : ℝ), t * inner ℝ v d ≤ g (x + t • d) - g x := by
  constructor
  · intro hv d
    refine Filter.Eventually.of_forall fun t => ?_
    have := hv (x + t • d) (Set.mem_univ _)
    rw [add_sub_cancel_left, real_inner_smul_right] at this
    linarith
  · intro H y _
    set d := y - x
    obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := ((eventually_mem_nhdsWithin.and
      (nhdsWithin_le_nhds (eventually_le_nhds one_pos))).and (H d)).exists
    have ht0' : (0 : ℝ) < t := ht0
    have hconv := hg.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith : (0 : ℝ) ≤ 1 - t)
      ht0'.le (by ring)
    have heq : (1 - t) • x + t • y = x + t • d := by
      simp only [d, smul_sub, sub_smul, one_smul]; abel
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    have : t * inner ℝ v d ≤ t * (g y - g x) := by nlinarith
    show g y - g x ≥ inner ℝ v (y - x)
    exact le_of_mul_le_mul_left this ht0'

end SAA3A

open SAA3A SAARate.Sharp SAARate.Polyhedral in
theorem solution {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : ∀ ω, P {ω} ≠ 0)
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω)) :
    ∃ (r : ℕ) (z : Fin r → SAARate.Sharp.E m), ∀ x : SAARate.Sharp.E m, ∃ k : Fin r,
      subdifferential Set.univ (SAARate.Sharp.expectedObj P h) x =
          subdifferential Set.univ (SAARate.Sharp.expectedObj P h) (z k) ∧
        ∀ (s : ℕ → Ω) (N : ℕ),
          subdifferential Set.univ (SAARate.Sharp.saaObj h s N) x =
            subdifferential Set.univ (SAARate.Sharp.saaObj h s N) (z k) := by
  classical
  choose k a b hrep0 using hpl
  have hrep : ∀ ω x, h x ω = Finset.univ.sup' Finset.univ_nonempty
      (fun i => inner ℝ (a ω i) x + b ω i) := fun ω x => hrep0 ω x
  have hle : ∀ ω i x, inner ℝ (a ω i) x + b ω i ≤ h x ω := fun ω i x => by
    rw [hrep ω x]
    exact Finset.le_sup' (fun i => inner ℝ (a ω i) x + b ω i) (Finset.mem_univ i)
  have hex : ∀ ω x, ∃ i, h x ω = inner ℝ (a ω i) x + b ω i := fun ω x => by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i => inner ℝ (a ω i) x + b ω i)
    exact ⟨i, by rw [hrep ω x, hi]⟩
  have hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω) := by
    intro ω
    refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
    simp only [smul_eq_mul]
    rw [hrep ω (α • x + β • y)]
    apply Finset.sup'_le
    intro i _
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 := mul_le_mul_of_nonneg_left (hle ω i x) hα
    have h2 := mul_le_mul_of_nonneg_left (hle ω i y) hβ
    have : b ω i = α * b ω i + β * b ω i := by rw [← add_mul, hαβ, one_mul]
    linarith
  -- the activity pattern
  let pat : E m → (∀ ω, Finset (Fin (k ω + 1))) := fun x ω =>
    Finset.univ.filter (fun i => inner ℝ (a ω i) x + b ω i = h x ω)
  -- local increments depend only on the pattern
  have hinc : ∀ x z : E m, pat x = pat z → ∀ ω (d : E m), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      h (x + t • d) ω - h x ω = h (z + t • d) ω - h z ω := by
    intro x z hxz ω d
    set I := pat x ω with hI
    have hIz : pat z ω = I := (congrFun hxz ω).symm
    obtain ⟨i0, hi0⟩ := hex ω x
    have hi0I : i0 ∈ I := by simp [I, pat, hi0]
    have hIne : I.Nonempty := ⟨i0, hi0I⟩
    -- near `x`, the maximum is attained on `I`
    have hloc : ∀ y : E m, pat y ω = I → ∀ᶠ t in 𝓝[>] (0 : ℝ),
        h (y + t • d) ω = I.sup' hIne (fun i => inner ℝ (a ω i) (y + t • d) + b ω i) := by
      intro y hy
      have hi0y : inner ℝ (a ω i0) y + b ω i0 = h y ω := by
        have : i0 ∈ pat y ω := hy ▸ hi0I
        simpa [pat] using this
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ (Finset.univ.filter (fun i => i ∉ I)),
          inner ℝ (a ω i) (y + t • d) + b ω i < inner ℝ (a ω i0) (y + t • d) + b ω i0 := by
        rw [Filter.eventually_all_finset]
        intro i hi
        have hiI : i ∉ I := (Finset.mem_filter.1 hi).2
        have hlt : inner ℝ (a ω i) y + b ω i < h y ω := by
          refine lt_of_le_of_ne (hle ω i y) fun heq => hiI ?_
          rw [← hy]; simp [pat, heq]
        have hc1 : Continuous fun t : ℝ => inner ℝ (a ω i) (y + t • d) + b ω i := by fun_prop
        have hc2 : Continuous fun t : ℝ => inner ℝ (a ω i0) (y + t • d) + b ω i0 := by fun_prop
        have : ∀ᶠ t in 𝓝 (0 : ℝ), inner ℝ (a ω i) (y + t • d) + b ω i <
            inner ℝ (a ω i0) (y + t • d) + b ω i0 := by
          apply hc1.continuousAt.eventually_lt hc2.continuousAt
          simpa [hi0y] using hlt
        exact nhdsWithin_le_nhds this
      filter_upwards [hev] with t ht
      rw [hrep ω (y + t • d)]
      apply le_antisymm
      · apply Finset.sup'_le
        intro i _
        by_cases hiI : i ∈ I
        · exact Finset.le_sup' (fun i => inner ℝ (a ω i) (y + t • d) + b ω i) hiI
        · exact (ht i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hiI⟩)).le.trans
            (Finset.le_sup' (fun i => inner ℝ (a ω i) (y + t • d) + b ω i) hi0I)
      · exact Finset.sup'_le _ _ fun i _ =>
          Finset.le_sup' (fun i => inner ℝ (a ω i) (y + t • d) + b ω i) (Finset.mem_univ i)
    filter_upwards [hloc x rfl, hloc z hIz] with t hx hz
    rw [hx, hz]
    -- on `I`, the pieces at `z + t d` are those at `x + t d` shifted by `h z - h x`
    have hshift : ∀ i ∈ I, inner ℝ (a ω i) (z + t • d) + b ω i =
        inner ℝ (a ω i) (x + t • d) + b ω i + (h z ω - h x ω) := by
      intro i hi
      have hx' : inner ℝ (a ω i) x + b ω i = h x ω := by simpa [I, pat] using hi
      have hz' : inner ℝ (a ω i) z + b ω i = h z ω := by
        have : i ∈ pat z ω := hIz ▸ hi
        simpa [pat] using this
      rw [inner_add_right, inner_add_right]
      linarith
    have e1 : I.sup' hIne (fun i => inner ℝ (a ω i) (z + t • d) + b ω i) ≤
        I.sup' hIne (fun i => inner ℝ (a ω i) (x + t • d) + b ω i) + (h z ω - h x ω) := by
      apply Finset.sup'_le
      intro i hi
      rw [hshift i hi]
      have := Finset.le_sup' (fun i => inner ℝ (a ω i) (x + t • d) + b ω i) hi
      linarith
    have e2 : I.sup' hIne (fun i => inner ℝ (a ω i) (x + t • d) + b ω i) ≤
        I.sup' hIne (fun i => inner ℝ (a ω i) (z + t • d) + b ω i) - (h z ω - h x ω) := by
      apply Finset.sup'_le
      intro i hi
      have := Finset.le_sup' (fun i => inner ℝ (a ω i) (z + t • d) + b ω i) hi
      rw [hshift i hi] at this
      linarith
    linarith
  -- generic statement for nonnegative combinations
  have hgen : ∀ {J : Type} (F : Finset J) (c : J → ℝ) (o : J → Ω), (∀ j ∈ F, 0 ≤ c j) →
      ∀ x z : E m, pat x = pat z →
      subdifferential Set.univ (fun y => ∑ j ∈ F, c j * h y (o j)) x =
        subdifferential Set.univ (fun y => ∑ j ∈ F, c j * h y (o j)) z := by
    intro J F c o hc x z hxz
    have hgconv : ConvexOn ℝ Set.univ (fun y => ∑ j ∈ F, c j * h y (o j)) := by
      refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
      simp only [smul_eq_mul, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j hj => ?_
      have := (hconv (o j)).2 (Set.mem_univ x) (Set.mem_univ y) hα hβ hαβ
      simp only [smul_eq_mul] at this
      have := mul_le_mul_of_nonneg_left this (hc j hj)
      nlinarith
    have hincg : ∀ d : E m, ∀ᶠ t in 𝓝[>] (0 : ℝ),
        (∑ j ∈ F, c j * h (x + t • d) (o j)) - ∑ j ∈ F, c j * h x (o j) =
          (∑ j ∈ F, c j * h (z + t • d) (o j)) - ∑ j ∈ F, c j * h z (o j) := by
      intro d
      have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ ω,
          h (x + t • d) ω - h x ω = h (z + t • d) ω - h z ω := by
        rw [Filter.eventually_all]; exact fun ω => hinc x z hxz ω d
      filter_upwards [hall] with t ht
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_sub, ← mul_sub, ht (o j)]
    ext v
    rw [mem_subdiff_iff_local _ hgconv, mem_subdiff_iff_local _ hgconv]
    refine forall_congr' fun d => ?_
    constructor
    · intro H
      filter_upwards [H, hincg d] with t h1 h2
      rw [← h2]; exact h1
    · intro H
      filter_upwards [H, hincg d] with t h1 h2
      rw [h2]; exact h1
  -- the two objective functions as nonnegative combinations
  have hfeq : SAARate.Sharp.expectedObj P h =
      fun y => ∑ i ∈ (Finset.univ : Finset (Fin (Fintype.card Ω))),
        P.real {(Fintype.equivFin Ω).symm i} * h y ((Fintype.equivFin Ω).symm i) := by
    funext y
    simp only [SAARate.Sharp.expectedObj]
    rw [integral_fintype Integrable.of_finite,
      ← (Fintype.equivFin Ω).symm.sum_comp (fun ω => P.real {ω} • h y ω)]
    simp [smul_eq_mul]
  have hsaa : ∀ (s : ℕ → Ω) (N : ℕ), SAARate.Sharp.saaObj h s N =
      fun y => ∑ j ∈ Finset.range N, (N : ℝ)⁻¹ * h y (s j) := by
    intro s N; funext y
    simp only [SAARate.Sharp.saaObj, Finset.mul_sum]
  -- representatives of the finitely many patterns
  let Pat := ∀ ω, Finset (Fin (k ω + 1))
  let rep : Pat → E m := fun π => if hπ : ∃ x, pat x = π then Classical.choose hπ else 0
  have hrep_pat : ∀ x, pat (rep (pat x)) = pat x := by
    intro x
    have hπ : ∃ y, pat y = pat x := ⟨x, rfl⟩
    simp only [rep, dif_pos hπ]
    exact Classical.choose_spec hπ
  let e := Fintype.equivFin Pat
  refine ⟨Fintype.card Pat, fun i => rep (e.symm i), fun x => ⟨e (pat x), ?_, ?_⟩⟩
  · simp only [Equiv.symm_apply_apply]
    rw [hfeq]
    exact hgen _ _ (Fintype.equivFin Ω).symm (fun ω _ => measureReal_nonneg) x _ (hrep_pat x).symm
  · intro s N
    simp only [Equiv.symm_apply_apply]
    rw [hsaa]
    exact hgen _ _ s (fun j _ => inv_nonneg.2 N.cast_nonneg) x _ (hrep_pat x).symm
