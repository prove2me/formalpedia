-- Prove2me | solution 1 for SignRankMargin.OREquality.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:53:52.181305+00:00
-- url     : https://prove2.me/submissions/7742ee79-08e2-4e0b-bf81-8e5f9caf8c66

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_Geometry

section
namespace SignRankMargin.OREquality.Dev.L12

open MeasureTheory

/-- Packing bound: a τ/2-separated finite subset of the unit sphere has at most (1+4/τ)^r points. -/
lemma card_sep_le {r : ℕ} (τ : ℝ) (hτ : 0 < τ) (S : Finset (EuclideanSpace ℝ (Fin r)))
    (hS1 : ∀ s ∈ S, ‖s‖ = 1)
    (hsep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → τ / 2 ≤ dist s s') :
    (S.card : ℝ) ≤ (1 + 4 / τ) ^ r := by
  set μ : Measure (EuclideanSpace ℝ (Fin r)) := volume with hμ
  have hdisj : (S : Set (EuclideanSpace ℝ (Fin r))).PairwiseDisjoint
      (fun s => Metric.ball s (τ / 4)) := by
    intro s hs s' hs' hne
    rw [Function.onFun, Set.disjoint_left]
    intro z hz hz'
    have := hsep s hs s' hs' hne
    rw [Metric.mem_ball] at hz hz'
    have := dist_triangle s z s'
    rw [dist_comm s z] at this
    linarith
  have hsub : (⋃ s ∈ S, Metric.ball s (τ / 4)) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin r)) (1 + τ / 4) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨s, hs, hz⟩ := hz
    rw [Metric.mem_ball] at hz ⊢
    have h1 := hS1 s hs
    rw [dist_eq_norm] at hz
    rw [dist_zero_right]
    have h2 : ‖z‖ ≤ ‖z - s‖ + ‖s‖ := by simpa using norm_add_le (z - s) s
    linarith
  have hm : μ (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) 1) ≠ 0 :=
    (Metric.measure_ball_pos μ _ one_pos).ne'
  have hmt : μ (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hle : μ (⋃ s ∈ S, Metric.ball s (τ / 4)) ≤ μ (Metric.ball 0 (1 + τ / 4)) := measure_mono hsub
  rw [measure_biUnion_finset hdisj (fun s _ => measurableSet_ball)] at hle
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = r := by simp
  have e1 : ∀ s : EuclideanSpace ℝ (Fin r), μ (Metric.ball s (τ / 4)) =
      ENNReal.ofReal ((τ / 4) ^ r) * μ (Metric.ball 0 1) := by
    intro s
    rw [hμ, Measure.addHaar_ball_of_pos _ s (by linarith), hfr]
  have e2 : μ (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) (1 + τ / 4)) =
      ENNReal.ofReal ((1 + τ / 4) ^ r) * μ (Metric.ball 0 1) := by
    rw [hμ, Measure.addHaar_ball_of_pos _ 0 (by linarith), hfr]
  simp only [e1, Finset.sum_const, nsmul_eq_mul] at hle
  rw [e2] at hle
  rw [← mul_assoc] at hle
  have hle2 := (ENNReal.mul_le_mul_iff_left hm hmt).1 hle
  have h3 : ((S.card : ENNReal)) * ENNReal.ofReal ((τ / 4) ^ r) =
      ENNReal.ofReal ((S.card : ℝ) * (τ / 4) ^ r) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [h3] at hle2
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle2
  have h5 : (1 + 4 / τ) ^ r = (1 + τ / 4) ^ r / (τ / 4) ^ r := by
    rw [← div_pow]; congr 1; field_simp; ring
  rw [h5, le_div_iff₀ (by positivity)]
  exact h4

/-- A partition of the unit vectors into at most (1+4/τ)^r cells of diameter at most τ. -/
lemma exists_cells {X : Type*} [Fintype X] {r : ℕ} (u : X → EuclideanSpace ℝ (Fin r))
    (hu : ∀ x, ‖u x‖ = 1) (τ : ℝ) (hτ : 0 < τ) :
    ∃ (M : ℕ) (c : X → Fin M), (M : ℝ) ≤ (1 + 4 / τ) ^ r ∧
      ∀ x x', c x = c x' → ‖u x - u x'‖ ≤ τ := by
  classical
  let T : Finset (EuclideanSpace ℝ (Fin r)) := Finset.univ.image u
  let P : Finset (Finset (EuclideanSpace ℝ (Fin r))) :=
    T.powerset.filter (fun S => ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → τ / 2 ≤ dist s s')
  have hPne : P.Nonempty := ⟨∅, by simp [P]⟩
  obtain ⟨S, hSP, hmax⟩ := Finset.exists_max_image P Finset.card hPne
  simp only [P, Finset.mem_filter, Finset.mem_powerset] at hSP
  obtain ⟨hST, hsep⟩ := hSP
  have hcover : ∀ t ∈ T, ∃ s ∈ S, dist t s < τ / 2 := by
    intro t ht
    by_contra hcon
    push Not at hcon
    by_cases htS : t ∈ S
    · exact absurd (hcon t htS) (by simp; linarith)
    · have : insert t S ∈ P := by
        simp only [P, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨Finset.insert_subset ht hST, ?_⟩
        intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hcon b hb
        · rw [dist_comm]; exact hcon a ha
        · exact hsep a ha b hb hab
      have := hmax _ this
      rw [Finset.card_insert_of_notMem htS] at this
      omega
  have hS1 : ∀ s ∈ S, ‖s‖ = 1 := by
    intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (hST hs)
    exact hu x
  have hcard := card_sep_le τ hτ S hS1 hsep
  let e : S ≃ Fin S.card := S.equivFin
  have hex : ∀ x, ∃ s : S, dist (u x) s < τ / 2 := by
    intro x
    obtain ⟨s, hs, h⟩ := hcover (u x) (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    exact ⟨⟨s, hs⟩, h⟩
  choose f hf using hex
  refine ⟨S.card, fun x => e (f x), hcard, ?_⟩
  intro x x' h
  have : f x = f x' := e.injective h
  have h1 := hf x
  have h2 := hf x'
  rw [this] at h1
  rw [← dist_eq_norm]
  have := dist_triangle_right (u x) (u x') (f x' : EuclideanSpace ℝ (Fin r))
  linarith

end SignRankMargin.OREquality.Dev.L12

namespace SignRankMargin.OREquality

open SignRankMargin.OREquality.Dev.L12 in
theorem chk_lemma_12 {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (F : Matrix X Y Bool) (η : ℝ) (hηpos : 0 < η) (hηlt : η < 1)
    (hsparse : (oneCount F : ℝ) ≤ η * (Fintype.card X : ℝ) * (Fintype.card Y : ℝ))
    (r : ℕ) (u : X → EuclideanSpace ℝ (Fin r)) (v : Y → EuclideanSpace ℝ (Fin r))
    (hreal : UnitRealization F r u v) (τ : ℝ) (hτpos : 0 < τ) (hτlt : τ < 1) :
    ∃ (E : Finset X) (G : Finset Y),
      (E.card : ℝ) / (Fintype.card X : ℝ) +
        (G.card : ℝ) / (Fintype.card Y : ℝ) ≤
        2 * Real.sqrt (η * (1 + 4 / τ) ^ r) ∧
      ∀ x y, F x y = true → x ∉ E → y ∉ G →
        0 < inner ℝ (u x) (v y) ∧ inner ℝ (u x) (v y) ≤ τ := by
  classical
  obtain ⟨hu, hv, hstrict⟩ := hreal
  obtain ⟨M, c, hM, hc⟩ := exists_cells u hu τ hτpos
  set N : ℝ := (1 + 4 / τ) ^ r with hN
  have h4τ : 0 < 4 / τ := by positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by linarith)
  have hNpos : 0 < N := by linarith
  set α : ℝ := Real.sqrt (η / N) with hα
  have hαpos : 0 < α := Real.sqrt_pos.2 (by positivity)
  have hαsq : α * α = η / N := Real.mul_self_sqrt (by positivity)
  set nX : ℝ := (Fintype.card X : ℝ) with hnX
  set nY : ℝ := (Fintype.card Y : ℝ) with hnY
  have hnXp : 0 < nX := by rw [hnX]; exact_mod_cast Fintype.card_pos
  have hnYp : 0 < nY := by rw [hnY]; exact_mod_cast Fintype.card_pos
  let cellSize : X → ℕ := fun x => (Finset.univ.filter (fun x' => c x' = c x)).card
  let colOnes : Y → ℕ := fun y => (Finset.univ.filter (fun x => F x y = true)).card
  let E : Finset X := Finset.univ.filter (fun x => (cellSize x : ℝ) ≤ α * nX)
  let G : Finset Y := Finset.univ.filter (fun y => α * nX < (colOnes y : ℝ))
  refine ⟨E, G, ?_, ?_⟩
  · -- counting
    have hE : (E.card : ℝ) ≤ M * (α * nX) := by
      have h1 : E.card = ∑ j : Fin M, (E.filter (fun x => c x = j)).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (c x))
      have h2 : ∀ j : Fin M, ((E.filter (fun x => c x = j)).card : ℝ) ≤ α * nX := by
        intro j
        by_cases hne : (E.filter (fun x => c x = j)).Nonempty
        · obtain ⟨x0, hx0⟩ := hne
          simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hx0
          obtain ⟨hx0E, rfl⟩ := hx0
          refine le_trans ?_ hx0E
          exact_mod_cast Finset.card_le_card (fun x hx => by
            simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact hx.2)
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          rw [hne]; simp; positivity
      rw [h1]; push_cast
      calc (∑ j : Fin M, ((E.filter (fun x => c x = j)).card : ℝ)) ≤ ∑ _j : Fin M, α * nX :=
            Finset.sum_le_sum (fun j _ => h2 j)
        _ = M * (α * nX) := by simp
    have hG : α * nX * (G.card : ℝ) ≤ η * nX * nY := by
      have : ∀ y ∈ G, α * nX ≤ (colOnes y : ℝ) := fun y hy => by
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and] at hy; exact hy.le
      calc α * nX * (G.card : ℝ) = ∑ _y ∈ G, α * nX := by simp [mul_comm]
        _ ≤ ∑ y ∈ G, (colOnes y : ℝ) := Finset.sum_le_sum this
        _ ≤ ∑ y, (colOnes y : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
        _ = (oneCount F : ℝ) := by
            have : oneCount F = ∑ y, colOnes y := by
              unfold oneCount colOnes
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl (fun y _ => ?_)
              rw [Finset.card_filter]
            rw [this]; push_cast; rfl
        _ ≤ _ := hsparse
    have hG' : (G.card : ℝ) / nY ≤ η / α := by
      rw [div_le_div_iff₀ hnYp hαpos]
      nlinarith [hG]
    have hE' : (E.card : ℝ) / nX ≤ α * N := by
      rw [div_le_iff₀ hnXp]
      have : (M : ℝ) * (α * nX) ≤ N * (α * nX) := by
        apply mul_le_mul_of_nonneg_right hM; positivity
      nlinarith
    have hαN : α * N = Real.sqrt (η * N) := by
      have h : η * N = (α * N) ^ 2 := by
        have : (α * N) ^ 2 = (α * α) * N * N := by ring
        rw [this, hαsq]; field_simp
      rw [h, Real.sqrt_sq (by positivity)]
    have hηα : η / α = Real.sqrt (η * N) := by
      rw [← hαN, div_eq_iff hαpos.ne']
      have : α * N * α = (α * α) * N := by ring
      rw [this, hαsq]; field_simp
    linarith
  · intro x y hxy hxE hyG
    have hpos : 0 < inner ℝ (u x) (v y) := by
      have := hstrict x y
      rw [hxy] at this; simpa using this
    refine ⟨hpos, ?_⟩
    by_contra hgt
    push Not at hgt
    apply hyG
    simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hxE
    refine lt_of_lt_of_le hxE ?_
    have hsub : Finset.univ.filter (fun x' => c x' = c x) ⊆ Finset.univ.filter (fun x => F x y = true) := by
      intro x' hx'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' ⊢
      have hd := hc x' x hx'
      have h1 : inner ℝ (u x) (v y) - inner ℝ (u x') (v y) ≤ τ := by
        have : inner ℝ (u x) (v y) - inner ℝ (u x') (v y) = inner ℝ (u x - u x') (v y) := by
          rw [inner_sub_left]
        rw [this]
        calc _ ≤ ‖u x - u x'‖ * ‖v y‖ := real_inner_le_norm _ _
          _ ≤ τ * 1 := by rw [hv y]; rw [norm_sub_rev]; simpa using hd
          _ = τ := mul_one _
      by_contra hF
      have := hstrict x' y
      simp only [Bool.not_eq_true] at hF
      rw [hF] at this
      simp at this
      linarith
    exact_mod_cast Finset.card_le_card hsub

end SignRankMargin.OREquality
end

theorem solution : type_of% @SignRankMargin.OREquality.chk_lemma_12 := @SignRankMargin.OREquality.chk_lemma_12
