-- Prove2me | solution 1 for SPOBounds.Polyhedral.nu_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:00:40.627432+00:00
-- url     : https://prove2.me/submissions/8e485624-cbbf-470c-b9bd-093f4f313cc8

import Mathlib
import Definitions.Def_SPOBounds_Shared_Degeneracy
import Definitions.Def_SPOBounds_Polyhedral_NegNormalCone



namespace SPOBounds.Polyhedral

open SPOBounds.Shared

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : ℕ} (v : Fin K → E)

lemma spo4_hull_ge (c : StrongDual ℝ E) (a : ℝ) (h : ∀ i, a ≤ c (v i)) :
    ∀ x ∈ convexHull ℝ (Set.range v), a ≤ c x := by
  intro x hx
  have : convexHull ℝ (Set.range v) ⊆ {w | a ≤ c w} :=
    convexHull_min (Set.range_subset_iff.2 h) (convex_halfSpace_ge (c : E →ₗ[ℝ] ℝ).isLinear a)
  exact this hx

lemma spo4_minvert (hK : 0 < K) (c : StrongDual ℝ E) : ∃ j, ∀ i, c (v j) ≤ c (v i) := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  exact Finite.exists_min (fun i => c (v i))

lemma spo4_isMin (c : StrongDual ℝ E) (j : Fin K) (h : ∀ i, c (v j) ≤ c (v i)) :
    IsMinOn (fun x => c x) (convexHull ℝ (Set.range v)) (v j) :=
  isMinOn_iff.2 (spo4_hull_ge v c _ h)

lemma spo4_L (c : StrongDual ℝ E) (x p : E) (hx : x ∈ convexHull ℝ (Set.range v))
    (hmin : ∀ y ∈ convexHull ℝ (Set.range v), c x ≤ c y) (hxp : x ≠ p) :
    ∃ i, v i ≠ p ∧ ∀ k, c (v i) ≤ c (v k) := by
  by_contra hne
  push_neg at hne
  obtain ⟨ι, _, lam, z, hl0, hl1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hx
  have hzS : ∀ k, z k ∈ convexHull ℝ (Set.range v) := fun k => subset_convexHull ℝ _ (hz k)
  have hterm : ∑ k, lam k * (c (z k) - c x) = 0 := by
    have h1 : ∑ k, lam k * (c (z k) - c x) = c (∑ k, lam k • z k) - (∑ k, lam k) * c x := by
      simp [map_sum, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [h1, hsum, hl1]; ring
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ lam k * (c (z k) - c x) :=
    fun k _ => mul_nonneg (hl0 k) (by linarith [hmin _ (hzS k)])
  have hz0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm
  have hkey : ∀ k, lam k ≠ 0 → z k = p := by
    intro k hk
    obtain ⟨i, hi⟩ := hz k
    by_contra hzp
    rw [← hi] at hzp
    obtain ⟨k', hk'⟩ := hne i hzp
    have h0 := hz0 k (Finset.mem_univ _)
    have hce : c (z k) = c x := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hk
      · linarith
    have := hmin _ (subset_convexHull ℝ _ (Set.mem_range_self k'))
    rw [← hi] at hce
    linarith
  apply hxp
  rw [← hsum]
  calc ∑ k, lam k • z k = ∑ k, lam k • p := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : lam k = 0
        · simp [hk]
        · rw [hkey k hk]
    _ = p := by rw [← Finset.sum_smul, hl1, one_smul]

lemma spo4_K_pos (hne : (convexHull ℝ (Set.range v)).Nonempty) : 0 < K := by
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h
    exfalso
    obtain ⟨x, hx⟩ := hne
    have : Set.range v = ∅ := Set.range_eq_empty v
    rw [this, convexHull_empty] at hx
    exact hx
  · exact h

lemma spo4_eval (c φ : StrongDual ℝ E) (s : ℝ) (x : E) : (c - s • φ) x = c x - s * φ x := by
  simp

/-- key upper bound on `nu` -/
lemma spo4_nu_le (c : StrongDual ℝ E) (w0 y : E) (hw0 : w0 ∈ convexHull ℝ (Set.range v))
    (hmin : ∀ x ∈ convexHull ℝ (Set.range v), c w0 ≤ c x)
    (hy : y ∈ convexHull ℝ (Set.range v)) (hyw : y ≠ w0) :
    nu (convexHull ℝ (Set.range v)) c ≤ c (y - w0) / ‖y - w0‖ := by
  set S := convexHull ℝ (Set.range v) with hSdef
  have hK : 0 < K := spo4_K_pos v ⟨_, hw0⟩
  have hn : 0 < ‖y - w0‖ := norm_pos_iff.2 (sub_ne_zero.2 hyw)
  obtain ⟨φ, hφ1, hφ0⟩ := exists_dual_vector ℝ (y - w0) hn.ne'
  have hφ : φ (y - w0) = ‖y - w0‖ := by simpa using hφ0
  set t := c (y - w0) / ‖y - w0‖ with ht
  have hcy : 0 ≤ c (y - w0) := by rw [map_sub]; linarith [hmin y hy]
  have ht0 : 0 ≤ t := div_nonneg hcy hn.le
  -- existence of degenerate point on segment
  have hex : ∃ s ∈ Set.Icc 0 t, (c - s • φ) ∈ degenerate S := by
    let A : Set ℝ := {s | ∀ k, (c - s • φ) w0 ≤ (c - s • φ) (v k)}
    let B : Set ℝ := ⋃ i, {s | v i ≠ w0 ∧ ∀ k, (c - s • φ) (v i) ≤ (c - s • φ) (v k)}
    have hdeg : ∀ (s : ℝ) i, v i ≠ w0 → (∀ k, (c - s • φ) w0 ≤ (c - s • φ) (v k)) →
        (∀ k, (c - s • φ) (v i) ≤ (c - s • φ) (v k)) → (c - s • φ) ∈ degenerate S := by
      intro s i hi hA hB
      refine ⟨w0, hw0, v i, subset_convexHull ℝ _ (Set.mem_range_self i), fun h => hi h.symm,
        isMinOn_iff.2 (spo4_hull_ge v _ _ hA), spo4_isMin v _ i hB⟩
    have hAc : IsClosed A := by
      simp only [A, Set.setOf_forall, spo4_eval]
      exact isClosed_iInter fun k => isClosed_le (by fun_prop) (by fun_prop)
    have hBc : IsClosed B := by
      apply isClosed_iUnion_of_finite
      intro i
      rw [Set.setOf_and]
      refine IsClosed.inter isClosed_const ?_
      simp only [Set.setOf_forall, spo4_eval]
      exact isClosed_iInter fun k => isClosed_le (by fun_prop) (by fun_prop)
    have hcov : Set.Icc 0 t ⊆ A ∪ B := by
      intro s _
      obtain ⟨j, hj⟩ := spo4_minvert v hK (c - s • φ)
      by_cases hjw : v j = w0
      · left; intro k; rw [← hjw]; exact hj k
      · right; exact Set.mem_iUnion.2 ⟨j, hjw, hj⟩
    have h0A : (0:ℝ) ∈ A := by
      intro k; simp only [zero_smul, sub_zero]
      exact hmin _ (subset_convexHull ℝ _ (Set.mem_range_self k))
    by_cases htA : t ∈ A
    · refine ⟨t, ⟨ht0, le_rfl⟩, w0, hw0, y, hy, hyw.symm, isMinOn_iff.2 (spo4_hull_ge v _ _ htA),
        isMinOn_iff.2 ?_⟩
      intro x hx
      have h1 := spo4_hull_ge v _ _ htA x hx
      have h2 : (c - t • φ) y = (c - t • φ) w0 := by
        have : (c - t • φ) (y - w0) = 0 := by
          rw [spo4_eval, hφ, ht, div_mul_cancel₀ _ hn.ne', sub_self]
        rw [map_sub] at this; linarith
      rw [h2]; exact h1
    · have htB : t ∈ B := by
        rcases hcov ⟨ht0, le_rfl⟩ with h | h
        · exact absurd h htA
        · exact h
      obtain ⟨s, hs, hsA, hsB⟩ := isPreconnected_closed_iff.1 isPreconnected_Icc A B hAc hBc hcov
        ⟨0, ⟨le_rfl, ht0⟩, h0A⟩ ⟨t, ⟨ht0, le_rfl⟩, htB⟩
      obtain ⟨i, hi, hiB⟩ := Set.mem_iUnion.1 hsB
      exact ⟨s, hs, hdeg s i hi hsA hiB⟩
  obtain ⟨s, ⟨hs0, hst⟩, hsd⟩ := hex
  calc nu S c ≤ dist c (c - s • φ) := Metric.infDist_le_dist_of_mem hsd
    _ = s := by
        rw [dist_eq_norm, sub_sub_cancel, norm_smul, hφ1, mul_one, Real.norm_eq_abs,
          abs_of_nonneg hs0]
    _ ≤ t := hst

/-- lower bound -/
lemma spo4_deg_bound (c c' : StrongDual ℝ E) (w0 : E) (hw0 : w0 ∈ convexHull ℝ (Set.range v)) (hd : c' ∈ degenerate (convexHull ℝ (Set.range v))) :
    ∃ j, v j ≠ w0 ∧ c (v j - w0) ≤ ‖c - c'‖ * ‖v j - w0‖ ∧
      ∀ k, c' (v j) ≤ c' (v k) := by
  obtain ⟨u1, hu1, u2, hu2, hne, hm1, hm2⟩ := hd
  have hm1' := isMinOn_iff.1 hm1
  have hm2' := isMinOn_iff.1 hm2
  obtain ⟨i, hi, hik⟩ : ∃ i, v i ≠ w0 ∧ ∀ k, c' (v i) ≤ c' (v k) := by
    by_cases h1 : u1 = w0
    · exact spo4_L v c' u2 w0 hu2 hm2' (by rw [← h1]; exact fun h => hne h.symm)
    · exact spo4_L v c' u1 w0 hu1 hm1' h1
  refine ⟨i, hi, ?_, hik⟩
  have h1 : c' (v i) ≤ c' w0 := spo4_hull_ge v c' _ hik w0 hw0
  have h2 := (c - c').le_opNorm (v i - w0)
  rw [Real.norm_eq_abs] at h2
  have h3 := (le_abs_self _).trans h2
  simp only [ContinuousLinearMap.sub_apply, map_sub] at h3
  rw [map_sub]
  linarith

lemma spo4_vert_ne (w0 : E) (hSnt : (convexHull ℝ (Set.range v)).Nontrivial) : ∃ j, v j ≠ w0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, y, hy, hxy⟩ := hSnt
  have hsub : convexHull ℝ (Set.range v) ⊆ {w0} :=
    convexHull_min (Set.range_subset_iff.2 fun i => by simp [h i]) (convex_singleton w0)
  exact hxy ((hsub hx).trans (hsub hy).symm)

lemma spo4_zero_deg (hSnt : (convexHull ℝ (Set.range v)).Nontrivial) :
    (0 : StrongDual ℝ E) ∈ degenerate (convexHull ℝ (Set.range v)) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hSnt
  exact ⟨x, hx, y, hy, hxy, isMinOn_iff.2 (by simp), isMinOn_iff.2 (by simp)⟩

theorem nu_formula_core
    (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ x ∈ S, c (w c) ≤ c x)
    (chat : StrongDual ℝ E) :
    IsLeast ((fun j => chat (v j - w chat) / ‖v j - w chat‖) '' {j | v j ≠ w chat})
      (SPOBounds.Shared.nu S chat) := by
  classical
  subst hS
  obtain ⟨hw0, hmin⟩ := hw chat
  set w0 := w chat
  obtain ⟨j1, hj1⟩ := spo4_vert_ne v w0 hSnt
  have hT : (Finset.univ.filter (fun j => v j ≠ w0)).Nonempty := ⟨j1, by simp [hj1]⟩
  obtain ⟨j0, hj0, hjmin⟩ := (Finset.univ.filter (fun j => v j ≠ w0)).exists_min_image
    (fun j => chat (v j - w0) / ‖v j - w0‖) hT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj0 hjmin
  constructor
  · refine ⟨j0, hj0, le_antisymm ?_ (spo4_nu_le v chat w0 (v j0) hw0 hmin
      (subset_convexHull ℝ _ (Set.mem_range_self j0)) hj0)⟩
    show _ ≤ Metric.infDist chat _
    refine (Metric.le_infDist ⟨0, spo4_zero_deg v hSnt⟩).2 fun c' hc' => ?_
    obtain ⟨i, hi, hb, -⟩ := spo4_deg_bound v chat c' w0 hw0 hc'
    have hn : 0 < ‖v i - w0‖ := norm_pos_iff.2 (sub_ne_zero.2 hi)
    refine (hjmin i hi).trans ?_
    rw [dist_eq_norm, div_le_iff₀ hn]
    exact hb
  · rintro _ ⟨j, hj, rfl⟩
    exact spo4_nu_le v chat w0 (v j) hw0 hmin (subset_convexHull ℝ _ (Set.mem_range_self j)) hj

theorem strength_property_core
    (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ x ∈ S, c (w c) ≤ c x) :
    0 < 2 / Metric.diam S ∧ SPOBounds.Shared.StrengthProperty S (2 / Metric.diam S) w := by
  subst hS
  have hc : IsCompact (convexHull ℝ (Set.range v)) := (Set.finite_range v).isCompact_convexHull ℝ
  have hb : Bornology.IsBounded (convexHull ℝ (Set.range v)) := hc.isBounded
  obtain ⟨x, hx, y, hy, hxy⟩ := hSnt
  have hΔ : 0 < Metric.diam (convexHull ℝ (Set.range v)) :=
    lt_of_lt_of_le (dist_pos.2 hxy) (Metric.dist_le_diam_of_mem hb hx hy)
  refine ⟨div_pos two_pos hΔ, ?_⟩
  intro c u hu
  by_cases huw : u = w c
  · rw [huw]; simp
  have h1 := spo4_nu_le v c (w c) u (hw c).1 (hw c).2 hu huw
  have hn : 0 < ‖u - w c‖ := norm_pos_iff.2 (sub_ne_zero.2 huw)
  have hν0 : 0 ≤ nu (convexHull ℝ (Set.range v)) c := Metric.infDist_nonneg
  have hd : ‖u - w c‖ ≤ Metric.diam (convexHull ℝ (Set.range v)) := by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem hb hu (hw c).1
  have h2 : nu (convexHull ℝ (Set.range v)) c * ‖u - w c‖ ≤ c (u - w c) := (le_div_iff₀ hn).1 h1
  set Δ := Metric.diam (convexHull ℝ (Set.range v))
  set ν := nu (convexHull ℝ (Set.range v)) c
  set n := ‖u - w c‖
  have he : 2 / Δ * ν / 2 * n ^ 2 = ν * n * (n / Δ) := by field_simp
  rw [he]
  have hq : n / Δ ≤ 1 := (div_le_one hΔ).2 hd
  calc ν * n * (n / Δ) ≤ ν * n * 1 := mul_le_mul_of_nonneg_left hq (mul_nonneg hν0 hn.le)
    _ ≤ _ := by rw [mul_one]; exact h2

theorem unique_optimum_core
    (hK : 0 < K) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) :
    (∀ chat : StrongDual ℝ E,
      (∃! u, u ∈ S ∧ IsMinOn (fun x => chat x) S u) ↔
        ∃ j, chat ∈ interior (negNormalCone S (v j))) ∧
    SPOBounds.Shared.degenerate S = (⋃ j, interior (negNormalCone S (v j)))ᶜ := by
  subst hS
  have part1 : ∀ chat : StrongDual ℝ E,
      (∃! u, u ∈ convexHull ℝ (Set.range v) ∧ IsMinOn (fun x => chat x) (convexHull ℝ (Set.range v)) u) ↔
        ∃ j, chat ∈ interior (negNormalCone (convexHull ℝ (Set.range v)) (v j)) := by
    intro chat
    constructor
    · rintro ⟨u, ⟨hu, hum⟩, huniq⟩
      obtain ⟨j, hj⟩ := spo4_minvert v hK chat
      have hvj := spo4_isMin v chat j hj
      have hvjS : v j ∈ convexHull ℝ (Set.range v) := subset_convexHull ℝ _ (Set.mem_range_self j)
      refine ⟨j, mem_interior.2 ⟨{c' | ∀ i, i ≠ j → 0 < c' (v i - v j)}, ?_, ?_, ?_⟩⟩
      · intro c' hc' x hx
        have : ∀ i, c' (v j) ≤ c' (v i) := by
          intro i
          by_cases hij : i = j
          · rw [hij]
          · have := hc' i hij; rw [map_sub] at this; linarith
        have := spo4_hull_ge v c' _ this x hx
        rw [map_sub]; linarith
      · have : {c' : StrongDual ℝ E | ∀ i, i ≠ j → 0 < c' (v i - v j)} =
            ⋂ i ∈ ({j}ᶜ : Set (Fin K)), {c' | 0 < c' (v i - v j)} := by ext; simp
        rw [this]
        refine (Set.toFinite _).isOpen_biInter fun i _ => ?_
        exact isOpen_lt continuous_const ((ContinuousLinearMap.apply ℝ ℝ (v i - v j)).continuous)
      · intro i hij
        by_contra hle
        push_neg at hle
        rw [map_sub] at hle
        have hvi : IsMinOn (fun x => chat x) (convexHull ℝ (Set.range v)) (v i) :=
          isMinOn_iff.2 fun x hx => by
            have := isMinOn_iff.1 hvj x hx
            linarith
        have e1 := huniq (v i) ⟨subset_convexHull ℝ _ (Set.mem_range_self i), hvi⟩
        have e2 := huniq (v j) ⟨hvjS, hvj⟩
        exact hij (hv (e1.trans e2.symm))
    · rintro ⟨j, hj⟩
      have hK' := interior_subset hj
      have hvjS : v j ∈ convexHull ℝ (Set.range v) := subset_convexHull ℝ _ (Set.mem_range_self j)
      have hvjmin : ∀ x ∈ convexHull ℝ (Set.range v), chat (v j) ≤ chat x := by
        intro x hx
        have := hK' x hx
        rw [map_sub] at this; linarith
      refine ⟨v j, ⟨hvjS, isMinOn_iff.2 hvjmin⟩, ?_⟩
      rintro u ⟨hu, hum⟩
      by_contra hne
      have hum' := isMinOn_iff.1 hum
      obtain ⟨i, hi, hik⟩ := spo4_L v chat u (v j) hu hum' hne
      have heq : chat (v i) = chat (v j) := le_antisymm (hik j)
        (hvjmin _ (subset_convexHull ℝ _ (Set.mem_range_self i)))
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior chat hj
      have hn : 0 < ‖v i - v j‖ := norm_pos_iff.2 (sub_ne_zero.2 hi)
      obtain ⟨φ, hφ1, hφ0⟩ := exists_dual_vector ℝ (v i - v j) hn.ne'
      have hφ : φ (v i - v j) = ‖v i - v j‖ := by simpa using hφ0
      have hmem : chat - (ε / 2) • φ ∈ Metric.ball chat ε := by
        rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hφ1,
          mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
        exact half_lt_self hε
      have := interior_subset (hball hmem) (v i) (subset_convexHull ℝ _ (Set.mem_range_self i))
      rw [spo4_eval, hφ, map_sub, heq, sub_self] at this
      have : 0 < ε / 2 * ‖v i - v j‖ := mul_pos (half_pos hε) hn
      linarith
  refine ⟨part1, ?_⟩
  ext c
  rw [Set.mem_compl_iff, Set.mem_iUnion, ← part1]
  constructor
  · rintro ⟨u1, hu1, u2, hu2, hne, hm1, hm2⟩ ⟨u, _, huniq⟩
    exact hne ((huniq u1 ⟨hu1, hm1⟩).trans (huniq u2 ⟨hu2, hm2⟩).symm)
  · intro hnot
    obtain ⟨j, hj⟩ := spo4_minvert v hK c
    have hvj := spo4_isMin v c j hj
    have hvjS : v j ∈ convexHull ℝ (Set.range v) := subset_convexHull ℝ _ (Set.mem_range_self j)
    by_contra hnd
    apply hnot
    refine ⟨v j, ⟨hvjS, hvj⟩, fun u ⟨hu, hum⟩ => ?_⟩
    by_contra hne
    exact hnd ⟨u, hu, v j, hvjS, hne, hum, hvj⟩
end

end SPOBounds.Polyhedral

open SPOBounds.Polyhedral


theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K : ℕ} (v : Fin K → E) (hv : Function.Injective v)
    (S : Set E) (hS : S = convexHull ℝ (Set.range v)) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : ∀ c : StrongDual ℝ E, w c ∈ S ∧ ∀ x ∈ S, c (w c) ≤ c x)
    (chat : StrongDual ℝ E) :
    IsLeast ((fun j => chat (v j - w chat) / ‖v j - w chat‖) '' {j | v j ≠ w chat})
      (SPOBounds.Shared.nu S chat) := by
  exact nu_formula_core v hv S hS hSnt w hw chat
