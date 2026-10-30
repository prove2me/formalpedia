-- Prove2me | solution 1 for ProductMixAuction.Allocate.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:48:26.564234+00:00
-- url     : https://prove2.me/submissions/7a25785c-6e2e-4105-b303-88998353dd28

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm
import Theorems.Thm_ProductMixAuction_Allocate_lemma_9

open ProductMixAuction.Allocate

namespace PMAL16

variable {n : ℕ}

lemma le_sM (b : Bid n) (q : Fin n → ℝ) (m : Fin (n + 1)) :
    b.v m - ext q m ≤ surplusMax b q :=
  Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ m)

lemma dG_val (b : Bid n) (q : Fin n → ℝ) (g : Fin (n + 1)) (hg : g ∈ demGoods b q) :
    b.v g - ext q g = surplusMax b q := by
  simpa [demGoods] using hg

lemma mem_dG (b : Bid n) (q : Fin n → ℝ) (g : Fin (n + 1)) :
    g ∈ demGoods b q ↔ b.v g - ext q g = surplusMax b q := by
  simp [demGoods]

lemma dG_ne (b : Bid n) (q : Fin n → ℝ) : (demGoods b q).Nonempty := by
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (n + 1)))
    (fun i => b.v i - ext q i)
  exact ⟨m, by simp only [demGoods, Finset.mem_filter, Finset.mem_univ, true_and]; exact hm.symm⟩

lemma sM_eq_of (b : Bid n) (q : Fin n → ℝ) (c : ℝ) (g : Fin (n + 1))
    (hle : ∀ m, b.v m - ext q m ≤ c) (hg : b.v g - ext q g = c) : surplusMax b q = c :=
  le_antisymm (Finset.sup'_le _ _ fun m _ => hle m) (hg ▸ le_sM b q g)

open scoped Classical in
/-- the increment added by the projection -/
noncomputable def incr (b : Bid n) (p : Fin n → ℝ) (m : Fin (n + 1)) : ℝ :=
  if (0 : Fin (n + 1)) ∈ demGoods b p then (if m ∈ demGoods b p then 0 else -1)
  else (if m ∈ demGoods b p then 1 else 0)

open scoped Classical in
noncomputable def cst (b : Bid n) (p : Fin n → ℝ) : ℝ :=
  if (0 : Fin (n + 1)) ∈ demGoods b p then 0 else 1

lemma proj_v (b : Bid n) (p : Fin n → ℝ) (m : Fin (n + 1)) :
    (project b p).v m = b.v m + incr b p m := by
  classical
  unfold project incr
  split_ifs <;> simp_all <;> ring

lemma proj_w (b : Bid n) (p : Fin n → ℝ) : (project b p).w = b.w := by
  unfold project; split_ifs <;> rfl

/-- If the demanded goods at `q` are among those at `p`, projecting w.r.t. `p` does not change the
demanded goods at `q` and shifts the surplus by a constant. -/
lemma proj_at (b : Bid n) (p q : Fin n → ℝ) (hsub : demGoods b q ⊆ demGoods b p) :
    demGoods (project b p) q = demGoods b q ∧
      surplusMax (project b p) q = surplusMax b q + cst b p := by
  classical
  obtain ⟨g, hg⟩ := dG_ne b q
  have hgp := hsub hg
  have hgv := dG_val b q g hg
  -- values strictly below the max outside demGoods at q
  have hlt : ∀ m, m ∉ demGoods b q → b.v m - ext q m < surplusMax b q := by
    intro m hm
    rcases (le_sM b q m).lt_or_eq with h | h
    · exact h
    · exact absurd ((mem_dG b q m).mpr h) hm
  have hsM : surplusMax (project b p) q = surplusMax b q + cst b p := by
    apply sM_eq_of _ _ _ g
    · intro m
      rw [proj_v]
      have := le_sM b q m
      unfold incr cst
      by_cases hm : m ∈ demGoods b q
      · have := hsub hm
        split_ifs <;> linarith
      · have := hlt m hm
        split_ifs <;> linarith
    · rw [proj_v]
      have e : b.v g + incr b p g - ext q g = (b.v g - ext q g) + incr b p g := by ring
      rw [e, hgv]
      unfold incr cst
      split_ifs <;> simp_all
  refine ⟨?_, hsM⟩
  ext m
  rw [mem_dG, mem_dG, hsM, proj_v]
  constructor
  · intro h
    by_contra h2
    have hm : m ∉ demGoods b q := fun h' => h2 ((mem_dG b q m).mp h')
    have h1 := hlt m hm
    unfold incr cst at h
    by_cases hmp : m ∈ demGoods b p
    · -- m demanded at p but not at q
      split_ifs at h <;> linarith
    · split_ifs at h <;> linarith
  · intro h
    have hmp := hsub ((mem_dG b q m).mpr h)
    unfold incr cst
    split_ifs <;> linarith

lemma eventually_sub (B : List (Bid n)) (p : Fin n → ℝ) :
    ∀ᶠ q in nhds p, ∀ b ∈ B, demGoods b q ⊆ demGoods b p := by
  classical
  have : ∀ᶠ q in nhds p, ∀ b ∈ B.toFinset, demGoods b q ⊆ demGoods b p := by
    rw [Filter.eventually_all_finset]
    intro b _
    obtain ⟨g, hg⟩ := dG_ne b p
    have hall : ∀ᶠ q in nhds p, ∀ m : Fin (n + 1), m ∉ demGoods b p →
        b.v m - ext q m < b.v g - ext q g := by
      rw [Filter.eventually_all]
      intro m
      by_cases hm : m ∈ demGoods b p
      · exact Filter.Eventually.of_forall fun _ h => absurd hm h
      · have hlt : b.v m - ext p m < b.v g - ext p g := by
          rw [dG_val b p g hg]
          rcases (le_sM b p m).lt_or_eq with h | h
          · exact h
          · exact absurd ((mem_dG b p m).mpr h) hm
        have hc : Continuous (fun q : Fin n → ℝ => b.v m - ext q m) := by
          cases m using Fin.cases with
          | zero => simp only [ext, Fin.cons_zero]; fun_prop
          | succ i => simp only [ext, Fin.cons_succ]; fun_prop
        have hc' : Continuous (fun q : Fin n → ℝ => b.v g - ext q g) := by
          cases g using Fin.cases with
          | zero => simp only [ext, Fin.cons_zero]; fun_prop
          | succ i => simp only [ext, Fin.cons_succ]; fun_prop
        exact (hc.continuousAt.eventually_lt hc'.continuousAt hlt).mono fun q hq _ => hq
    filter_upwards [hall] with q hq
    intro m hm
    by_contra hmp
    have h1 := hq m hmp
    have h2 := le_sM b q g
    have h3 := dG_val b q m hm
    linarith
  filter_upwards [this] with q hq b hb
  exact hq b (List.mem_toFinset.mpr hb)

lemma fB_proj (B : List (Bid n)) (p q : Fin n → ℝ) (h : ∀ b ∈ B, demGoods b q ⊆ demGoods b p) :
    fB (B.map fun b => project b p) q =
      fB B q + (B.map fun b => (b.w : ℝ) * cst b p).sum := by
  induction B with
  | nil => simp [fB]
  | cons b L ih =>
    have ih' := ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
    simp only [fB, List.map_cons, List.map_map, Function.comp, List.sum_cons] at ih' ⊢
    rw [ih', (proj_at b p q (h b List.mem_cons_self)).2, proj_w]
    ring

lemma nb_eq (B : List (Bid n)) (p : Fin n → ℝ) :
    nearBundles (B.map fun b => project b p) p = nearBundles B p := by
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.mp (eventually_sub B p)
  have key : ∀ q, dist q p < ρ → (NonMarginalAt (B.map fun b => project b p) q ↔
      NonMarginalAt B q) ∧ nmBundle (B.map fun b => project b p) q = nmBundle B q := by
    intro q hq
    have hs := hρs hq
    refine ⟨?_, ?_⟩
    · simp only [NonMarginalAt, List.forall_mem_map]
      exact forall₂_congr fun b hb => by rw [(proj_at b p q (hs b hb)).1]
    · simp only [nmBundle, List.map_map, Function.comp]
      congr 1
      apply List.map_congr_left
      intro b hb
      simp only [Function.comp_apply]
      rw [(proj_at b p q (hs b hb)).1, proj_w]
  ext x
  simp only [nearBundles, Set.mem_ofPred_eq]
  constructor
  · intro h δ hδ
    obtain ⟨q, hq, hnm, hx⟩ := h (min δ ρ) (lt_min hδ hρ)
    have hq' : dist q p < ρ := lt_of_lt_of_le hq (min_le_right _ _)
    exact ⟨q, lt_of_lt_of_le hq (min_le_left _ _), (key q hq').1.mp hnm,
      (key q hq').2 ▸ hx⟩
  · intro h δ hδ
    obtain ⟨q, hq, hnm, hx⟩ := h (min δ ρ) (lt_min hδ hρ)
    have hq' : dist q p < ρ := lt_of_lt_of_le hq (min_le_right _ _)
    exact ⟨q, lt_of_lt_of_le hq (min_le_left _ _), (key q hq').1.mpr hnm,
      by rw [(key q hq').2]; exact hx⟩

end PMAL16

open PMAL16 in
theorem solution {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) :
    demand (B.map fun b => project b p) p = demand B p ∧
      (LocallyValid B p → EpsValid (B.map fun b => project b p) p (1 / 2)) := by
  refine ⟨by unfold demand; rw [nb_eq], ?_⟩
  rintro ⟨δ, hδ, hconv⟩
  obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.mp (eventually_sub B p)
  have hval : EpsValid (B.map fun b => project b p) p (min δ ρ) := by
    unfold EpsValid at hconv ⊢
    have hsub : Metric.ball p (min δ ρ) ⊆ Metric.ball p δ := Metric.ball_subset_ball (min_le_left _ _)
    have h1 := hconv.subset hsub (convex_ball _ _)
    have h2 : ConvexOn ℝ (Metric.ball p (min δ ρ))
        (fun q => fB B q + (B.map fun b => (b.w : ℝ) * cst b p).sum) :=
      h1.add (convexOn_const _ (convex_ball _ _))
    refine h2.congr ?_
    intro q hq
    have hq' : dist q p < ρ := lt_of_lt_of_le (Metric.mem_ball.mp hq) (min_le_right _ _)
    exact (fB_proj B p q (hρs hq')).symm
  have := ProductMixAuction.Allocate.lemma_9 (B.map fun b => project b p) p (min δ ρ) 1
    (lt_min hδ hρ) hval ?_
  · simpa using this
  · intro b' hb' k hk
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hb'
    have hpp := proj_at b p p (subset_refl _)
    rw [hpp.1] at hk
    rw [hpp.2, proj_v]
    have := le_sM b p k
    unfold incr cst
    split_ifs <;> linarith
