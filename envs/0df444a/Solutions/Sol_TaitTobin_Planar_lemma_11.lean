-- Prove2me | solution 1 for TaitTobin.Planar.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T13:06:58.688983+00:00
-- url     : https://prove2.me/submissions/af801550-47ba-4651-92c9-56c63a3319aa

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_lemma_8
import Theorems.Thm_TaitTobin_Planar_lemma_9
import Theorems.Thm_TaitTobin_Planar_lemma_10
import Theorems.Thm_TaitTobin_Planar_eq_7
import Theorems.Thm_TaitTobin_Planar_LS_counts

set_option autoImplicit false

section L11

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

/-! Reduction of TaitTobin.Planar.lemma_11 to Lemmas 8, 9, 10, Eq. (7) and the counts of L and S. -/

theorem l11_row {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (h : (G.adjMatrix ℝ).mulVec v = l • v) (i : Fin n) :
    ∑ j, (if G.Adj i j then v j else 0) = l * v i := by
  have := congrFun h i
  simpa [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, ite_mul] using this

theorem l11_swap {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (hrow : ∀ i, ∑ j, (if G.Adj i j then v j else 0) = l * v i) :
    l * ∑ i, v i = ∑ i, (∑ j, if G.Adj i j then (1:ℝ) else 0) * v i := by
  have h1 : ∑ i, ∑ j, (if G.Adj i j then v j else 0) = l * ∑ i, v i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hrow i)
  rw [← h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : G.Adj j i
  · have h' : G.Adj i j := h.symm
    simp [h, h']
  · have h' : ¬ G.Adj i j := fun h'' => h h''.symm
    simp [h, h']

theorem l11_between {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
    (hd : Disjoint X Y) :
    ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then (1:ℝ) else 0) ≤
      (TaitTobin.Outerplanar.eBetween G X Y : ℝ) := by
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then (1:ℝ) else 0), Finset.sum_boole]
  have key : ((X ×ˢ Y).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤
      TaitTobin.Outerplanar.eBetween G X Y := by
    unfold TaitTobin.Outerplanar.eBetween
    refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
      simp only [Finset.coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq,
        SimpleGraph.mem_edgeSet]
      exact ⟨hp.2, p.1, hp.1.1, p.2, hp.1.2, rfl⟩
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp hq
      rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exact absurd (h1 ▸ hp.1.1) (Finset.disjoint_left.1 hd |>.mt (not_not.2 hq.1.2))
  exact_mod_cast key

theorem l11_within {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    ∑ i ∈ X, ∑ j ∈ X, (if G.Adj i j then (1:ℝ) else 0) ≤
      2 * (TaitTobin.Outerplanar.eIn G X : ℝ) := by
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then (1:ℝ) else 0), Finset.sum_boole]
  have gen : ∀ E : Finset (Sym2 (Fin n)),
      (∀ e, e ∈ E ↔ (e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ X)) →
      ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤ 2 * E.card := by
    intro E hE
    calc ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card
        ≤ (E ×ˢ (Finset.univ : Finset Bool)).card := by
          refine Finset.card_le_card_of_injOn (fun p => (s(p.1, p.2), decide (p.1 < p.2))) ?_ ?_
          · intro p hp
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
            simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hE, Finset.coe_univ,
              Set.mem_univ, and_true]
            refine ⟨hp.2, ?_⟩
            intro v hv
            rcases Sym2.mem_iff.1 hv with rfl | rfl
            · exact hp.1.1
            · exact hp.1.2
          · intro p hp q hq hpq
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp hq
            have hpq' := Prod.mk.inj hpq
            rcases Sym2.eq_iff.1 hpq'.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Prod.ext h1 h2
            · exfalso
              have hne : p.1 ≠ p.2 := hp.2.ne
              have h3 := hpq'.2
              rw [← h1, ← h2] at h3
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · simp [hlt, not_lt.2 hlt.le] at h3
              · simp [hgt, not_lt.2 hgt.le] at h3
      _ = 2 * E.card := by rw [Finset.card_product]; simp [mul_comm]
  have key : ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤
      2 * TaitTobin.Outerplanar.eIn G X := by
    unfold TaitTobin.Outerplanar.eIn
    exact gen _ (fun e => by simp)
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  exact this

theorem l11_arith (ε m s : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/80) (hm : 100 / ε^2 ≤ m)
    (hs : s ≤ 3/2 * m)
    (h : 10 * ε * (m^2 - 3 - 8 * ε * m^2) ≤ 18 * s / ε + 4 + 8 * ε * m^2) : False := by
  have hε2 : 0 < ε^2 := by positivity
  have hm' : 100 ≤ ε^2 * m := by
    rw [div_le_iff₀ hε2] at hm; linarith
  have hε2' : ε^2 ≤ 1/6400 := by nlinarith
  have hm0 : 0 ≤ m := by
    have : 0 ≤ 100 / ε^2 := by positivity
    linarith
  have hbig : 640000 ≤ m := by nlinarith
  have e1 : ε * (18 * s / ε) = 18 * s := by field_simp
  have h' := mul_le_mul_of_nonneg_left h hε0.le
  have e2 : ε * (18 * s / ε + 4 + 8 * ε * m^2) = 18 * s + 4 * ε + 8 * ε^2 * m^2 := by
    rw [mul_add, mul_add, e1]; ring
  rw [e2] at h'
  have h3 : ε^2 * m^2 ≤ 18 * s + 4 * ε + 30 * ε^2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 80 * ε) (mul_nonneg hε2.le (sq_nonneg m))]
  have h4 : 100 * m ≤ ε^2 * m^2 := by nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
theorem l11_core {n : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1/80)
    (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (x : Fin n)
    (hn3 : 3 ≤ n) (hnε : (100 / ε^2)^2 ≤ (n:ℝ))
    (hlam : Real.sqrt (2 * (n:ℝ) - 4) < specRad G)
    (hmv : (G.adjMatrix ℝ).mulVec v = specRad G • v)
    (hpos : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1) (hx : v x = 1)
    (h9b : ∑ z ∈ Sset ε v, v z ≤ (1 + 3 * ε) * Real.sqrt (2 * (n:ℝ) - 4))
    (h10 : ∀ z : Fin n, 1 / Real.sqrt (6 * (n:ℝ)) < v z)
    (h7 : ∀ u ∈ Lset ε v,
      (v u - ε) * Real.sqrt (2 * (n:ℝ) - 4) - 18 / ε ≤
        ∑ y ∈ (Sset ε v).filter (fun y => G.Adj u y), v y)
    (hc2 : TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) ≤ 2 * n - 4)
    (hc3 : TaitTobin.Outerplanar.eIn G (Sset ε v) ≤ 3 * n - 6)
    (hc4 : (TaitTobin.Outerplanar.eIn G (Lset ε v) : ℝ) ≤
      9 * Real.sqrt (2 * (n:ℝ) - 4) / ε) :
    ∃ w : Fin n, IsSecondHub G ε v x w := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (2 * (n:ℝ) - 4) := ⟨_, rfl⟩
  rw [← hs] at hlam h9b h7 hc4
  have hn3r : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s^2 = 2 * (n:ℝ) - 4 := by rw [hs]; exact Real.sq_sqrt (by linarith)
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = specRad G := ⟨_, rfl⟩
  rw [← hlamdef] at hlam hmv
  have hlam0 : 0 < lam := lt_of_le_of_lt hs0 hlam
  have hlam2 : 2 * (n:ℝ) - 4 < lam^2 := by nlinarith
  have hrow := l11_row G v lam hmv
  obtain ⟨D, hD⟩ : ∃ D : Fin n → ℝ, ∀ i, D i = ∑ j, if G.Adj i j then (1:ℝ) else 0 :=
    ⟨_, fun _ => rfl⟩
  have hD0 : ∀ i, 0 ≤ D i := fun i => by
    rw [hD]; exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  have hswap : lam * ∑ i, v i = ∑ i, D i * v i := by
    have := l11_swap G v lam hrow
    simp only [hD]; exact this
  have hxle : lam ≤ ∑ i, v i := by
    have := hrow x
    rw [hx, mul_one] at this
    rw [← this]
    exact Finset.sum_le_sum (fun j _ => by
      split_ifs
      · exact le_rfl
      · exact (hpos j).le)
  have hDv : lam^2 ≤ ∑ i, D i * v i := by
    have := mul_le_mul_of_nonneg_left hxle hlam0.le
    nlinarith [hswap]
  -- membership and partition
  have hSm : ∀ z, z ∈ Sset ε v ↔ v z ≤ ε := fun z => by simp [Sset]
  have hLm : ∀ z, z ∈ Lset ε v ↔ ε < v z := fun z => by simp [Lset]
  have hdisj : Disjoint (Sset ε v) (Lset ε v) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [hSm] at hz; rw [hLm] at hz'; linarith
  have hunion : Sset ε v ∪ Lset ε v = Finset.univ := by
    ext z
    simp only [Finset.mem_union, hSm, hLm, Finset.mem_univ, iff_true]
    exact le_or_gt _ _
  have hsplit : ∀ f : Fin n → ℝ,
      ∑ i, f i = ∑ i ∈ Sset ε v, f i + ∑ i ∈ Lset ε v, f i := by
    intro f; rw [← Finset.sum_union hdisj, hunion]
  have hDsplit : ∀ i, D i = ∑ j ∈ Sset ε v, (if G.Adj i j then (1:ℝ) else 0) +
      ∑ j ∈ Lset ε v, (if G.Adj i j then (1:ℝ) else 0) := fun i => by
    rw [hD]; exact hsplit _
  have hSS := l11_within G (Sset ε v)
  have hSL := l11_between G (Sset ε v) (Lset ε v) hdisj
  have hLL := l11_within G (Lset ε v)
  have hLS : ∑ i ∈ Lset ε v, ∑ j ∈ Sset ε v, (if G.Adj i j then (1:ℝ) else 0) ≤
      (TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) : ℝ) := by
    refine le_trans (le_of_eq ?_) hSL
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    by_cases h : G.Adj j i
    · have h' : G.Adj i j := h.symm
      simp [h, h']
    · have h' : ¬ G.Adj i j := fun h'' => h h''.symm
      simp [h, h']
  have hc2r : (TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) : ℝ) ≤ 2 * n := by
    have := hc2.trans (Nat.sub_le (2 * n) 4)
    exact_mod_cast this
  have hc3r : (TaitTobin.Outerplanar.eIn G (Sset ε v) : ℝ) ≤ 3 * n := by
    have := hc3.trans (Nat.sub_le (3 * n) 6)
    exact_mod_cast this
  -- degree sums
  have hDS : ∑ i ∈ Sset ε v, D i ≤ 8 * n := by
    calc ∑ i ∈ Sset ε v, D i
        = ∑ i ∈ Sset ε v, ∑ j ∈ Sset ε v, (if G.Adj i j then (1:ℝ) else 0) +
          ∑ i ∈ Sset ε v, ∑ j ∈ Lset ε v, (if G.Adj i j then (1:ℝ) else 0) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => hDsplit i)
      _ ≤ 8 * n := by linarith
  have hDL : ∑ i ∈ Lset ε v, D i ≤ 2 * n + 18 * s / ε := by
    have hh : 2 * (9 * s / ε) = 18 * s / ε := by ring
    calc ∑ i ∈ Lset ε v, D i
        = ∑ i ∈ Lset ε v, ∑ j ∈ Sset ε v, (if G.Adj i j then (1:ℝ) else 0) +
          ∑ i ∈ Lset ε v, ∑ j ∈ Lset ε v, (if G.Adj i j then (1:ℝ) else 0) := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => hDsplit i)
      _ ≤ 2 * n + 18 * s / ε := by linarith
  -- weighted sums
  have hSDv : ∑ i ∈ Sset ε v, D i * v i ≤ 8 * ε * n := by
    calc ∑ i ∈ Sset ε v, D i * v i ≤ ∑ i ∈ Sset ε v, D i * ε :=
          Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left ((hSm i).1 hi) (hD0 i))
      _ = (∑ i ∈ Sset ε v, D i) * ε := by rw [Finset.sum_mul]
      _ ≤ 8 * n * ε := mul_le_mul_of_nonneg_right hDS hε0.le
      _ = 8 * ε * n := by ring
  have hLDv : 2 * (n:ℝ) - 4 - 8 * ε * n ≤ ∑ i ∈ Lset ε v, D i * v i := by
    have := hsplit (fun i => D i * v i)
    linarith
  have hε1' : ε < 1 := by linarith
  have hxL : x ∈ Lset ε v := (hLm x).2 (by rw [hx]; exact hε1')
  have hDx : D x ≤ (n:ℝ) - 1 := by
    rw [hD]
    have h1 : ∀ j : Fin n, (if j = x then (0:ℝ) else 1) = 1 - (if j = x then 1 else 0) :=
      fun j => by split_ifs <;> norm_num
    calc ∑ j, (if G.Adj x j then (1:ℝ) else 0) ≤ ∑ j : Fin n, (if j = x then (0:ℝ) else 1) :=
          Finset.sum_le_sum (fun j _ => by
            by_cases h : G.Adj x j
            · have hj : j ≠ x := fun e => G.loopless.irrefl x (e ▸ h)
              simp [h, hj]
            · simp only [h, if_false]; split_ifs <;> norm_num)
      _ = (n:ℝ) - 1 := by simp [h1, Finset.sum_sub_distrib]
  have hLerase : (n:ℝ) - 3 - 8 * ε * n ≤ ∑ i ∈ (Lset ε v).erase x, D i * v i := by
    have := Finset.add_sum_erase (Lset ε v) (fun i => D i * v i) hxL
    simp only [hx, mul_one] at this
    linarith
  have hLerase2 : ∑ i ∈ (Lset ε v).erase x, D i * v i ≤ ∑ i ∈ (Lset ε v).erase x, D i :=
    Finset.sum_le_sum (fun i _ => by
      have := mul_le_mul_of_nonneg_left (hle i) (hD0 i)
      linarith)
  have hLDone : ∑ i ∈ Lset ε v, D i * (1 - v i) ≤ 18 * s / ε + 4 + 8 * ε * n := by
    have : ∑ i ∈ Lset ε v, D i * (1 - v i) =
        ∑ i ∈ Lset ε v, D i - ∑ i ∈ Lset ε v, D i * v i := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    linarith
  -- the second hub
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = Real.sqrt n := ⟨_, rfl⟩
  have hm2 : m^2 = n := by rw [hm]; exact Real.sq_sqrt (by positivity)
  have hm0 : 0 ≤ m := by rw [hm]; exact Real.sqrt_nonneg _
  have hmε : 100 / ε^2 ≤ m := by
    have := Real.sqrt_le_sqrt hnε
    rw [Real.sqrt_sq (by positivity)] at this
    rwa [← hm] at this
  have hsm : s ≤ 3/2 * m := by
    rw [hs, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hex : ∃ w ∈ Lset ε v, w ≠ x ∧ 1 - 10 * ε < v w := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    have h1 : ∑ i ∈ (Lset ε v).erase x, D i * (10 * ε) ≤
        ∑ i ∈ (Lset ε v).erase x, D i * (1 - v i) :=
      Finset.sum_le_sum (fun i hi => by
        have := hcon i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
        exact mul_le_mul_of_nonneg_left (by linarith) (hD0 i))
    have h2 : ∑ i ∈ (Lset ε v).erase x, D i * (1 - v i) ≤ ∑ i ∈ Lset ε v, D i * (1 - v i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun i _ _ => mul_nonneg (hD0 i) (by linarith [hle i]))
    rw [← Finset.sum_mul] at h1
    have h3 : 10 * ε * ((n:ℝ) - 3 - 8 * ε * n) ≤ 18 * s / ε + 4 + 8 * ε * n := by
      have := mul_le_mul_of_nonneg_left (hLerase.trans hLerase2) (by positivity : (0:ℝ) ≤ 10 * ε)
      have e : 10 * ε * ∑ i ∈ (Lset ε v).erase x, D i = (∑ i ∈ (Lset ε v).erase x, D i) * (10 * ε) :=
        mul_comm _ _
      linarith
    rw [← hm2] at h3
    exact l11_arith ε m s hε0 hε1 hmε hsm h3
  obtain ⟨w, hwL, hwx, hwv⟩ := hex
  refine ⟨w, hwL, hwx, by linarith, ?_⟩
  -- nonneighbours of w in S
  have hw7 := h7 w hwL
  have hsum : ∑ y ∈ Sset ε v, v y =
      ∑ y ∈ (Sset ε v).filter (fun y => G.Adj w y), v y +
      ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj w y), v y :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hU : (Sset ε v).filter (fun y => ¬ G.Adj w y) = (Sset ε v).filter (fun y => ¬ G.Adj y w) :=
    Finset.filter_congr (fun y _ => by rw [G.adj_comm])
  rw [hU] at hsum
  have hUv : ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj y w), v y ≤ 14 * ε * s + 18 / ε := by
    have : (1 - 11 * ε) * s ≤ (v w - ε) * s :=
      mul_le_mul_of_nonneg_right (by linarith) hs0
    nlinarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (6 * (n:ℝ)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 (by positivity)
  have hrm : r ≤ 5/2 * m := by
    rw [hr, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith
  have hcard : ((((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℕ) : ℝ) * (1 / r) ≤
      ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj y w), v y := by
    have : ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj y w), (1 / r) ≤
        ∑ y ∈ (Sset ε v).filter (fun y => ¬ G.Adj y w), v y :=
      Finset.sum_le_sum (fun y _ => by rw [hr]; exact (h10 y).le)
    simpa using this
  have hcard2 : ((((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℕ) : ℝ) ≤
      r * (14 * ε * s + 18 / ε) := by
    have h1 : ((((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℕ) : ℝ) / r ≤
        14 * ε * s + 18 / ε := by
      rw [div_eq_mul_one_div]; exact hcard.trans hUv
    rwa [div_le_iff₀ hr0, mul_comm] at h1
  have hε2 : 0 < ε^2 := by positivity
  have hm' : 100 ≤ ε^2 * m := by
    rw [div_le_iff₀ hε2] at hmε; linarith
  have hfin : r * (14 * ε * s + 18 / ε) ≤ 94 * ε * n := by
    have h1 : r * (14 * ε * s) ≤ 5/2 * m * (14 * ε * (3/2 * m)) := by
      have := mul_le_mul hrm (mul_le_mul_of_nonneg_left hsm (by positivity : (0:ℝ) ≤ 14 * ε))
        (by positivity) (by positivity)
      linarith
    have h2 : r * (18 / ε) ≤ 5/2 * m * (18 / ε) :=
      mul_le_mul_of_nonneg_right hrm (by positivity)
    have h3 : 45 * m / ε ≤ 41.5 * ε * m^2 := by
      rw [div_le_iff₀ hε0]
      nlinarith [mul_le_mul_of_nonneg_right hm' hm0]
    have h4 : 5/2 * m * (18 / ε) = 45 * m / ε := by ring
    rw [← hm2]
    nlinarith
  exact hcard2.trans hfin

end L11

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∃ w : Fin n, IsSecondHub G ε v x w := by
  refine ⟨1/80, by norm_num, fun ε hε0 hε1 => ?_⟩
  obtain ⟨N9, h9⟩ := TaitTobin.Planar.lemma_9 ε hε0
  obtain ⟨N10, h10⟩ := TaitTobin.Planar.lemma_10
  obtain ⟨N7, h7⟩ := TaitTobin.Planar.eq_7 ε hε0
  obtain ⟨NL, hL⟩ := TaitTobin.Planar.LS_counts ε hε0
  refine ⟨max (max N9 N10) (max (max N7 NL) (⌈(100 / ε^2)^2⌉₊ + 3)), fun n hn G hG v hv hpos hle x hx => ?_⟩
  have hn' := hn
  simp only [ge_iff_le, max_le_iff] at hn'
  obtain ⟨⟨hn9, hn10⟩, ⟨hn7, hnL⟩, hn3⟩ := hn'
  have hn3' : 3 ≤ n := by omega
  have hnε : (100 / ε^2)^2 ≤ (n:ℝ) := by
    have h1 : (100 / ε^2)^2 ≤ (⌈(100 / ε^2)^2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(100 / ε^2)^2⌉₊ : ℝ) ≤ n := by
      have : ⌈(100 / ε^2)^2⌉₊ ≤ n := by omega
      exact_mod_cast this
    linarith
  have hlam := (TaitTobin.Planar.lemma_8 hn3' G hG).1
  exact l11_core ε hε0 (by linarith) G v x hn3' hnε hlam hv hpos hle hx
    (h9 n hn9 G hG v hv hpos hle x hx).2 (fun z => (h10 n hn10 G hG v hv hpos hle x hx) z)
    (fun u hu => (h7 n hn7 G hG v hv hpos hle x hx u hu))
    (hL n hnL G hG v hv hpos hle x hx).2.1 (hL n hnL G hG v hv hpos hle x hx).2.2.1
    (hL n hnL G hG v hv hpos hle x hx).2.2.2
