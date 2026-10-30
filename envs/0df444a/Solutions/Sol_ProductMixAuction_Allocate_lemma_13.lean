-- Prove2me | solution 1 for ProductMixAuction.Allocate.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:51:36.220668+00:00
-- url     : https://prove2.me/submissions/64cdd16e-2376-4eff-b4bf-2590275ab5fb

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm
import Theorems.Thm_ProductMixAuction_Allocate_lemma_9

open ProductMixAuction.Allocate

namespace PMAL13

variable {n : ℕ}

lemma le_sM (b : Bid n) (q : Fin n → ℝ) (m : Fin (n + 1)) :
    b.v m - ext q m ≤ surplusMax b q :=
  Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ m)

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

lemma ext_line (p q : Fin n → ℝ) (θ : ℝ) (m : Fin (n + 1)) :
    ext (p + θ • (q - p)) m = (1 - θ) * ext p m + θ * ext q m := by
  cases m using Fin.cases <;> simp [ext] ; ring

lemma ext_close (p q : Fin n → ℝ) (r : ℝ) (hq : q ∈ Metric.ball p r) (m : Fin (n + 1)) :
    |ext q m - ext p m| < r := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hq
  cases m using Fin.cases with
  | zero => simpa [ext] using hr
  | succ i =>
    have := lt_of_le_of_lt (dist_le_pi_dist q p i) hq
    simpa [ext, Real.dist_eq] using this

lemma obs7 (b : Bid n) (p q : Fin n → ℝ) (ε : ℝ)
    (hgap : ∀ k ∉ demGoods b p, b.v k - ext p k ≤ surplusMax b p - ε)
    (hq : q ∈ Metric.ball p (ε / 2)) : demGoods b q ⊆ demGoods b p := by
  intro i hi
  by_contra hip
  obtain ⟨g, hg⟩ := dG_ne b p
  have h1 := hgap i hip
  have h2 := (mem_dG b q i).mp hi
  have h3 := le_sM b q g
  have h4 := (mem_dG b p g).mp hg
  have c1 := abs_lt.mp (ext_close p q _ hq i)
  have c2 := abs_lt.mp (ext_close p q _ hq g)
  linarith [c1.1, c1.2, c2.1, c2.2]

/-- Contracting towards `p` keeps the demanded goods of a bid. -/
lemma dG_contract (b : Bid n) (p z : Fin n → ℝ) (hsub : demGoods b z ⊆ demGoods b p)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    demGoods b (p + t • (z - p)) = demGoods b z := by
  obtain ⟨g, hg⟩ := dG_ne b z
  have hgp := hsub hg
  have hsM : surplusMax b (p + t • (z - p)) = (1 - t) * surplusMax b p + t * surplusMax b z := by
    apply sM_eq_of _ _ _ g
    · intro m; rw [ext_line]
      have := le_sM b p m; have := le_sM b z m
      nlinarith
    · rw [ext_line, ← (mem_dG b p g).mp hgp, ← (mem_dG b z g).mp hg]; ring
  ext m
  rw [mem_dG, mem_dG, hsM, ext_line]
  constructor
  · intro h
    have h1 := le_sM b p m
    have h2 := le_sM b z m
    by_contra hne
    have h3 : b.v m - ext z m < surplusMax b z := lt_of_le_of_ne h2 hne
    nlinarith
  · intro h
    have hmp := (mem_dG b p m).mp (hsub ((mem_dG b z m).mpr h))
    rw [← hmp, ← h]; ring

lemma gap_one (b : Bid n) (p : Fin n → ℝ) (hb : ∀ k, ∃ z : ℤ, b.v k = z)
    (hp : ∀ i, ∃ z : ℤ, p i = z) : ∀ k ∉ demGoods b p, b.v k - ext p k ≤ surplusMax b p - 1 := by
  have hint : ∀ k, ∃ z : ℤ, b.v k - ext p k = z := by
    intro k
    obtain ⟨zb, hzb⟩ := hb k
    cases k using Fin.cases with
    | zero => exact ⟨zb, by simp [ext, hzb]⟩
    | succ i =>
      obtain ⟨zp, hzp⟩ := hp i
      exact ⟨zb - zp, by simp [ext, hzb, hzp]⟩
  intro k hk
  obtain ⟨g, hg⟩ := dG_ne b p
  have hg' := (mem_dG b p g).mp hg
  have hlt : b.v k - ext p k < surplusMax b p :=
    lt_of_le_of_ne (le_sM b p k) (fun h => hk ((mem_dG b p k).mpr h))
  obtain ⟨zk, hzk⟩ := hint k
  obtain ⟨zg, hzg⟩ := hint g
  rw [← hg', hzg, hzk]
  rw [← hg', hzg, hzk] at hlt
  have h1 : zk < zg := by exact_mod_cast hlt
  have h2 : zk ≤ zg - 1 := by omega
  have h3 : (zk : ℝ) ≤ ((zg - 1 : ℤ) : ℝ) := by exact_mod_cast h2
  simpa using h3

/-- shifting a bid by `ε e^{i+1}` is translating prices by `ε e^i` -/
lemma ext_shift (x : Fin n → ℝ) (i : Fin n) (ε : ℝ) (m : Fin (n + 1)) :
    ext (x - ε • Pi.single i (1 : ℝ)) m = ext x m - (Pi.single i.succ ε : Fin (n + 1) → ℝ) m := by
  cases m using Fin.cases with
  | zero => simp [ext, Fin.succ_ne_zero]
  | succ k =>
    simp only [ext, Fin.cons_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk, Pi.single_apply, Fin.succ_inj]

lemma shift_val (b : Bid n) (x : Fin n → ℝ) (i : Fin n) (ε : ℝ) (m : Fin (n + 1)) :
    (shiftBid i.succ ε b).v m - ext x m = b.v m - ext (x - ε • Pi.single i (1 : ℝ)) m := by
  rw [ext_shift]; simp [shiftBid]; ring

lemma shift_sM (b : Bid n) (x : Fin n → ℝ) (i : Fin n) (ε : ℝ) :
    surplusMax (shiftBid i.succ ε b) x = surplusMax b (x - ε • Pi.single i (1 : ℝ)) := by
  unfold surplusMax
  congr 1; funext m; exact shift_val b x i ε m

lemma shift_dG (b : Bid n) (x : Fin n → ℝ) (i : Fin n) (ε : ℝ) :
    demGoods (shiftBid i.succ ε b) x = demGoods b (x - ε • Pi.single i (1 : ℝ)) := by
  ext m; rw [mem_dG, mem_dG, shift_sM, shift_val]

/-- A list whose bids, at every price `x`, look like those of `L` at `x - d`. -/
structure Transl (L L' : List (Bid n)) (d : Fin n → ℝ) : Prop where
  fB_eq : ∀ x, fB L' x = fB L (x - d)
  nm_iff : ∀ x, NonMarginalAt L' x ↔ NonMarginalAt L (x - d)
  nmB_eq : ∀ x, nmBundle L' x = nmBundle L (x - d)

lemma transl_shift (L : List (Bid n)) (i : Fin n) (ε : ℝ) :
    Transl L (L.map (shiftBid i.succ ε)) (ε • Pi.single i (1 : ℝ)) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · simp only [fB, List.map_map, Function.comp_def, shift_sM]
    rfl
  · simp only [NonMarginalAt, List.forall_mem_map, shift_dG]
  · simp only [nmBundle, List.map_map, Function.comp_def, shift_dG]
    rfl

lemma transl_id (L : List (Bid n)) : Transl L L 0 :=
  ⟨fun x => by simp, fun x => by simp, fun x => by simp⟩

lemma main (L L' : List (Bid n)) (p : Fin n → ℝ) (d : Fin n → ℝ) (ε : ℝ) (hε : |ε| < 1 / 4)
    (hd : ‖d‖ ≤ |ε|) (hT : Transl L L' d) (hV : EpsValid L p (1 / 2))
    (hgap : ∀ b ∈ L, ∀ k ∉ demGoods b p, b.v k - ext p k ≤ surplusMax b p - 1)
    (q : Fin n → ℝ) (hq : q ∈ Metric.closedBall p |ε|) :
    LocallyValid L' q ∧ demand L' q ⊆ demand L p := by
  have hqp : ‖q - p‖ ≤ |ε| := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hq
  have key : ∀ x, ‖x - q‖ < 1 / 2 - 2 * |ε| → x - d ∈ Metric.ball p (1 / 2) := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    have : x - d - p = (x - q) + (q - p) - d := by abel
    rw [this]
    calc ‖(x - q) + (q - p) - d‖ ≤ ‖x - q‖ + ‖q - p‖ + ‖d‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ < 1 / 2 := by linarith
  have hr : 0 < 1 / 2 - 2 * |ε| := by linarith
  refine ⟨⟨1 / 2 - 2 * |ε|, hr, ?_⟩, ?_⟩
  · -- local validity at q
    have h1 := hV.translate_right (-d)
    have h2 : Metric.ball q (1 / 2 - 2 * |ε|) ⊆ (fun z => -d + z) ⁻¹' Metric.ball p (1 / 2) := by
      intro x hx
      have := key x (by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hx)
      simpa [neg_add_eq_sub] using this
    refine (h1.subset h2 (convex_ball _ _)).congr ?_
    intro x _
    simp [hT.fB_eq x, neg_add_eq_sub]
  · -- demand inclusion
    unfold demand
    intro y hy
    refine (convexHull_mono (Set.image_mono ?_)) hy
    intro x hx δ hδ
    obtain ⟨w, hw, hnm, hx'⟩ := hx (1 / 2 - 2 * |ε|) hr
    set z := w - d with hz
    have hzb : z ∈ Metric.ball p (1 / 2) := key w (by rw [← dist_eq_norm]; exact hw)
    have hnmz : NonMarginalAt L z := (hT.nm_iff w).mp hnm
    have hxz : nmBundle L z = x := by rw [← hT.nmB_eq w]; exact hx'
    have hsub : ∀ b ∈ L, demGoods b z ⊆ demGoods b p := fun b hb =>
      obs7 b p z 1 (hgap b hb) (by simpa using hzb)
    set D := dist z p
    set t : ℝ := min 1 (δ / (2 * (D + 1))) with htdef
    have hD : 0 ≤ D := dist_nonneg
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have hcontr : ∀ b ∈ L, demGoods b (p + t • (z - p)) = demGoods b z := fun b hb =>
      dG_contract b p z (hsub b hb) t ht0 ht1
    refine ⟨p + t • (z - p), ?_, ?_, ?_⟩
    · rw [dist_eq_norm]
      have : p + t • (z - p) - p = t • (z - p) := by abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← dist_eq_norm]
      have h1 : t ≤ δ / (2 * (D + 1)) := min_le_right _ _
      have h2 : t * D ≤ δ / (2 * (D + 1)) * D := mul_le_mul_of_nonneg_right h1 hD
      have h3 : δ / (2 * (D + 1)) * D < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    · intro b hb; rw [hcontr b hb]; exact hnmz b hb
    · rw [← hxz]
      unfold nmBundle
      congr 1
      apply List.map_congr_left
      intro b hb
      rw [hcontr b hb]

end PMAL13

open PMAL13 in
theorem solution {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (A : AllocProblem n J)
    (hA : IsAllocProblem A)
    (hbint : ∀ j, ∀ b ∈ A.B j, ∀ k, ∃ z : ℤ, b.v k = z)
    (hpint : ∀ i, ∃ z : ℤ, A.p i = z)
    (ε : ℝ) (hε : |ε| < 1 / 4) (i : Fin n) (j : J) :
    ∀ q ∈ Metric.closedBall A.p |ε|, ∀ j' : J,
      LocallyValid (shiftList A.B j i.succ ε j') q ∧
        demand (shiftList A.B j i.succ ε j') q ⊆ demand (A.B j') A.p := by
  intro q hq j'
  have hgap : ∀ b ∈ A.B j', ∀ k ∉ demGoods b A.p, b.v k - ext A.p k ≤ surplusMax b A.p - 1 :=
    fun b hb => gap_one b A.p (hbint j' b hb) hpint
  obtain ⟨δ, hδ, hval⟩ := hA.2.1 j'
  have hV : EpsValid (A.B j') A.p (1 / 2) :=
    ProductMixAuction.Allocate.lemma_9 (A.B j') A.p δ 1 hδ hval hgap
  unfold shiftList
  split_ifs with hj
  · refine main (A.B j') _ A.p (ε • Pi.single i (1 : ℝ)) ε hε ?_ (hj ▸ transl_shift _ i ε) hV hgap q hq
    rw [norm_smul, Real.norm_eq_abs]
    have : ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro k; by_cases hk : k = i <;> simp [hk, Pi.single_apply]
    nlinarith [abs_nonneg ε]
  · exact main (A.B j') _ A.p 0 ε hε (by simp) (transl_id _) hV hgap q hq
