-- Prove2me | solution 1 for ProductMixAuction.Allocate.theorem_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:40:56.247025+00:00
-- url     : https://prove2.me/submissions/dcc41e2b-03b4-43b9-8487-0f55caa74a16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm
import Theorems.Thm_ProductMixAuction_Allocate_theorem_4
import Theorems.Thm_ProductMixAuction_Allocate_lemma_11_nonneg
import Theorems.Thm_ProductMixAuction_Allocate_lemma_18_nonMarginals_nonneg
import Theorems.Thm_ProductMixAuction_Allocate_lemma_12
import Theorems.Thm_ProductMixAuction_Allocate_lemma_17
import Theorems.Thm_ProductMixAuction_Allocate_lemma_18
import Theorems.Thm_ProductMixAuction_Allocate_proposition_14
import Theorems.Thm_ProductMixAuction_Allocate_proposition_14_submodular_reject

open ProductMixAuction.Allocate

set_option linter.unusedSectionVars false

namespace PMAT19v2

variable {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

def IntBids (A : AllocProblem n J) : Prop := ∀ j, ∀ b ∈ A.B j, ∀ k, ∃ z : ℤ, b.v k = z

lemma red_trans {A B C : AllocProblem n J} (h1 : IsReduction C B) (h2 : IsReduction B A) :
    IsReduction C A := ⟨h1.1, fun t ht => h2.2 t (h1.2 t ht)⟩

lemma nm_marg (A : AllocProblem n J) : ∀ j, ∀ b ∈ (nonMarginals A).B j,
    IsMarginalBid b (nonMarginals A).p := by
  intro j b hb
  simp only [nonMarginals, List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2

lemma nm_int (A : AllocProblem n J) (h : IntBids A) : IntBids (nonMarginals A) := by
  intro j b hb
  simp only [nonMarginals, List.mem_filter] at hb
  exact h j b hb.1

lemma um_int (A : AllocProblem n J) (I : Finset (Fin (n + 1))) (j : J) (h : IntBids A) :
    IntBids (unambiguousMarginals A I j) := by
  intro j' b hb
  simp only [unambiguousMarginals] at hb
  by_cases hj : j' = j
  · subst hj
    simp only [Function.update_self, List.mem_filter] at hb
    exact h _ b hb.1
  · rw [Function.update_of_ne hj] at hb
    exact h j' b hb

lemma project_int (c : Bid n) (q : Fin n → ℝ) (k : Fin (n + 1)) :
    ∃ z : ℤ, (project c q).v k = c.v k + z := by
  unfold project
  split_ifs with h0
  · by_cases hk : k ∈ demGoods c q
    · exact ⟨0, by simp [hk]⟩
    · exact ⟨-1, by simp [hk]; ring⟩
  · by_cases hk : k ∈ demGoods c q
    · exact ⟨1, by simp [hk]⟩
    · exact ⟨0, by simp [hk]⟩

lemma spu_int (sfm : SFMOracle n) (A : AllocProblem n J) (istar : Fin (n + 1)) (jstar : J)
    (h : IntBids A) : IntBids (shiftProjectUnshift sfm A istar jstar) := by
  intro j' b hb k
  simp only [shiftProjectUnshift, shiftList] at hb
  by_cases hj : j' = jstar
  · subst hj
    simp only [if_true, List.map_map, List.mem_map, Function.comp] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    obtain ⟨z, hz⟩ := h _ c hc k
    obtain ⟨z', hz'⟩ := project_int (shiftBid istar spuEps c) (pEps sfm A istar j') k
    refine ⟨z + z', ?_⟩
    simp only [shiftBid, Pi.add_apply] at hz' ⊢
    rw [hz']
    by_cases hk : k = istar
    · subst hk; simp [hz]; ring
    · simp [hk, hz]
  · simp only [hj, if_false, List.mem_map] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    obtain ⟨z, hz⟩ := h _ c hc k
    obtain ⟨z', hz'⟩ := project_int c (pEps sfm A istar jstar) k
    exact ⟨z + z', by rw [hz', hz]; push_cast; ring⟩

lemma spuEps_abs : |spuEps| = spuEps := abs_of_pos (by unfold spuEps; norm_num)

lemma spuEps_lt : |spuEps| < 1 / 4 := by rw [spuEps_abs]; unfold spuEps; norm_num

lemma genuine_shift (sfm : SFMOracle n) (A : AllocProblem n J) (hA : IsAllocProblem A)
    (hint : IntBids A) (hpint : ∀ i, ∃ z : ℤ, A.p i = z) (istar : Fin (n + 1)) (jstar : J) :
    SfmCallsGenuine A istar jstar := by
  unfold SfmCallsGenuine spuHPlus spuHMinus spuShifted
  induction istar using Fin.cases with
  | zero =>
    have := proposition_14_submodular_reject A hA hint hpint spuEps spuEps_lt jstar
    simp only [spuEps_abs] at this
    exact this
  | succ i =>
    have := proposition_14 A hA hint hpint spuEps spuEps_lt i jstar
    simp only [spuEps_abs] at this
    exact ⟨this.2.1, this.2.2.1⟩

structure Good (A : AllocProblem n J) : Prop where
  alloc : IsAllocProblem A
  int : IntBids A
  pint : ∀ i, ∃ z : ℤ, A.p i = z
  marg : ∀ j, ∀ b ∈ A.B j, IsMarginalBid b A.p

lemma step_spec (sel : Selector n J) (hsel : sel.Admissible) (sfm : SFMOracle n)
    (hsfm : SfmAdmissible sfm) (A : AllocProblem n J) (hA : Good A) (hne : ∃ j, A.B j ≠ []) :
    IsReduction (step sel sfm A) A ∧ Good (step sel sfm A) ∧
      (edges (step sel sfm A)).card < (edges A).card ∧ StepGenuine sel A ∧
      (step sel sfm A).p = A.p := by
  have hne' : ¬ ∀ j, A.B j = [] := by
    rintro h; obtain ⟨j, hj⟩ := hne; exact hj (h j)
  have hadm := hsel A hA.marg hne
  unfold step StepGenuine
  rw [if_neg hne']
  cases hc : sel A with
  | cluster I j =>
    rw [hc] at hadm
    obtain ⟨hI, hlink⟩ := hadm
    obtain ⟨h12a, h12b⟩ := lemma_12 A hA.alloc hA.marg I j hI hlink
    have hnn : ∀ j' k, 0 ≤ (nonMarginals (unambiguousMarginals A I j)).m j' k := by
      classical
      intro j' k
      have hnil : ((unambiguousMarginals A I j).B j').filter
          (fun b => ¬ IsMarginalBid b (unambiguousMarginals A I j).p) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        have hb' : b ∈ A.B j' := by
          simp only [unambiguousMarginals] at hb
          by_cases hj : j' = j
          · subst hj
            simp only [Function.update_self, List.mem_filter] at hb
            exact hb.1
          · rwa [Function.update_of_ne hj] at hb
        simpa [unambiguousMarginals] using hA.marg j' b hb'
      simp only [nonMarginals]
      rw [hnil]
      simpa [nmBundle] using h12a.1.2.2.1 j' k
    obtain ⟨h11a, h11b⟩ := lemma_11_nonneg _ h12a.1 hnn
    refine ⟨red_trans h11a h12a, ⟨h11a.1, nm_int _ (um_int A I j hA.int), hA.pint,
      nm_marg _⟩, ?_, fun _ => trivial, rfl⟩
    rw [h11b]; exact h12b
  | shift istar jstar =>
    rw [hc] at hadm
    have h18 := lemma_18 A hA.alloc hA.int hA.pint istar jstar hadm sfm hsfm
    have h17 := lemma_17 A hA.alloc hA.int hA.pint istar jstar hadm sfm hsfm
    have hnn := lemma_18_nonMarginals_nonneg A hA.alloc hA.marg hA.int hA.pint istar jstar hadm
      sfm hsfm
    obtain ⟨h11a, h11b⟩ := lemma_11_nonneg _ h18.1 hnn
    refine ⟨red_trans h11a h18, ⟨h11a.1, nm_int _ (spu_int sfm A istar jstar hA.int), hA.pint,
      nm_marg _⟩, ?_, fun _ => genuine_shift sfm A hA.alloc hA.int hA.pint istar jstar, rfl⟩
    rw [h11b]; exact h17

lemma edges_nonempty (A : AllocProblem n J) (j : J) (b : Bid n) (hb : b ∈ A.B j)
    (hm : IsMarginalBid b A.p) : (edges A).Nonempty := by
  obtain ⟨i, hi, i', hi', hii⟩ := Finset.one_lt_card.mp hm
  refine ⟨(s(i, i'), j), ?_⟩
  unfold edges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨by simpa using hii, b, hb, ?_⟩
  intro x hx
  rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption

lemma edges_bound (A : AllocProblem n J) :
    (edges A).card ≤ Fintype.card J * (n + 1).choose 2 := by
  classical
  have hsub : edges A ⊆ (Finset.univ.filter (fun z : Sym2 (Fin (n + 1)) => ¬ z.IsDiag)) ×ˢ
      (Finset.univ : Finset J) := by
    intro e he
    unfold edges at he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    simp [he.1]
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Finset.card_univ, mul_comm]
  apply le_of_eq
  congr 1
  rw [← Fintype.card_subtype, Sym2.card_subtype_not_diag, Fintype.card_fin]

section run
variable (sel : Selector n J) (hsel : sel.Admissible) (sfm : SFMOracle n)
  (hsfm : SfmAdmissible sfm) (A0 : AllocProblem n J) (hA0 : IsAllocProblem A0)
  (hint0 : IntBids A0) (hp0 : ∀ i, ∃ z : ℤ, A0.p i = z)
  (hm0 : ∀ j k, 0 ≤ (nonMarginals A0).m j k)
include hsel hsfm hA0 hint0 hp0 hm0

lemma run_good : ∀ k, Good (run sel sfm A0 k) ∧ IsReduction (run sel sfm A0 k) A0 ∧
    (run sel sfm A0 k).p = A0.p := by
  intro k
  induction k with
  | zero =>
    obtain ⟨h1, -⟩ := lemma_11_nonneg A0 hA0 hm0
    exact ⟨⟨h1.1, nm_int _ hint0, hp0, nm_marg _⟩, h1, rfl⟩
  | succ k ih =>
    obtain ⟨hg, hr, hp⟩ := ih
    show Good (step sel sfm _) ∧ IsReduction (step sel sfm _) A0 ∧ (step sel sfm _).p = A0.p
    by_cases hall : ∀ j, (run sel sfm A0 k).B j = []
    · have : step sel sfm (run sel sfm A0 k) = run sel sfm A0 k := by
        unfold step; rw [if_pos hall]
      rw [this]; exact ⟨hg, hr, hp⟩
    · push_neg at hall
      obtain ⟨h1, h2, -, -, h5⟩ := step_spec sel hsel sfm hsfm _ hg hall
      exact ⟨h2, red_trans h1 hr, h5.trans hp⟩

lemma run_edges (k : ℕ) (hne : ∃ j, (run sel sfm A0 k).B j ≠ []) :
    (edges (run sel sfm A0 (k + 1))).card < (edges (run sel sfm A0 k)).card :=
  (step_spec sel hsel sfm hsfm _ (run_good sel hsel sfm hsfm A0 hA0 hint0 hp0 hm0 k).1 hne).2.2.1

lemma run_genuine (k : ℕ) : StepGenuine sel (run sel sfm A0 k) := by
  intro hne
  exact (step_spec sel hsel sfm hsfm _ (run_good sel hsel sfm hsfm A0 hA0 hint0 hp0 hm0 k).1
    hne).2.2.2.1 hne

lemma run_terminates : ∃ k ≤ (edges (run sel sfm A0 0)).card,
    ∀ j, (run sel sfm A0 k).B j = [] := by
  by_contra H
  push_neg at H
  set E0 := (edges (run sel sfm A0 0)).card
  have key : ∀ k ≤ E0, (edges (run sel sfm A0 k)).card + k ≤ E0 := by
    intro k
    induction k with
    | zero => intro _; simp [E0]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := run_edges sel hsel sfm hsfm A0 hA0 hint0 hp0 hm0 k (H k (by omega))
      omega
  have h0 := key E0 le_rfl
  obtain ⟨j, hj⟩ := H E0 le_rfl
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ hj
  have hm := (run_good sel hsel sfm hsfm A0 hA0 hint0 hp0 hm0 E0).1.marg j b hb
  have := (edges_nonempty _ j b hb hm).card_pos
  omega

end run

def castZ {m : ℕ} (y : Fin m → ℤ) : Fin m → ℝ := fun k => (y k : ℝ)

lemma demand_sub (B : List (Bid n)) (p : Fin n → ℝ) (S : Set (Fin (n + 1) → ℝ))
    (hS : Convex ℝ S) (h : ∀ y ∈ nearBundles B p, castZ y ∈ S) :
    ∀ x ∈ demand B p, castZ x ∈ S := by
  intro x hx
  unfold demand at hx
  refine convexHull_min ?_ hS hx
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

lemma demand_nil (p : Fin n → ℝ) (x : Fin (n + 1) → ℤ) (hx : x ∈ demand ([] : List (Bid n)) p) :
    x = 0 := by
  have := demand_sub [] p {0} (convex_singleton _) (by
    intro y hy
    obtain ⟨q, -, -, hq⟩ := hy 1 one_pos
    simp only [nmBundle, List.map_nil, List.sum_nil] at hq
    subst hq; funext k; simp [castZ]) x hx
  funext k
  have h := congrFun (Set.mem_singleton_iff.mp this) k
  simpa [castZ] using h

lemma list_sum_coord {α : Type*} (L : List α) (f : α → Fin (n + 1) → ℤ) :
    ∑ k, (L.map f).sum k = (L.map fun a => ∑ k, f a k).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

lemma nm_total (B : List (Bid n)) (q : Fin n → ℝ) (h : NonMarginalAt B q) :
    ∑ k, nmBundle B q k = (B.map Bid.w).sum := by
  unfold nmBundle
  rw [list_sum_coord]
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_apply]
  rw [Finset.sum_comm]
  simp [Pi.single_apply, h b hb]

lemma demand_total (B : List (Bid n)) (p : Fin n → ℝ) (x : Fin (n + 1) → ℤ)
    (hx : x ∈ demand B p) : ∑ k, x k = (B.map Bid.w).sum := by
  have hS : Convex ℝ {z : Fin (n + 1) → ℝ | ∑ k, z k = (((B.map Bid.w).sum : ℤ) : ℝ)} := by
    apply convex_hyperplane
    exact ⟨fun a b => by simp [Finset.sum_add_distrib],
      fun c a => by simp [Finset.mul_sum]⟩
  have := demand_sub B p _ hS (by
    intro y hy
    obtain ⟨q, -, hq, rfl⟩ := hy 1 one_pos
    simp only [Set.mem_ofPred_eq, castZ]
    exact_mod_cast nm_total B q hq) x hx
  simp only [Set.mem_ofPred_eq, castZ] at this
  exact_mod_cast this

lemma ext_add_smul (q d : Fin n → ℝ) (s : ℝ) (m : Fin (n + 1)) :
    ext (q + s • d) m = ext q m + s * ext d m := by
  cases m using Fin.cases <;> simp [ext]

lemma surplusMax_eq_of (b : Bid n) (q : Fin n → ℝ) (g : Fin (n + 1))
    (h : ∀ m, b.v m - ext q m ≤ b.v g - ext q g) : surplusMax b q = b.v g - ext q g :=
  le_antisymm (Finset.sup'_le _ _ fun m _ => h m)
    (Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ g))

lemma le_surplusMax (b : Bid n) (q : Fin n → ℝ) (m : Fin (n + 1)) :
    b.v m - ext q m ≤ surplusMax b q :=
  Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ m)

lemma near0 (b : Bid n) (q d : Fin n → ℝ) (hb : (demGoods b q).card = 1) :
    ∀ᶠ s in nhds (0 : ℝ), surplusMax b (q + s • d) =
      surplusMax b q - s * ∑ i ∈ demGoods b q, ext d i := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hb
  have hgm : g ∈ demGoods b q := by rw [hg]; exact Finset.mem_singleton_self g
  have hgv : b.v g - ext q g = surplusMax b q := by
    simpa [demGoods] using hgm
  have hall : ∀ᶠ s in nhds (0 : ℝ), ∀ m, b.v m - (ext q m + s * ext d m) ≤
      b.v g - (ext q g + s * ext d g) := by
    rw [Filter.eventually_all]
    intro m
    by_cases hm : m = g
    · subst hm; exact Filter.Eventually.of_forall fun _ => le_rfl
    · have hlt : b.v m - ext q m < b.v g - ext q g := by
        rcases (le_surplusMax b q m).lt_or_eq with h | h
        · rwa [hgv]
        · exfalso
          have : m ∈ demGoods b q := by simp [demGoods, h]
          rw [hg] at this; exact hm (Finset.mem_singleton.mp this)
      have hc : ContinuousAt (fun s : ℝ => b.v m - (ext q m + s * ext d m)) 0 := by fun_prop
      have hc' : ContinuousAt (fun s : ℝ => b.v g - (ext q g + s * ext d g)) 0 := by fun_prop
      exact (hc.eventually_lt hc' (by simpa using hlt)).mono fun _ h => h.le
  filter_upwards [hall] with s hs
  rw [surplusMax_eq_of b _ g (fun m => by simpa only [ext_add_smul] using hs m), hg,
    Finset.sum_singleton, ext_add_smul, ← hgv]
  ring

lemma lsum1 (B : List (Bid n)) (x y : Bid n → ℝ) (s : ℝ) :
    (B.map fun b => (b.w : ℝ) * (x b - s * y b)).sum =
      (B.map fun b => (b.w : ℝ) * x b).sum - s * (B.map fun b => (b.w : ℝ) * y b).sum := by
  induction B with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma lsum2 (B : List (Bid n)) (M : Bid n → ℝ) (c s : ℝ) :
    (B.map fun b => (b.w : ℝ) * (c * s + M b)).sum =
      c * s * (B.map fun b => (b.w : ℝ)).sum + (B.map fun b => (b.w : ℝ) * M b).sum := by
  induction B with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma nm_nonneg_aux (B : List (Bid n)) (hV : Valid B) (q : Fin n → ℝ)
    (d : Fin n → ℝ) (τ : Bid n → ℝ)
    (hτ : ∀ b ∈ B, ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      surplusMax b (q + s • d) = surplusMax b q - s * τ b)
    (c : ℝ) (M : Bid n → ℝ)
    (hM : ∀ b, ∀ᶠ s in Filter.atTop, surplusMax b (q + s • d) = c * s + M b) :
    -(B.map fun b => (b.w : ℝ) * τ b).sum ≤ c * (B.map fun b => (b.w : ℝ)).sum := by
  classical
  set a := (B.map fun b => (b.w : ℝ) * τ b).sum
  set W := (B.map fun b => (b.w : ℝ)).sum
  set φ : ℝ → ℝ := fun s => fB B (q + s • d)
  have hφ : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩
    have h := hV.2 (Set.mem_univ (q + x • d)) (Set.mem_univ (q + y • d)) hα hβ hαβ
    have e : α • (q + x • d) + β • (q + y • d) = q + (α • x + β • y) • d := by
      funext m; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (q m) * hαβ
    simp only [φ, smul_eq_mul] at h ⊢
    rw [e] at h; simpa using h
  have hnear : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), φ s = fB B q - s * a := by
    have : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ b ∈ B.toFinset, surplusMax b (q + s • d) =
        surplusMax b q - s * τ b := by
      rw [Filter.eventually_all_finset]
      intro b hb
      exact hτ b (List.mem_toFinset.mp hb)
    filter_upwards [this] with s hs
    simp only [φ, fB]
    rw [List.map_congr_left (fun b hb => by rw [hs b (List.mem_toFinset.mpr hb)]), lsum1]
  obtain ⟨s0, hφ0, hs0⟩ := (hnear.and self_mem_nhdsWithin).exists
  have hs0 : 0 < s0 := hs0
  have hφz : φ 0 = fB B q := by simp [φ]
  have hfar : ∀ᶠ s in Filter.atTop, φ s = c * s * W + (B.map fun b => (b.w : ℝ) * M b).sum := by
    have : ∀ᶠ s in Filter.atTop, ∀ b ∈ B.toFinset, surplusMax b (q + s • d) = c * s + M b := by
      rw [Filter.eventually_all_finset]
      intro b _; exact hM b
    filter_upwards [this] with s hs
    simp only [φ, fB]
    rw [List.map_congr_left (fun b hb => by rw [hs b (List.mem_toFinset.mpr hb)]), lsum2]
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hfar
  set S1 := max T (s0 + 1)
  set S2 := S1 + 1
  have h1 := hT S1 (le_max_left _ _)
  have h2 := hT S2 (by have := le_max_left T (s0 + 1); simp only [S2, S1]; linarith)
  have hs01 : s0 < S1 := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have m1 := hφ.slope_mono_adjacent (Set.mem_univ 0) (Set.mem_univ S1) hs0 hs01
  have m2 := hφ.slope_mono_adjacent (Set.mem_univ s0) (Set.mem_univ S2) hs01 (by simp [S2])
  rw [hφ0, hφz] at m1
  rw [hφ0, h1, h2] at m2
  rw [h1] at m1
  have e1 : (fB B q - s0 * a - fB B q) / (s0 - 0) = -a := by
    rw [sub_zero, div_eq_iff hs0.ne']; ring
  have e2 : (c * S2 * W + (B.map fun b => (b.w : ℝ) * M b).sum -
      (c * S1 * W + (B.map fun b => (b.w : ℝ) * M b).sum)) / (S2 - S1) = c * W := by
    simp only [S2]; field_simp; ring
  rw [e1] at m1; rw [e2] at m2
  linarith

lemma dG_nonempty (b : Bid n) (q : Fin n → ℝ) : (demGoods b q).Nonempty := by
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (n + 1)))
    (fun i => b.v i - ext q i)
  exact ⟨m, by simp only [demGoods, Finset.mem_filter, Finset.mem_univ, true_and]; exact hm.symm⟩

lemma dG_other (b : Bid n) (q : Fin n → ℝ) (k : Fin (n + 1)) (h : demGoods b q ≠ {k}) :
    ∃ g ∈ demGoods b q, g ≠ k := by
  by_contra H
  push Not at H
  apply h
  obtain ⟨g, hg⟩ := dG_nonempty b q
  rw [Finset.eq_singleton_iff_unique_mem]
  exact ⟨H g hg ▸ hg, H⟩

lemma dG_val (b : Bid n) (q : Fin n → ℝ) (g : Fin (n + 1)) (hg : g ∈ demGoods b q) :
    b.v g - ext q g = surplusMax b q := by
  simpa [demGoods] using hg

lemma nearS_succ (b : Bid n) (q : Fin n → ℝ) (i : Fin n) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      surplusMax b (q + s • Pi.single i (1 : ℝ)) =
        surplusMax b q - s * (if demGoods b q = {i.succ} then 1 else 0) := by
  have hed : ∀ m, ext (Pi.single i (1 : ℝ)) m = if m = i.succ then 1 else 0 := by
    intro m; cases m using Fin.cases <;> simp [ext, Pi.single_apply, (Fin.succ_ne_zero _).symm]
  by_cases h : demGoods b q = {i.succ}
  · have hc : (demGoods b q).card = 1 := by rw [h]; rfl
    refine (Filter.Eventually.filter_mono nhdsWithin_le_nhds (near0 b q (Pi.single i (1 : ℝ)) hc)).mono fun s hs => ?_
    rw [hs, h, if_pos rfl, Finset.sum_singleton, hed, if_pos rfl]
  · rw [if_neg h]
    obtain ⟨g, hg, hgk⟩ := dG_other b q _ h
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : (0 : ℝ) < s := hs
    have hgv := dG_val b q g hg
    rw [surplusMax_eq_of b _ g, ext_add_smul, hed, if_neg hgk]
    · rw [← hgv]; ring
    · intro m
      rw [ext_add_smul, ext_add_smul, hed, hed, if_neg hgk]
      have := le_surplusMax b q m
      split_ifs <;> nlinarith

lemma nearS_zero (b : Bid n) (q : Fin n → ℝ) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      surplusMax b (q + s • (fun _ => (-1 : ℝ))) =
        surplusMax b q - s * (if demGoods b q = {0} then 0 else -1) := by
  have hed : ∀ m : Fin (n + 1), ext (n := n) (fun _ => (-1 : ℝ)) m = if m = 0 then 0 else -1 := by
    intro m; cases m using Fin.cases <;> simp [ext, Fin.succ_ne_zero]
  by_cases h : demGoods b q = {0}
  · have hc : (demGoods b q).card = 1 := by rw [h]; rfl
    refine (Filter.Eventually.filter_mono nhdsWithin_le_nhds (near0 b q (fun _ => (-1 : ℝ)) hc)).mono fun s hs => ?_
    rw [hs, h, if_pos rfl, Finset.sum_singleton, hed, if_pos rfl]
  · rw [if_neg h]
    obtain ⟨g, hg, hgk⟩ := dG_other b q _ h
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs : (0 : ℝ) < s := hs
    have hgv := dG_val b q g hg
    rw [surplusMax_eq_of b _ g, ext_add_smul, hed, if_neg hgk]
    · rw [← hgv]; ring
    · intro m
      rw [ext_add_smul, ext_add_smul, hed, hed, if_neg hgk]
      have := le_surplusMax b q m
      split_ifs <;> nlinarith

lemma farSucc (b : Bid n) (q : Fin n → ℝ) (i : Fin n) :
    ∃ M : ℝ, ∀ᶠ s in Filter.atTop, surplusMax b (q + s • Pi.single i (1 : ℝ)) = 0 * s + M := by
  have h0 : (0 : Fin (n + 1)) ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.succ :=
    Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero i).symm, Finset.mem_univ _⟩
  set M := ((Finset.univ : Finset (Fin (n + 1))).erase i.succ).sup' ⟨0, h0⟩
    (fun m => b.v m - ext q m) with hMdef
  refine ⟨M, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop
    (b.v i.succ - ext q i.succ - (b.v 0 - ext q 0))] with s hs
  have hed : ∀ m, ext (Pi.single i (1 : ℝ)) m = if m = i.succ then 1 else 0 := by
    intro m; cases m using Fin.cases <;> simp [ext, Pi.single_apply, (Fin.succ_ne_zero _).symm]
  have hle : ∀ m ∈ (Finset.univ : Finset (Fin (n + 1))).erase i.succ, b.v m - ext q m ≤ M :=
    fun m hm => Finset.le_sup' (fun m => b.v m - ext q m) hm
  rw [zero_mul, zero_add]
  apply le_antisymm
  · apply Finset.sup'_le
    intro m _
    rw [ext_add_smul, hed]
    by_cases hm : m = i.succ
    · subst hm; simp only [if_true]; have := hle 0 h0; linarith
    · simp only [hm, if_false, mul_zero, add_zero]
      exact hle m (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩)
  · apply Finset.sup'_le
    intro m hm
    have := le_surplusMax b (q + s • Pi.single i (1 : ℝ)) m
    rw [ext_add_smul, hed, if_neg (Finset.mem_erase.mp hm).1] at this
    simpa using this

lemma farZero (hn : 0 < n) (b : Bid n) (q : Fin n → ℝ) :
    ∃ M : ℝ, ∀ᶠ s in Filter.atTop, surplusMax b (q + s • (fun _ => (-1 : ℝ))) = 1 * s + M := by
  set g1 : Fin (n + 1) := (⟨0, hn⟩ : Fin n).succ
  have h1 : g1 ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0 :=
    Finset.mem_erase.mpr ⟨Fin.succ_ne_zero _, Finset.mem_univ _⟩
  set M := ((Finset.univ : Finset (Fin (n + 1))).erase 0).sup' ⟨g1, h1⟩
    (fun m => b.v m - ext q m) with hMdef
  refine ⟨M, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop
    (b.v 0 - ext q 0 - (b.v g1 - ext q g1))] with s hs
  have hed : ∀ m : Fin (n + 1), ext (n := n) (fun _ => (-1 : ℝ)) m = if m = 0 then 0 else -1 := by
    intro m; cases m using Fin.cases <;> simp [ext, Fin.succ_ne_zero]
  have hle : ∀ m ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, b.v m - ext q m ≤ M :=
    fun m hm => Finset.le_sup' (fun m => b.v m - ext q m) hm
  apply le_antisymm
  · apply Finset.sup'_le
    intro m _
    rw [ext_add_smul, hed]
    by_cases hm : m = 0
    · subst hm; simp only [if_true, mul_zero, add_zero]; have := hle g1 h1; linarith
    · simp only [hm, if_false]
      have := hle m (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩); linarith
  · have : M ≤ surplusMax b (q + s • (fun _ => (-1 : ℝ))) - s := by
      apply Finset.sup'_le
      intro m hm
      have := le_surplusMax b (q + s • (fun _ => (-1 : ℝ))) m
      rw [ext_add_smul, hed, if_neg (Finset.mem_erase.mp hm).1] at this
      linarith
    linarith

lemma list_apply_cast (B : List (Bid n)) (f : Bid n → Fin (n + 1) → ℤ) (k : Fin (n + 1)) :
    (((B.map f).sum k : ℤ) : ℝ) = (B.map fun b => ((f b k : ℤ) : ℝ)).sum := by
  induction B with
  | nil => simp
  | cons a L ih => simp [List.map_cons, List.sum_cons, ih]

open scoped Classical in
lemma nm_filter_cast (B : List (Bid n)) (q : Fin n → ℝ) (k : Fin (n + 1)) :
    ((nmBundle (B.filter fun b => ¬ IsMarginalBid b q) q k : ℤ) : ℝ) =
      (B.map fun b => (b.w : ℝ) * (if demGoods b q = {k} then 1 else 0)).sum := by
  classical
  induction B with
  | nil => simp [nmBundle]
  | cons b L ih =>
    rw [List.filter_cons]
    by_cases hb : IsMarginalBid b q
    · have hne : demGoods b q ≠ {k} := by
        intro h; unfold IsMarginalBid at hb; rw [h] at hb; simp at hb
      simp only [hb, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      rw [ih]; simp [hne]
    · simp only [hb, not_false_eq_true, decide_true, if_true]
      have hc : (demGoods b q).card = 1 := by
        unfold IsMarginalBid at hb
        have := (dG_nonempty b q).card_pos
        omega
      obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hc
      have : ((nmBundle (b :: L.filter fun b => ¬ IsMarginalBid b q) q k : ℤ) : ℝ) =
          (b.w : ℝ) * (if g = k then 1 else 0) +
            ((nmBundle (L.filter fun b => ¬ IsMarginalBid b q) q k : ℤ) : ℝ) := by
        simp only [nmBundle, List.map_cons, List.sum_cons, Pi.add_apply, hg]
        simp [Pi.single_apply, eq_comm]
      rw [this, ih]
      simp only [List.map_cons, List.sum_cons, hg, Finset.singleton_inj]

open scoped Classical in
lemma nm_part_nonneg (hn : 0 < n) (B : List (Bid n)) (hV : Valid B) (q : Fin n → ℝ)
    (k : Fin (n + 1)) : 0 ≤ nmBundle (B.filter fun b => ¬ IsMarginalBid b q) q k := by
  suffices h : (0 : ℝ) ≤ ((nmBundle (B.filter fun b => ¬ IsMarginalBid b q) q k : ℤ) : ℝ) by
    exact_mod_cast h
  rw [nm_filter_cast]
  cases k using Fin.cases with
  | succ i =>
    have hh := fun b => farSucc b q i
    choose M hM using hh
    have := nm_nonneg_aux B hV q _ _ (fun b _ => nearS_succ b q i) 0 M hM
    simp only [zero_mul] at this
    linarith
  | zero =>
    have hh := fun b => farZero hn b q
    choose M hM using hh
    have := nm_nonneg_aux B hV q _ _ (fun b _ => nearS_zero b q) 1 M hM
    have e : ∀ b ∈ B, (if demGoods b q = {0} then (0 : ℝ) else -1) =
        (if demGoods b q = {0} then 1 else 0) - 1 * 1 := by
      intro b _; split_ifs <;> ring
    rw [List.map_congr_left (fun b hb => by rw [e b hb]), lsum1] at this
    simp only [mul_one, one_mul] at this
    linarith

open scoped Classical in
lemma nm_nonneg (hn : 0 < n) (B : List (Bid n)) (hV : Valid B) (q : Fin n → ℝ)
    (hq : NonMarginalAt B q) (k : Fin (n + 1)) : 0 ≤ nmBundle B q k := by
  classical
  have hf : (B.filter fun b => ¬ IsMarginalBid b q) = B := by
    rw [List.filter_eq_self]
    intro b hb
    unfold IsMarginalBid
    simp [hq b hb]
  have := nm_part_nonneg hn B hV q k
  rwa [hf] at this

lemma demand_nonneg (hn : 0 < n) (B : List (Bid n)) (hV : Valid B) (p : Fin n → ℝ)
    (x : Fin (n + 1) → ℤ) (hx : x ∈ demand B p) (k : Fin (n + 1)) : 0 ≤ x k := by
  have hS : Convex ℝ {z : Fin (n + 1) → ℝ | (0 : ℝ) ≤ z k} := by
    apply convex_halfSpace_ge
    exact ⟨fun a b => by simp, fun c a => by simp⟩
  have := demand_sub B p _ hS (by
    intro y hy
    obtain ⟨q, -, hq, rfl⟩ := hy 1 one_pos
    simp only [Set.mem_ofPred_eq, castZ]
    exact_mod_cast nm_nonneg hn B hV q hq k) x hx
  simp only [Set.mem_ofPred_eq, castZ] at this
  exact_mod_cast this

lemma initial_int (B : J → List (IntBid n)) (p t : Fin n → ℤ) : IntBids (initial B p t) := by
  intro j b hb k
  simp only [initial, List.mem_map] at hb
  obtain ⟨c, -, rfl⟩ := hb
  cases k using Fin.cases with
  | zero => exact ⟨0, by simp [IntBid.toBid]⟩
  | succ i => exact ⟨c.v i, by simp [IntBid.toBid]⟩

lemma initial_alloc (hn : 0 < n) (B : J → List (IntBid n)) (hw : ∀ j, ∀ b ∈ B j, b.w = 1 ∨ b.w = -1)
    (hvalid : ∀ j, Valid ((B j).map IntBid.toBid)) (p t : Fin n → ℤ)
    (hclear : t ∈ demandN (aggregate fun j => (B j).map IntBid.toBid) (fun i => (p i : ℝ))) :
    IsAllocProblem (initial B p t) := by
  obtain ⟨tj, hsum, hdem⟩ := theorem_4 B hw hvalid (fun i => (p i : ℝ)) t hclear
  choose x hx hxt using hdem
  have hS0 : ∑ j, x j = (initial B p t).r := by
    funext k
    rw [Finset.sum_apply]
    cases k using Fin.cases with
    | zero =>
      have e1 : ∀ j, x j 0 = ((B j).map IntBid.w).sum - ∑ i, tj j i := by
        intro j
        have h := demand_total _ _ _ (hx j)
        rw [Fin.sum_univ_succ] at h
        rw [List.map_map] at h
        have h2 : ∀ i, x j i.succ = tj j i := fun i => by rw [← hxt j]; rfl
        simp only [h2] at h
        have h3 : (Bid.w ∘ IntBid.toBid : IntBid n → ℤ) = IntBid.w := rfl
        rw [h3] at h
        linarith
      simp only [e1, Finset.sum_sub_distrib, initial, Fin.cons_zero]
      congr 1
      rw [Finset.sum_comm]
      congr 1; funext i
      rw [← hsum, Finset.sum_apply]
    | succ i =>
      simp only [initial, Fin.cons_succ]
      rw [← hsum, Finset.sum_apply]
      congr 1; funext j
      rw [← hxt j]; rfl
  refine ⟨?_, ?_, ?_, ?_, ⟨x, x, hx, hS0, fun j => by simp [initial]⟩⟩
  · intro j b hb
    simp only [initial, List.mem_map] at hb
    obtain ⟨c, -, rfl⟩ := hb
    exact ⟨by simp [IntBid.toBid], fun i => ⟨c.v i, Or.inl (by simp [IntBid.toBid])⟩⟩
  · intro j
    exact ⟨1, one_pos, (hvalid j).subset (Set.subset_univ _) (convex_ball _ _)⟩
  · intro j k; simp [initial]
  · intro k
    rw [← hS0, Finset.sum_apply]
    exact Finset.sum_nonneg fun j _ => demand_nonneg hn _ (hvalid j) _ _ (hx j) k

lemma demand_nonempty_zero (L : List (Bid 0)) (p : Fin 0 → ℝ) : ∃ x, x ∈ demand L p := by
  have hnm : NonMarginalAt L p := by
    intro b _
    apply le_antisymm
    · exact (Finset.card_le_univ _).trans (by simp)
    · obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin 1))
        (fun i => b.v i - ext p i)
      refine Finset.card_pos.mpr ⟨m, ?_⟩
      simp only [demGoods, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hm.symm
  refine ⟨nmBundle L p, ?_⟩
  unfold demand
  apply subset_convexHull
  refine ⟨nmBundle L p, ?_, rfl⟩
  intro δ hδ
  exact ⟨p, by simpa using hδ, hnm, rfl⟩

end PMAT19v2

open PMAT19v2 in
theorem solution {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (B : J → List (IntBid n)) (hw : ∀ j, ∀ b ∈ B j, b.w = 1 ∨ b.w = -1)
    (hvalid : ∀ j, Valid ((B j).map IntBid.toBid))
    (p t : Fin n → ℤ)
    (hclear : t ∈ demandN (aggregate fun j => (B j).map IntBid.toBid) (fun i => (p i : ℝ)))
    (sel : Selector n J) (hsel : sel.Admissible)
    (sfm : SFMOracle n) (hsfm : SfmAdmissible sfm) :
    ∃ k ≤ Fintype.card J * (n + 1).choose 2,
      (∀ j, (run sel sfm (initial B p t) k).B j = []) ∧
      (∀ k' < k, StepGenuine sel (run sel sfm (initial B p t) k')) ∧
      ∑ j, Fin.tail ((run sel sfm (initial B p t) k).m j) = t ∧
      ∀ j, Fin.tail ((run sel sfm (initial B p t) k).m j) ∈
        demandN ((B j).map IntBid.toBid) (fun i => (p i : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, Nat.zero_le _, ?_, fun k' hk' => absurd hk' (Nat.not_lt_zero _),
      Subsingleton.elim _ _, ?_⟩
    · intro j
      show ((initial B p t).B j).filter _ = []
      rw [List.filter_eq_nil_iff]
      intro b _
      classical
      simp only [decide_eq_true_eq]
      unfold IsMarginalBid
      exact not_lt.mpr ((Finset.card_le_univ _).trans (by simp))
    · intro j
      obtain ⟨x, hx⟩ := demand_nonempty_zero ((B j).map IntBid.toBid) (fun i => (p i : ℝ))
      exact ⟨x, hx, Subsingleton.elim _ _⟩
  · set A0 := initial B p t with hA0def
    have hA0 := initial_alloc hn B hw hvalid p t hclear
    have hint0 := initial_int B p t
    have hp0 : ∀ i, ∃ z : ℤ, A0.p i = z := fun i => ⟨p i, rfl⟩
    have hm0 : ∀ j k, 0 ≤ (nonMarginals A0).m j k := by
      intro j k
      simp only [nonMarginals, Pi.add_apply]
      have := nm_part_nonneg hn _ (hvalid j) A0.p k
      simpa [A0, initial] using this
    obtain ⟨k, hk, hempty⟩ := run_terminates sel hsel sfm hsfm A0 hA0 hint0 hp0 hm0
    obtain ⟨hg, hred, -⟩ := run_good sel hsel sfm hsfm A0 hA0 hint0 hp0 hm0 k
    refine ⟨k, hk.trans (edges_bound _), hempty,
      fun k' _ => run_genuine sel hsel sfm hsfm A0 hA0 hint0 hp0 hm0 k', ?_⟩
    obtain ⟨-, rr, hrr, hsum, -⟩ := hg.alloc.2.2.2.2
    have hrr0 : ∀ j, rr j = 0 := fun j => demand_nil _ _ (by rw [← hempty j]; exact hrr j)
    have hsol : IsSolution (run sel sfm A0 k) (run sel sfm A0 k).m :=
      ⟨rr, hrr, hsum, fun j => by rw [hrr0 j, zero_add]⟩
    obtain ⟨rr0, hdem0, hsum0, hm⟩ := hred.2 _ hsol
    have hm' : ∀ j, (run sel sfm A0 k).m j = rr0 j := fun j => by
      rw [hm j]; simp [A0, initial]
    refine ⟨?_, fun j => ⟨rr0 j, hdem0 j, by rw [hm' j]⟩⟩
    funext i
    simp only [hm', Finset.sum_apply, Fin.tail]
    have := congrFun hsum0 i.succ
    rw [Finset.sum_apply] at this
    rw [this]
    simp [A0, initial]
