-- Prove2me | solution 1 for Plasticity.SeqSpace.exists_signed_permutation_inward
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T08:07:15.767595+00:00
-- url     : https://prove2.me/submissions/7770514e-10e9-42b4-864c-476714e2fe73

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Sign

open Plasticity Filter Topology Set

namespace Sol_Plasticity_SeqSpace_exists_signed_permutation_inward

variable {Γ Δ : Type*}

/-! ### Coordinates and the supremum norm -/

theorem abs_apply_le_norm (x : Linf Γ) (i : Γ) : |x i| ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (p := ⊤) ENNReal.top_ne_zero x i
  simpa [Real.norm_eq_abs] using this

theorem norm_le_of_abs_le (x : Linf Γ) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |x i| ≤ r) : ‖x‖ ≤ r :=
  lp.norm_le_of_forall_le hr (fun i => by rw [Real.norm_eq_abs]; exact h i)

theorem sub_apply' (x y : Linf Γ) (i : Γ) : (x - y) i = x i - y i := by
  rw [lp.coeFn_sub]; rfl

theorem add_apply' (x y : Linf Γ) (i : Γ) : (x + y) i = x i + y i := by
  rw [lp.coeFn_add]; rfl

theorem zero_apply' (i : Γ) : (0 : Linf Γ) i = 0 := by
  rw [lp.coeFn_zero]; rfl

theorem mem_ballIn {X : Submodule ℝ (Linf Γ)} {x : Linf Γ} :
    x ∈ ballIn X ↔ x ∈ X ∧ ‖x‖ ≤ 1 := by
  simp [ballIn, Metric.mem_closedBall, dist_zero_right]

theorem abs_le_one_of_mem {X : Submodule ℝ (Linf Γ)} {x : Linf Γ} (hx : x ∈ ballIn X) (i : Γ) :
    |x i| ≤ 1 :=
  (abs_apply_le_norm x i).trans (mem_ballIn.1 hx).2

theorem mem_of_finite {X : Submodule ℝ (Linf Γ)} (hX0 : c00 Γ ≤ X) {x : Linf Γ}
    (hfin : (Function.support ⇑x).Finite) (hb : ∀ i, |x i| ≤ 1) : x ∈ ballIn X :=
  mem_ballIn.2 ⟨hX0 hfin, norm_le_of_abs_le x zero_le_one hb⟩

theorem memℓp_of_bound (f : Γ → ℝ) (hf : ∀ i, |f i| ≤ 1) : Memℓp f ⊤ := by
  rw [memℓp_infty_iff]
  refine ⟨1, ?_⟩
  rintro _ ⟨i, rfl⟩
  show ‖f i‖ ≤ 1
  rw [Real.norm_eq_abs]; exact hf i

/-- A function bounded by one, as an element of `ℓ∞`. -/
def pt (f : Γ → ℝ) (hf : ∀ i, |f i| ≤ 1) : Linf Γ :=
  ⟨f, memℓp_of_bound f hf⟩

@[simp] theorem pt_apply (f : Γ → ℝ) (hf : ∀ i, |f i| ≤ 1) (i : Γ) : pt f hf i = f i := rfl

theorem pt_mem {X : Submodule ℝ (Linf Γ)} (hX0 : c00 Γ ≤ X) (f : Γ → ℝ) (hf : ∀ i, |f i| ≤ 1)
    (hfin : (Function.support f).Finite) : pt f hf ∈ ballIn X :=
  mem_of_finite hX0 hfin hf

theorem zero_mem {X : Submodule ℝ (Linf Γ)} (hX0 : c00 Γ ≤ X) : (0 : Linf Γ) ∈ ballIn X :=
  mem_of_finite hX0 (by rw [lp.coeFn_zero, Function.support_zero]; exact Set.finite_empty)
    (fun i => by rw [zero_apply']; simp)

/-- The point `a eₙ`. -/
def sg [DecidableEq Γ] (n : Γ) (a : ℝ) : Linf Γ := lp.single ⊤ n a

theorem single_apply' [DecidableEq Γ] (n : Γ) (a : ℝ) (i : Γ) :
    sg n a i = if i = n then a else 0 := by
  rw [sg, lp.single_apply, Pi.single_apply]

theorem sg_self [DecidableEq Γ] (n : Γ) (a : ℝ) : sg n a n = a := by
  rw [single_apply', if_pos rfl]

theorem single_mem [DecidableEq Γ] {X : Submodule ℝ (Linf Γ)} (hX0 : c00 Γ ≤ X) (n : Γ) {a : ℝ}
    (ha : |a| ≤ 1) : sg n a ∈ ballIn X := by
  refine mem_of_finite hX0 ((Set.finite_singleton n).subset ?_) ?_
  · intro i hi
    rw [Function.mem_support, single_apply'] at hi
    by_contra hne
    exact hi (if_neg hne)
  · intro i
    rw [single_apply']
    split_ifs
    · exact ha
    · simp

theorem two_apply [DecidableEq Γ] (n n' : Γ) (a b : ℝ) (i : Γ) :
    (sg n a + sg n' b) i = (if i = n then a else 0) + (if i = n' then b else 0) := by
  rw [add_apply', single_apply', single_apply']

theorem two_mem [DecidableEq Γ] {X : Submodule ℝ (Linf Γ)} (hX0 : c00 Γ ≤ X) {n n' : Γ}
    (hnn' : n ≠ n') {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    sg n a + sg n' b ∈ ballIn X := by
  refine mem_of_finite hX0 ((Set.toFinite ({n, n'} : Set Γ)).subset ?_) ?_
  · intro i hi
    rw [Function.mem_support, two_apply] at hi
    by_contra hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
    rw [if_neg hne.1, if_neg hne.2] at hi
    exact hi (by ring)
  · intro i
    rw [two_apply]
    by_cases h1 : i = n
    · subst h1; rw [if_pos rfl, if_neg hnn']; simpa using ha
    · rw [if_neg h1]
      split_ifs
      · simpa using hb
      · simp

/-! ### Elementary real inequalities -/

theorem far_both (v w : ℝ) (h : 0 < v * w) :
    ∃ ε : ℝ, |ε| ≤ 1 ∧ 1 < |ε - v| ∧ 1 < |ε - w| := by
  rcases lt_or_gt_of_ne (show v ≠ 0 by rintro rfl; simp at h) with hv | hv
  · have hw : w < 0 := by nlinarith
    refine ⟨1, by norm_num, ?_, ?_⟩
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  · have hw : 0 < w := by nlinarith
    refine ⟨-1, by norm_num, ?_, ?_⟩
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith

theorem far_one (v : ℝ) (hv : v ≠ 0) : ∃ ε : ℝ, |ε| ≤ 1 ∧ 1 < |ε - v| := by
  obtain ⟨ε, h1, h2, -⟩ := far_both v v (mul_self_pos.2 hv)
  exact ⟨ε, h1, h2⟩

theorem far_of_neg {ε v : ℝ} (hε : ε = 1 ∨ ε = -1) (h : ε * v < 0) : 1 < |ε - v| := by
  rcases hε with rfl | rfl
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

theorem nonneg_of_close {ε v : ℝ} (hε : ε = 1 ∨ ε = -1) (h : |ε - v| ≤ 1) : 0 ≤ ε * v := by
  rw [abs_le] at h
  rcases hε with rfl | rfl
  · linarith
  · linarith

theorem eq_zero_of_close {v : ℝ} (h1 : |1 - v| ≤ 1) (h2 : |-1 - v| ≤ 1) : v = 0 := by
  rw [abs_le] at h1 h2
  linarith

theorem close_of_same_sign {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (h : 0 < a * b) :
    |a - b| ≤ 1 := by
  rw [abs_le] at *
  rcases lt_or_gt_of_ne (show a ≠ 0 by rintro rfl; simp at h) with h1 | h1
  · have : b < 0 := by nlinarith
    constructor <;> linarith
  · have : 0 < b := by nlinarith
    constructor <;> linarith

theorem sign_eq (r : ℝ) (hr : r ≠ 0) : Real.sign r = 1 ∨ Real.sign r = -1 :=
  (Real.sign_apply_eq_of_ne_zero r hr).symm

theorem pm_mul {a b : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem pm_abs {a : ℝ} (ha : a = 1 ∨ a = -1) : |a| ≤ 1 := by
  rcases ha with rfl | rfl <;> norm_num

theorem pm_mul_self {a : ℝ} (ha : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases ha with rfl | rfl <;> norm_num

/-- Moving `u` by at most `ε` moves `a * u` by at most `ε` when `a = ±1`. -/
theorem pm_shift {a u v ε : ℝ} (ha : a = 1 ∨ a = -1) (h : |u - v| ≤ ε) :
    a * v - ε ≤ a * u ∧ a * u ≤ a * v + ε := by
  rw [abs_le] at h
  rcases ha with rfl | rfl
  · constructor <;> linarith
  · constructor <;> linarith

/-! ### The setting -/

/-- The hypotheses of the card, bundled. -/
structure Hyp (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ)) (F : Linf Γ → Linf Δ) :
    Prop where
  hX0 : c00 Γ ≤ X
  hX1 : X ≤ c0 Γ
  hY0 : c00 Δ ≤ Y
  bij : Set.BijOn F (ballIn X) (ballIn Y)
  lip : LipschitzOnWith 1 F (ballIn X)

namespace Hyp

variable {X : Submodule ℝ (Linf Γ)} {Y : Submodule ℝ (Linf Δ)} {F : Linf Γ → Linf Δ}

theorem coord_le (h : Hyp X Y F) {x y : Linf Γ} (hx : x ∈ ballIn X) (hy : y ∈ ballIn X)
    (j : Δ) : |F x j - F y j| ≤ ‖x - y‖ := by
  have h1 := h.lip.dist_le_mul x hx y hy
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul] at h1
  rw [← sub_apply']
  exact (abs_apply_le_norm _ j).trans h1

theorem coord_le' (h : Hyp X Y F) {x y : Linf Γ} (hx : x ∈ ballIn X) (hy : y ∈ ballIn X)
    {r : ℝ} (hr : 0 ≤ r) (hxy : ∀ i, |x i - y i| ≤ r) (j : Δ) : |F x j - F y j| ≤ r :=
  (h.coord_le hx hy j).trans (norm_le_of_abs_le _ hr (fun i => by rw [sub_apply']; exact hxy i))

/-- Transfer of coverings by unit balls, coordinatewise. -/
theorem transfer (h : Hyp X Y F) (C : Set (Linf Γ)) (hC : C ⊆ ballIn X)
    (hcov : ∀ u ∈ ballIn X, ∃ c ∈ C, ∀ i, |u i - c i| ≤ 1)
    {p : Linf Δ} (hp : p ∈ ballIn Y) : ∃ c ∈ C, ∀ j, |p j - F c j| ≤ 1 := by
  obtain ⟨u, hu, rfl⟩ := h.bij.surjOn hp
  obtain ⟨c, hc, hcu⟩ := hcov u hu
  exact ⟨c, hc, fun j => h.coord_le' hu (hC hc) zero_le_one hcu j⟩

theorem F_zero (h : Hyp X Y F) : F 0 = 0 := by
  classical
  have h0 : (0 : Linf Γ) ∈ ballIn X := zero_mem h.hX0
  have key : ∀ p ∈ ballIn Y, ∀ j, |p j - F 0 j| ≤ 1 := by
    intro p hp
    obtain ⟨c, hc, hcl⟩ := h.transfer {0} (by simpa using h0)
      (fun u hu => ⟨0, rfl, fun i => by rw [zero_apply', sub_zero]; exact abs_le_one_of_mem hu i⟩) hp
    rw [Set.mem_singleton_iff] at hc
    subst hc
    exact hcl
  apply lp.ext
  funext j
  rw [lp.coeFn_zero]
  by_contra hne
  obtain ⟨ε, hε, hfar⟩ := far_one (F 0 j) hne
  have := key (sg j ε) (single_mem h.hY0 j hε) j
  rw [sg_self] at this
  linarith

/-- An approximation of `x` by a finitely supported point of `B_X` that keeps the coordinates
in a finite set `K`. -/
theorem approx (h : Hyp X Y F) {x : Linf Γ} (hx : x ∈ ballIn X) (K : Set Γ) (hK : K.Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x' ∈ ballIn X, (Function.support ⇑x').Finite ∧ (∀ i ∈ K, x' i = x i) ∧
      ∀ j, |F x j - F x' j| ≤ ε := by
  classical
  have hc0 : Tendsto (⇑x) cofinite (𝓝 0) := h.hX1 (mem_ballIn.1 hx).1
  have hT : {i | ¬ |x i| < ε}.Finite := by
    have := (Metric.tendsto_nhds.1 hc0) ε hε
    rw [Filter.eventually_cofinite] at this
    simpa [Real.dist_eq] using this
  have hx1 := abs_le_one_of_mem hx
  let f : Γ → ℝ := fun i => if (¬ |x i| < ε ∨ i ∈ K) then x i else 0
  have hf : ∀ i, |f i| ≤ 1 := by
    intro i
    simp only [f]
    split_ifs
    · exact hx1 i
    · simp
  have hfs : (Function.support f).Finite := by
    apply (hT.union hK).subset
    intro i hi
    rw [Function.mem_support] at hi
    simp only [f] at hi
    split_ifs at hi with hc
    · exact hc
    · exact absurd rfl hi
  have hm : pt f hf ∈ ballIn X := pt_mem h.hX0 f hf hfs
  refine ⟨pt f hf, hm, hfs, fun i hi => ?_, fun j => h.coord_le' hx hm hε.le (fun i => ?_) j⟩
  · rw [pt_apply]
    simp only [f]
    rw [if_pos (Or.inr hi)]
  · rw [pt_apply]
    simp only [f]
    split_ifs with hc
    · rw [sub_self, abs_zero]; exact hε.le
    · push Not at hc
      rw [sub_zero]; exact hc.1.le

end Hyp

/-! ### Two unit balls covering the target ball -/

theorem two_centres [DecidableEq Δ] {Y : Submodule ℝ (Linf Δ)} (hY0 : c00 Δ ≤ Y) (a b : Linf Δ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hcov : ∀ p ∈ ballIn Y, (∀ j, |p j - a j| ≤ 1) ∨ (∀ j, |p j - b j| ≤ 1)) :
    ∃ m, (∀ j, j ≠ m → a j = 0 ∧ b j = 0) ∧ a m * b m < 0 := by
  have key : ∀ i k, i ≠ k → a i ≠ 0 → b k ≠ 0 → False := by
    intro i k hik hai hbk
    obtain ⟨ε, hε, hεa⟩ := far_one (a i) hai
    obtain ⟨δ, hδ, hδb⟩ := far_one (b k) hbk
    have hpi : (sg i ε + sg k δ) i = ε := by rw [two_apply, if_pos rfl, if_neg hik, add_zero]
    have hpk : (sg i ε + sg k δ) k = δ := by
      rw [two_apply, if_neg (Ne.symm hik), if_pos rfl, zero_add]
    rcases hcov _ (two_mem hY0 hik hε hδ) with h1 | h1
    · have := h1 i; rw [hpi] at this; linarith
    · have := h1 k; rw [hpk] at this; linarith
  have hex : ∀ c : Linf Δ, c ≠ 0 → ∃ i, c i ≠ 0 := by
    intro c hc
    by_contra hcon
    push Not at hcon
    exact hc (lp.ext (funext fun i => by rw [hcon i, zero_apply']))
  obtain ⟨i, hai⟩ := hex a ha
  obtain ⟨k, hbk⟩ := hex b hb
  have hik : i = k := by
    by_contra hne
    exact key i k hne hai hbk
  subst hik
  refine ⟨i, fun j hj => ⟨?_, ?_⟩, ?_⟩
  · by_contra h'; exact key j i hj h' hbk
  · by_contra h'; exact key i j (Ne.symm hj) hai h'
  · by_contra hpos
    push Not at hpos
    have hpos' : 0 < a i * b i := lt_of_le_of_ne hpos (Ne.symm (mul_ne_zero hai hbk))
    obtain ⟨ε, hε, hεa, hεb⟩ := far_both (a i) (b i) hpos'
    rcases hcov _ (single_mem hY0 i hε) with h1 | h1
    · have := h1 i; rw [sg_self] at this; linarith
    · have := h1 i; rw [sg_self] at this; linarith

namespace Hyp

variable {X : Submodule ℝ (Linf Γ)} {Y : Submodule ℝ (Linf Δ)} {F : Linf Γ → Linf Δ}

/-- The axes: `F(eₙ)` and `F(-eₙ)` are nonzero multiples of one unit vector, of opposite signs. -/
theorem axes [DecidableEq Γ] [DecidableEq Δ] (h : Hyp X Y F) (n : Γ) :
    ∃ m : Δ, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      (∀ j, j ≠ m → F (sg n 1) j = 0 ∧ F (sg n (-1)) j = 0) ∧
      0 < a * F (sg n 1) m ∧ a * F (sg n (-1)) m < 0 := by
  have hx : sg n (1:ℝ) ∈ ballIn X := single_mem h.hX0 n (by norm_num)
  have hx' : sg n (-1:ℝ) ∈ ballIn X := single_mem h.hX0 n (by norm_num)
  have hcov : ∀ p ∈ ballIn Y,
      (∀ j, |p j - F (sg n 1) j| ≤ 1) ∨ (∀ j, |p j - F (sg n (-1)) j| ≤ 1) := by
    intro p hp
    obtain ⟨c, hc, hcl⟩ := h.transfer {sg n 1, sg n (-1)} (by
        intro c hc
        rcases hc with hc | hc
        · rw [hc]; exact hx
        · rw [hc]; exact hx') (by
        intro u hu
        have hu1 := abs_le_one_of_mem hu
        by_cases hun : 0 ≤ u n
        · refine ⟨sg n 1, Or.inl rfl, fun i => ?_⟩
          rw [single_apply']
          split_ifs with hi
          · rw [hi]; have := hu1 n; rw [abs_le] at this ⊢; constructor <;> linarith
          · rw [sub_zero]; exact hu1 i
        · refine ⟨sg n (-1), Or.inr rfl, fun i => ?_⟩
          rw [single_apply']
          split_ifs with hi
          · rw [hi]; have := hu1 n; rw [abs_le] at this ⊢; constructor <;> linarith
          · rw [sub_zero]; exact hu1 i) hp
    rcases hc with hc | hc
    · rw [hc] at hcl; exact Or.inl hcl
    · rw [hc] at hcl; exact Or.inr hcl
  have hne : ∀ a : ℝ, a ≠ 0 → |a| ≤ 1 → F (sg n a) ≠ 0 := by
    intro a ha ha1 h0
    have := h.bij.injOn (single_mem h.hX0 n ha1) (zero_mem h.hX0) (h0.trans h.F_zero.symm)
    have := congrArg (fun z : Linf Γ => z n) this
    simp only [sg_self, zero_apply'] at this
    exact ha this
  obtain ⟨m, hm0, hmneg⟩ := two_centres h.hY0 _ _ (hne 1 one_ne_zero (by norm_num))
    (hne (-1) (by norm_num) (by norm_num)) hcov
  rcases lt_or_gt_of_ne (show F (sg n 1) m ≠ 0 by
      intro h0; rw [h0, zero_mul] at hmneg; exact lt_irrefl _ hmneg) with hlt | hgt
  · refine ⟨m, -1, Or.inr rfl, hm0, by linarith, ?_⟩
    nlinarith
  · exact ⟨m, 1, Or.inl rfl, hm0, by linarith, by nlinarith⟩

end Hyp

/-! ### No continuous injective map of a square into a line -/

/-- Two continuous paths from a common value whose end values lie on the same side of it
take a common value at a positive time of the first path. -/
theorem pair_meet (g k : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1)) (hk : ContinuousOn k (Icc 0 1))
    (h0 : g 0 = k 0) (hsame : 0 < (g 1 - g 0) * (k 1 - k 0)) :
    ∃ r ∈ Ioc (0:ℝ) 1, ∃ r' ∈ Icc (0:ℝ) 1, g r = k r' := by
  rcases lt_or_gt_of_ne (show g 1 - g 0 ≠ 0 by
      intro h'; rw [h', zero_mul] at hsame; exact lt_irrefl _ hsame) with hlt | hgt
  · have hk1 : k 1 < k 0 := by nlinarith
    have hw : max (g 1) (k 1) < g 0 := max_lt (by linarith) (by linarith)
    obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc' zero_le_one hg
      (show max (g 1) (k 1) ∈ Icc (g 1) (g 0) from ⟨le_max_left _ _, hw.le⟩)
    obtain ⟨r', hr', hkr⟩ := intermediate_value_Icc' zero_le_one hk
      (show max (g 1) (k 1) ∈ Icc (k 1) (k 0) from ⟨le_max_right _ _, by rw [← h0]; exact hw.le⟩)
    refine ⟨r, ⟨lt_of_le_of_ne hr.1 ?_, hr.2⟩, r', hr', hgr.trans hkr.symm⟩
    rintro rfl
    linarith
  · have hk1 : k 0 < k 1 := by nlinarith
    have hw : g 0 < min (g 1) (k 1) := lt_min (by linarith) (by linarith)
    obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc zero_le_one hg
      (show min (g 1) (k 1) ∈ Icc (g 0) (g 1) from ⟨hw.le, min_le_left _ _⟩)
    obtain ⟨r', hr', hkr⟩ := intermediate_value_Icc zero_le_one hk
      (show min (g 1) (k 1) ∈ Icc (k 0) (k 1) from ⟨by rw [← h0]; exact hw.le, min_le_right _ _⟩)
    refine ⟨r, ⟨lt_of_le_of_ne hr.1 ?_, hr.2⟩, r', hr', hgr.trans hkr.symm⟩
    rintro rfl
    linarith

theorem ray_mem {p r : ℝ} (hp : -1/4 ≤ p ∧ p ≤ 1/2) (hr : r ∈ Icc (0:ℝ) 1) :
    1/2 + p * r ∈ Icc (1/4:ℝ) 1 := by
  obtain ⟨hr0, hr1⟩ := hr
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ p + 1/4 by linarith) hr0]
  · nlinarith [mul_nonneg (show 0 ≤ 1/2 - p by linarith) hr0]

theorem ray_dist (p r r' : ℝ) : |(1/2 + p * r) - (1/2 + p * r')| = |p| * |r - r'| := by
  rw [show (1/2 + p * r) - (1/2 + p * r') = p * (r - r') by ring, abs_mul]

/-- Along two rays from the centre `(1/2, 1/2)` that meet only there, a continuous injective
function on the square `[1/4, 1]²` moves to opposite sides of its central value. -/
theorem ray_pair (G : ℝ → ℝ → ℝ)
    (hlip : ∀ a b a' b', a ∈ Icc (1/4:ℝ) 1 → b ∈ Icc (1/4:ℝ) 1 → a' ∈ Icc (1/4:ℝ) 1 →
      b' ∈ Icc (1/4:ℝ) 1 → |G a b - G a' b'| ≤ |a - a'| + |b - b'|)
    (hinj : ∀ a b a' b', a ∈ Icc (1/4:ℝ) 1 → b ∈ Icc (1/4:ℝ) 1 → a' ∈ Icc (1/4:ℝ) 1 →
      b' ∈ Icc (1/4:ℝ) 1 → G a b = G a' b' → a = a' ∧ b = b')
    (p q p' q' : ℝ) (hp : -1/4 ≤ p ∧ p ≤ 1/2) (hq : -1/4 ≤ q ∧ q ≤ 1/2)
    (hp' : -1/4 ≤ p' ∧ p' ≤ 1/2) (hq' : -1/4 ≤ q' ∧ q' ≤ 1/2)
    (hpq : |p| + |q| ≤ 1) (hpq' : |p'| + |q'| ≤ 1)
    (hmeet : ∀ r r' : ℝ, 0 < r → 0 ≤ r' → p * r = p' * r' → q * r = q' * r' → False) :
    (G (1/2 + p * 1) (1/2 + q * 1) - G (1/2 + p * 0) (1/2 + q * 0)) *
      (G (1/2 + p' * 1) (1/2 + q' * 1) - G (1/2 + p' * 0) (1/2 + q' * 0)) ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hcont : ∀ p q : ℝ, -1/4 ≤ p ∧ p ≤ 1/2 → -1/4 ≤ q ∧ q ≤ 1/2 → |p| + |q| ≤ 1 →
      ContinuousOn (fun r => G (1/2 + p * r) (1/2 + q * r)) (Icc 0 1) := by
    intro p q hp hq hpq
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun r hr r' hr' => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    refine (hlip _ _ _ _ (ray_mem hp hr) (ray_mem hq hr) (ray_mem hp hr')
      (ray_mem hq hr')).trans ?_
    rw [ray_dist, ray_dist]
    nlinarith [abs_nonneg (r - r')]
  obtain ⟨r, hr, r', hr', heq⟩ := pair_meet _ _ (hcont p q hp hq hpq) (hcont p' q' hp' hq' hpq')
    (by simp only [mul_zero]) hpos
  have hr1 : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le, hr.2⟩
  obtain ⟨h1, h2⟩ := hinj _ _ _ _ (ray_mem hp hr1) (ray_mem hq hr1) (ray_mem hp' hr')
    (ray_mem hq' hr') heq
  exact hmeet r r' hr.1 hr'.1 (by linarith) (by linarith)

theorem no_inj_square (G : ℝ → ℝ → ℝ)
    (hlip : ∀ a b a' b', a ∈ Icc (1/4:ℝ) 1 → b ∈ Icc (1/4:ℝ) 1 → a' ∈ Icc (1/4:ℝ) 1 →
      b' ∈ Icc (1/4:ℝ) 1 → |G a b - G a' b'| ≤ |a - a'| + |b - b'|)
    (hinj : ∀ a b a' b', a ∈ Icc (1/4:ℝ) 1 → b ∈ Icc (1/4:ℝ) 1 → a' ∈ Icc (1/4:ℝ) 1 →
      b' ∈ Icc (1/4:ℝ) 1 → G a b = G a' b' → a = a' ∧ b = b') : False := by
  -- rays towards `(1, 1/2)`, `(1/2, 1)` and `(1/4, 1/2)`
  have h12 := ray_pair G hlip hinj (1/2) 0 0 (1/2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun r r' hr _ h1 _ => by linarith)
  have h13 := ray_pair G hlip hinj (1/2) 0 (-1/4) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun r r' hr hr' h1 _ => by linarith)
  have h23 := ray_pair G hlip hinj 0 (1/2) (-1/4) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun r r' hr hr' h1 h2 => by linarith)
  norm_num at h12 h13 h23
  have hc : ∀ a b : ℝ, a ∈ Icc (1/4:ℝ) 1 → b ∈ Icc (1/4:ℝ) 1 → (a, b) ≠ (1/2, 1/2) →
      G a b - G (1/2) (1/2) ≠ 0 := by
    intro a b ha hb hab h0
    obtain ⟨h1, h2⟩ := hinj a b (1/2) (1/2) ha hb (by norm_num) (by norm_num) (by linarith)
    exact hab (by rw [h1, h2])
  have d1 := hc 1 (1/2) (by norm_num) (by norm_num) (by norm_num)
  have d2 := hc (1/2) 1 (by norm_num) (by norm_num) (by norm_num)
  have d3 := hc (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num)
  rcases lt_or_gt_of_ne d1 with e1 | e1 <;> rcases lt_or_gt_of_ne d2 with e2 | e2 <;>
    rcases lt_or_gt_of_ne d3 with e3 | e3 <;> nlinarith

namespace Hyp

variable {X : Submodule ℝ (Linf Γ)} {Y : Submodule ℝ (Linf Δ)} {F : Linf Γ → Linf Δ}

/-- The data of the axes: `σ`, `α` and the normalized images of `±eₙ`. -/
structure Axes [DecidableEq Γ] (F : Linf Γ → Linf Δ) (σ : Γ → Δ) (α : Γ → ℝ) : Prop where
  pm : ∀ n, α n = 1 ∨ α n = -1
  zero : ∀ n j, j ≠ σ n → F (sg n 1) j = 0 ∧ F (sg n (-1)) j = 0
  pos : ∀ n, 0 < α n * F (sg n 1) (σ n)
  neg : ∀ n, α n * F (sg n (-1)) (σ n) < 0

/-- `F(-s eₖ)` is a multiple of `e_{σ k}` with the sign of `-s αₖ`. -/
theorem Axes.centre [DecidableEq Γ] {σ : Γ → Δ} {α : Γ → ℝ} (hA : Axes F σ α) (k : Γ) {s : ℝ}
    (hs : s = 1 ∨ s = -1) :
    (∀ j, j ≠ σ k → F (sg k (-s)) j = 0) ∧ s * α k * F (sg k (-s)) (σ k) < 0 := by
  rcases hs with rfl | rfl
  · exact ⟨fun j hj => (hA.zero k j hj).2, by linarith [hA.neg k]⟩
  · rw [neg_neg]
    exact ⟨fun j hj => (hA.zero k j hj).1, by linarith [hA.pos k]⟩

/-- `σ` is injective. -/
theorem sigma_inj [DecidableEq Γ] [DecidableEq Δ] (h : Hyp X Y F) {σ : Γ → Δ} {α : Γ → ℝ}
    (hA : Axes F σ α) : Function.Injective σ := by
  intro n n' hσ
  by_contra hnn'
  obtain ⟨s, hs⟩ : ∃ s, s = α n * α n' := ⟨_, rfl⟩
  have hs1 : s = 1 ∨ s = -1 := hs ▸ pm_mul (hA.pm n) (hA.pm n')
  have hss : s * s = 1 := pm_mul_self hs1
  have hc1 := hA.centre n (Or.inl rfl : (1:ℝ) = 1 ∨ (1:ℝ) = -1)
  have hc2 := hA.centre n' hs1
  have hsα : s * α n' = α n := by rw [hs, mul_assoc, pm_mul_self (hA.pm n'), mul_one]
  rw [hsα, ← hσ] at hc2
  have hc1m : sg n (-1) ∈ ballIn X := single_mem h.hX0 n (by norm_num)
  have hc2m : sg n' (-s) ∈ ballIn X := single_mem h.hX0 n' (by rw [abs_neg]; exact pm_abs hs1)
  -- the two-parameter family `x a b = a eₙ + s b eₙ'`
  have hxn : ∀ a b : ℝ, (sg n a + sg n' (s * b)) n = a := by
    intro a b; rw [two_apply, if_pos rfl, if_neg hnn', add_zero]
  have hxn' : ∀ a b : ℝ, (sg n a + sg n' (s * b)) n' = s * b := by
    intro a b; rw [two_apply, if_neg (Ne.symm hnn'), if_pos rfl, zero_add]
  have hxi : ∀ a b : ℝ, ∀ i, i ≠ n → i ≠ n' → (sg n a + sg n' (s * b)) i = 0 := by
    intro a b i h1 h2; rw [two_apply, if_neg h1, if_neg h2, add_zero]
  have hsb : ∀ b : ℝ, b ∈ Icc (1/4:ℝ) 1 → |s * b| ≤ 1 := by
    intro b hb
    rw [abs_mul, abs_of_nonneg (by linarith [hb.1] : (0:ℝ) ≤ b)]
    rcases hs1 with h' | h' <;> rw [h'] <;> norm_num <;> exact hb.2
  have hxm : ∀ a b : ℝ, a ∈ Icc (1/4:ℝ) 1 → b ∈ Icc (1/4:ℝ) 1 →
      sg n a + sg n' (s * b) ∈ ballIn X := by
    intro a b ha hb
    exact two_mem h.hX0 hnn' (by rw [abs_le]; constructor <;> linarith [ha.1, ha.2]) (hsb b hb)
  -- the image of the family lies on the line `ℝ e_{σ n}`
  have hsupp : ∀ a b : ℝ, a ∈ Icc (1/4:ℝ) 1 → b ∈ Icc (1/4:ℝ) 1 →
      ∀ j, j ≠ σ n → F (sg n a + sg n' (s * b)) j = 0 := by
    intro a b ha hb j hj
    have hclose : ∀ p ∈ ballIn Y, p (σ n) = α n →
        ∀ i, |p i - F (sg n a + sg n' (s * b)) i| ≤ 1 := by
      intro p hp hpm
      obtain ⟨c, hc, hcl⟩ := h.transfer {sg n a + sg n' (s * b), sg n (-1), sg n' (-s)} (by
          intro c hc
          rcases hc with hc | hc | hc
          · rw [hc]; exact hxm a b ha hb
          · rw [hc]; exact hc1m
          · rw [hc]; exact hc2m) (by
          intro u hu
          have hu1 := abs_le_one_of_mem hu
          by_cases h1 : u n ≤ 0
          · refine ⟨sg n (-1), Or.inr (Or.inl rfl), fun i => ?_⟩
            rw [single_apply']
            split_ifs with hi
            · rw [hi]; have := hu1 n; rw [abs_le] at this ⊢; constructor <;> linarith
            · rw [sub_zero]; exact hu1 i
          by_cases h2 : s * u n' ≤ 0
          · refine ⟨sg n' (-s), Or.inr (Or.inr rfl), fun i => ?_⟩
            rw [single_apply']
            split_ifs with hi
            · rw [hi]; have := hu1 n'; rw [abs_le] at this ⊢
              rcases hs1 with h' | h' <;> rw [h'] at h2 ⊢ <;> constructor <;> linarith
            · rw [sub_zero]; exact hu1 i
          · push Not at h1 h2
            refine ⟨sg n a + sg n' (s * b), Or.inl rfl, fun i => ?_⟩
            by_cases hin : i = n
            · rw [hin, hxn]; have := hu1 n; rw [abs_le] at this ⊢
              constructor <;> linarith [ha.1, ha.2]
            by_cases hin' : i = n'
            · rw [hin', hxn']; have := hu1 n'; rw [abs_le] at this ⊢
              rcases hs1 with h' | h' <;> rw [h'] at h2 ⊢ <;> constructor <;>
                linarith [hb.1, hb.2]
            · rw [hxi a b i hin hin', sub_zero]; exact hu1 i) hp
      rcases hc with hc | hc | hc
      · rw [hc] at hcl; exact hcl
      · exfalso
        rw [hc] at hcl
        have h1 := hcl (σ n)
        rw [hpm] at h1
        have h2 := far_of_neg (hA.pm n) (by linarith [hc1.2] : α n * F (sg n (-1)) (σ n) < 0)
        linarith
      · exfalso
        rw [hc] at hcl
        have h1 := hcl (σ n)
        rw [hpm] at h1
        have h2 := far_of_neg (hA.pm n) hc2.2
        linarith
    have hpt : ∀ τ : ℝ, |τ| ≤ 1 → |τ - F (sg n a + sg n' (s * b)) j| ≤ 1 := by
      intro τ hτ
      have := hclose (sg (σ n) (α n) + sg j τ) (two_mem h.hY0 (Ne.symm hj) (pm_abs (hA.pm n)) hτ)
        (by rw [two_apply, if_pos rfl, if_neg (Ne.symm hj), add_zero]) j
      rwa [two_apply, if_neg hj, if_pos rfl, zero_add] at this
    exact eq_zero_of_close (hpt 1 (by norm_num)) (hpt (-1) (by norm_num))
  -- a continuous injective function on a square
  refine no_inj_square (fun a b => F (sg n a + sg n' (s * b)) (σ n)) ?_ ?_
  · intro a b a' b' ha hb ha' hb'
    refine h.coord_le' (hxm a b ha hb) (hxm a' b' ha' hb') (by positivity) (fun i => ?_) (σ n)
    by_cases hin : i = n
    · rw [hin, hxn, hxn]; linarith [abs_nonneg (b - b')]
    by_cases hin' : i = n'
    · rw [hin', hxn', hxn', ← mul_sub, abs_mul]
      rcases hs1 with h' | h' <;> rw [h'] <;> norm_num
    · rw [hxi a b i hin hin', hxi a' b' i hin hin', sub_zero, abs_zero]; positivity
  · intro a b a' b' ha hb ha' hb' heq
    have hF : F (sg n a + sg n' (s * b)) = F (sg n a' + sg n' (s * b')) := by
      apply lp.ext
      funext j
      by_cases hj : j = σ n
      · rw [hj]; exact heq
      · show F _ j = F _ j
        rw [hsupp a b ha hb j hj, hsupp a' b' ha' hb' j hj]
    have hx := h.bij.injOn (hxm a b ha hb) (hxm a' b' ha' hb') hF
    have e1 := congrArg (fun z : Linf Γ => z n) hx
    have e2 := congrArg (fun z : Linf Γ => z n') hx
    simp only [hxn, hxn'] at e1 e2
    refine ⟨e1, ?_⟩
    have := congrArg (fun t => s * t) e2
    rwa [← mul_assoc, ← mul_assoc, hss, one_mul, one_mul] at this

/-- A finitely supported point of `B_Y` with prescribed values `g k` at the coordinates `σ k`
(and zero elsewhere), for injective `σ`. -/
theorem extend_point {σ : Γ → Δ} (hσ : Function.Injective σ) (g : Γ → ℝ)
    (hg1 : ∀ k, |g k| ≤ 1) (hgs : (Function.support g).Finite) :
    (∀ j, |Function.extend σ g 0 j| ≤ 1) ∧ (Function.support (Function.extend σ g 0)).Finite ∧
      (∀ k, Function.extend σ g 0 (σ k) = g k) := by
  classical
  have hyσ : ∀ k, Function.extend σ g 0 (σ k) = g k := fun k => hσ.extend_apply g 0 k
  have hyo : ∀ j, (¬ ∃ k, σ k = j) → Function.extend σ g 0 j = 0 := fun j hj => by
    rw [Function.extend_apply' g (0 : Δ → ℝ) j hj]; rfl
  refine ⟨fun j => ?_, ?_, hyσ⟩
  · by_cases hj : ∃ k, σ k = j
    · obtain ⟨k, rfl⟩ := hj; rw [hyσ]; exact hg1 k
    · rw [hyo j hj]; simp
  · apply (hgs.image σ).subset
    intro j hj
    rw [Function.mem_support] at hj
    by_cases hj' : ∃ k, σ k = j
    · obtain ⟨k, rfl⟩ := hj'
      rw [hyσ] at hj
      exact ⟨k, hj, rfl⟩
    · exact absurd (hyo j hj') hj

/-- Zero and sign rules at finitely supported points. -/
theorem sign_fin [DecidableEq Γ] [DecidableEq Δ] (h : Hyp X Y F) {σ : Γ → Δ} {α : Γ → ℝ}
    (hA : Axes F σ α) (hσ : Function.Injective σ)
    {x : Linf Γ} (hx : x ∈ ballIn X) (hfin : (Function.support ⇑x).Finite) :
    (∀ n, x n ≠ 0 → 0 ≤ Real.sign (x n) * α n * F x (σ n)) ∧
      (∀ m, (∀ n, x n ≠ 0 → σ n ≠ m) → F x m = 0) := by
  have hx1 := abs_le_one_of_mem hx
  have hsg : ∀ k, x k ≠ 0 → Real.sign (x k) = 1 ∨ Real.sign (x k) = -1 :=
    fun k hk => sign_eq _ hk
  -- the covering of `B_X` by `B(x,1)` and the balls `B(-sgn(xₖ) eₖ, 1)`
  let C : Set (Linf Γ) := insert x {c | ∃ k, x k ≠ 0 ∧ c = sg k (-Real.sign (x k))}
  have hC : C ⊆ ballIn X := by
    intro c hc
    rcases hc with hc | ⟨k, hk, hc⟩
    · rw [hc]; exact hx
    · rw [hc]; exact single_mem h.hX0 k (by rw [abs_neg]; exact pm_abs (hsg k hk))
  have hcov : ∀ u ∈ ballIn X, ∃ c ∈ C, ∀ i, |u i - c i| ≤ 1 := by
    intro u hu
    have hu1 := abs_le_one_of_mem hu
    by_cases hk : ∃ k, x k ≠ 0 ∧ Real.sign (x k) * u k ≤ 0
    · obtain ⟨k, hk0, hku⟩ := hk
      refine ⟨sg k (-Real.sign (x k)), Or.inr ⟨k, hk0, rfl⟩, fun i => ?_⟩
      rw [single_apply']
      split_ifs with hi
      · rw [hi]; have := hu1 k; rw [abs_le] at this ⊢
        rcases hsg k hk0 with hs | hs <;> rw [hs] at hku ⊢ <;> constructor <;> linarith
      · rw [sub_zero]; exact hu1 i
    · push Not at hk
      refine ⟨x, Or.inl rfl, fun i => ?_⟩
      by_cases hxi : x i = 0
      · rw [hxi, sub_zero]; exact hu1 i
      · apply close_of_same_sign (hu1 i) (hx1 i)
        have := hk i hxi
        rcases lt_or_gt_of_ne hxi with h' | h'
        · rw [Real.sign_of_neg h'] at this; nlinarith
        · rw [Real.sign_of_pos h'] at this; nlinarith
  -- points carrying the signs `sgn(xₖ) αₖ` at `σ k` are within `1` of `F x`
  have hclose : ∀ p ∈ ballIn Y, (∀ k, x k ≠ 0 → p (σ k) = Real.sign (x k) * α k) →
      ∀ j, |p j - F x j| ≤ 1 := by
    intro p hp hpk
    obtain ⟨c, hc, hcl⟩ := h.transfer C hC hcov hp
    rcases hc with hc | ⟨k, hk, hc⟩
    · rw [hc] at hcl; exact hcl
    · exfalso
      rw [hc] at hcl
      have h1 := hcl (σ k)
      rw [hpk k hk] at h1
      have h2 := far_of_neg (pm_mul (hsg k hk) (hA.pm k)) (hA.centre k (hsg k hk)).2
      linarith
  -- the point `y = Σ sgn(xₖ) αₖ e_{σ k}`
  let g : Γ → ℝ := fun k => Real.sign (x k) * α k
  have hg1 : ∀ k, |g k| ≤ 1 := by
    intro k
    by_cases hk : x k = 0
    · simp [g, hk, Real.sign_zero]
    · exact pm_abs (pm_mul (hsg k hk) (hA.pm k))
  have hgs : (Function.support g).Finite := by
    apply hfin.subset
    intro k hk
    rw [Function.mem_support] at hk ⊢
    intro h0
    apply hk
    simp [g, h0, Real.sign_zero]
  obtain ⟨hyb, hys, hyσ⟩ := extend_point hσ g hg1 hgs
  set yf := Function.extend σ g 0 with hyf
  refine ⟨fun n hn => ?_, fun m hm => ?_⟩
  · have := hclose (pt yf hyb) (pt_mem h.hY0 yf hyb hys) (fun k _ => by rw [pt_apply, hyσ])
      (σ n)
    rw [pt_apply, hyσ] at this
    exact nonneg_of_close (pm_mul (hsg n hn) (hA.pm n)) this
  · have hτ : ∀ τ : ℝ, |τ| ≤ 1 → |τ - F x m| ≤ 1 := by
      intro τ hτ
      have hzb : ∀ j, |Function.update yf m τ j| ≤ 1 := by
        intro j
        by_cases hj : j = m
        · rw [hj, Function.update_self]; exact hτ
        · rw [Function.update_of_ne hj]; exact hyb j
      have hzs : (Function.support (Function.update yf m τ)).Finite := by
        apply (hys.insert m).subset
        intro j hj
        by_cases hjm : j = m
        · exact Or.inl hjm
        · right
          rw [Function.mem_support, Function.update_of_ne hjm] at hj
          exact hj
      have := hclose (pt _ hzb) (pt_mem h.hY0 _ hzb hzs)
        (fun k hk => by rw [pt_apply, Function.update_of_ne (hm k hk), hyσ]) m
      rwa [pt_apply, Function.update_self] at this
    exact eq_zero_of_close (hτ 1 (by norm_num)) (hτ (-1) (by norm_num))

/-- The sign rule at every point. -/
theorem sign_all [DecidableEq Γ] [DecidableEq Δ] (h : Hyp X Y F) {σ : Γ → Δ} {α : Γ → ℝ}
    (hA : Axes F σ α) (hσ : Function.Injective σ) :
    ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ α n * F x (σ n)) ∧ (x n ≤ 0 → α n * F x (σ n) ≤ 0) := by
  have hfin : ∀ x ∈ ballIn X, (Function.support ⇑x).Finite → ∀ n,
      (0 ≤ x n → 0 ≤ α n * F x (σ n)) ∧ (x n ≤ 0 → α n * F x (σ n) ≤ 0) := by
    intro x hx hxf n
    obtain ⟨h1, h2⟩ := h.sign_fin hA hσ hx hxf
    rcases lt_trichotomy (x n) 0 with hn | hn | hn
    · have := h1 n hn.ne
      rw [Real.sign_of_neg hn] at this
      exact ⟨fun h' => absurd h' (not_le.2 hn), fun _ => by linarith⟩
    · have := h2 (σ n) (fun k hk hkn => hk (by rw [hσ hkn]; exact hn))
      rw [this, mul_zero]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
    · have := h1 n hn.ne'
      rw [Real.sign_of_pos hn] at this
      exact ⟨fun _ => by linarith, fun h' => absurd h' (not_le.2 hn)⟩
  intro x hx n
  constructor
  · intro hn
    by_contra hneg
    push Not at hneg
    obtain ⟨x', hx', hx'f, hx'n, hFx⟩ := h.approx hx {n} (Set.finite_singleton n)
      (ε := -(α n * F x (σ n)) / 2) (by linarith)
    have h1 := (hfin x' hx' hx'f n).1 (by rw [hx'n n rfl]; exact hn)
    have h2 := (pm_shift (hA.pm n) (hFx (σ n))).1
    linarith
  · intro hn
    by_contra hpos
    push Not at hpos
    obtain ⟨x', hx', hx'f, hx'n, hFx⟩ := h.approx hx {n} (Set.finite_singleton n)
      (ε := (α n * F x (σ n)) / 2) (by linarith)
    have h1 := (hfin x' hx' hx'f n).2 (by rw [hx'n n rfl]; exact hn)
    have h2 := (pm_shift (hA.pm n) (hFx (σ n))).2
    linarith

/-- `σ` is onto. -/
theorem sigma_surj [DecidableEq Γ] [DecidableEq Δ] (h : Hyp X Y F) {σ : Γ → Δ} {α : Γ → ℝ}
    (hA : Axes F σ α) (hσ : Function.Injective σ) : Function.Surjective σ := by
  intro m
  by_contra hm
  push Not at hm
  have hzero : ∀ x ∈ ballIn X, F x m = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨x', hx', hx'f, -, hFx⟩ := h.approx hx ∅ Set.finite_empty
      (ε := |F x m| / 2) (by positivity)
    have h0 := (h.sign_fin hA hσ hx' hx'f).2 m (fun n _ => hm n)
    have := hFx m
    rw [h0, sub_zero] at this
    have : 0 < |F x m| := abs_pos.2 hne
    linarith
  obtain ⟨u, hu, hFu⟩ := h.bij.surjOn (single_mem h.hY0 m (by norm_num : |(1:ℝ)| ≤ 1))
  have := hzero u hu
  rw [hFu, sg_self] at this
  exact one_ne_zero this

/-- Inwardness at finitely supported points. -/
theorem inward_fin [DecidableEq Γ] [DecidableEq Δ] (h : Hyp X Y F) {σ : Γ → Δ} {α : Γ → ℝ}
    (hA : Axes F σ α) (hσ : Function.Injective σ)
    {x : Linf Γ} (hx : x ∈ ballIn X) (hfin : (Function.support ⇑x).Finite) (n : Γ)
    (hxn : x n ≠ 0) : Real.sign (x n) * α n * F x (σ n) ≤ |x n| := by
  have hx1 := abs_le_one_of_mem hx
  have hsign := h.sign_all hA hσ
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = Real.sign (x n) := ⟨_, rfl⟩
  rw [← hεdef]
  have hε : ε = 1 ∨ ε = -1 := hεdef ▸ sign_eq _ hxn
  -- the target point `y = -ε αₙ e_{σ n} + Σ_{k ≠ n} sgn(xₖ) αₖ e_{σ k}`
  let g : Γ → ℝ := fun k => α k * (if k = n then -ε else Real.sign (x k))
  have hg1 : ∀ k, |g k| ≤ 1 := by
    intro k
    simp only [g]
    rw [abs_mul]
    have ha : |α k| = 1 := by rcases hA.pm k with h' | h' <;> rw [h'] <;> norm_num
    rw [ha, one_mul]
    split_ifs
    · rw [abs_neg]; exact pm_abs hε
    · rcases Real.sign_apply_eq (x k) with h' | h' | h' <;> rw [h'] <;> norm_num
  have hgs : (Function.support g).Finite := by
    apply hfin.subset
    intro k hk
    rw [Function.mem_support] at hk ⊢
    intro h0
    apply hk
    simp only [g]
    split_ifs with hkn
    · rw [hkn] at h0; exact absurd h0 hxn
    · rw [h0, Real.sign_zero, mul_zero]
  obtain ⟨hyb, hys, hyσ⟩ := extend_point hσ g hg1 hgs
  obtain ⟨u, hu, hFu⟩ := h.bij.surjOn (pt_mem h.hY0 _ hyb hys)
  have hu1 := abs_le_one_of_mem hu
  have hFuσ : ∀ k, α k * F u (σ k) = (if k = n then -ε else Real.sign (x k)) := by
    intro k
    rw [hFu, pt_apply, hyσ]
    simp only [g]
    rw [← mul_assoc, pm_mul_self (hA.pm k), one_mul]
  -- by the sign rule, `u` has the strict signs of `x` on the support of `x` away from `n`
  have huk : ∀ k, k ≠ n → x k ≠ 0 → 0 < x k * u k := by
    intro k hkn hk
    have h1 := hFuσ k
    rw [if_neg hkn] at h1
    have hs := hsign u hu k
    rcases lt_or_gt_of_ne hk with hk' | hk'
    · rw [Real.sign_of_neg hk'] at h1
      have : u k < 0 := by
        by_contra hc
        push Not at hc
        have := hs.1 hc
        linarith
      nlinarith
    · rw [Real.sign_of_pos hk'] at h1
      have : 0 < u k := by
        by_contra hc
        push Not at hc
        have := hs.2 hc
        linarith
      nlinarith
  have hcl : ∀ i, |x i - u i| ≤ 1 + |x n| := by
    intro i
    by_cases hin : i = n
    · rw [hin]
      have h1 := abs_le.1 (hu1 n)
      rw [abs_le]
      constructor <;> linarith [le_abs_self (x n), neg_abs_le (x n)]
    · by_cases hxi : x i = 0
      · rw [hxi, zero_sub, abs_neg]; linarith [hu1 i, abs_nonneg (x n)]
      · have := close_of_same_sign (hx1 i) (hu1 i) (huk i hin hxi)
        linarith [abs_nonneg (x n)]
  have hFcl := h.coord_le' hx hu (by positivity) hcl (σ n)
  have hFun := hFuσ n
  rw [if_pos rfl] at hFun
  have h2 := pm_shift (hA.pm n) hFcl
  rcases hε with he | he <;> rw [he] at hFun ⊢ <;> linarith [h2.1, h2.2]

/-- Inwardness at every point. -/
theorem inward_all [DecidableEq Γ] [DecidableEq Δ] (h : Hyp X Y F) {σ : Γ → Δ} {α : Γ → ℝ}
    (hA : Axes F σ α) (hσ : Function.Injective σ) {x : Linf Γ} (hx : x ∈ ballIn X) (n : Γ)
    (hxn : x n ≠ 0) : Real.sign (x n) * α n * F x (σ n) ≤ |x n| := by
  by_contra hgt
  push Not at hgt
  obtain ⟨x', hx', hx'f, hx'n, hFx⟩ := h.approx hx {n} (Set.finite_singleton n)
    (ε := (Real.sign (x n) * α n * F x (σ n) - |x n|) / 2) (by linarith)
  have hn' : x' n = x n := hx'n n rfl
  have h1 := h.inward_fin hA hσ hx' hx'f n (by rw [hn']; exact hxn)
  rw [hn'] at h1
  have h2 := (pm_shift (pm_mul (sign_eq _ hxn) (hA.pm n)) (hFx (σ n))).2
  linarith

end Hyp

end Sol_Plasticity_SeqSpace_exists_signed_permutation_inward

open Sol_Plasticity_SeqSpace_exists_signed_permutation_inward in
theorem solution {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    ∃ σ : Γ ≃ Δ, ∃ α : Γ → ℝ, (∀ n, α n = 1 ∨ α n = -1) ∧
      ∀ x ∈ ballIn X, ∀ n, (0 ≤ x n → 0 ≤ α n * F x (σ n) ∧ α n * F x (σ n) ≤ x n) ∧
        (x n ≤ 0 → x n ≤ α n * F x (σ n) ∧ α n * F x (σ n) ≤ 0) := by
  classical
  have h : Hyp X Y F := ⟨hX0, hX1, hY0, hbij, hlip⟩
  choose σ0 α hα hzero hpos hneg using h.axes
  have hA : Hyp.Axes F σ0 α := ⟨hα, hzero, hpos, hneg⟩
  have hinj := h.sigma_inj hA
  have hsurj := h.sigma_surj hA hinj
  have hsign := h.sign_all hA hinj
  refine ⟨Equiv.ofBijective σ0 ⟨hinj, hsurj⟩, α, hα, fun x hx n => ?_⟩
  change (0 ≤ x n → 0 ≤ α n * F x (σ0 n) ∧ α n * F x (σ0 n) ≤ x n) ∧
    (x n ≤ 0 → x n ≤ α n * F x (σ0 n) ∧ α n * F x (σ0 n) ≤ 0)
  have hs := hsign x hx n
  refine ⟨fun hn => ⟨hs.1 hn, ?_⟩, fun hn => ⟨?_, hs.2 hn⟩⟩
  · rcases hn.lt_or_eq with hn' | hn'
    · have := h.inward_all hA hinj hx n hn'.ne'
      rw [Real.sign_of_pos hn', one_mul, abs_of_pos hn'] at this
      exact this
    · rw [← hn']; exact hs.2 hn'.ge
  · rcases hn.lt_or_eq with hn' | hn'
    · have := h.inward_all hA hinj hx n hn'.ne
      rw [Real.sign_of_neg hn', abs_of_neg hn'] at this
      linarith
    · rw [hn']; exact hs.1 hn'.ge
