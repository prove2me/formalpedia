-- Prove2me | solution 1 for StrictCQ.AGP.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:18:44.30887+00:00
-- url     : https://prove2.me/submissions/3eca0868-ba00-48e6-bcaa-9a4feee42548

import Mathlib
import Definitions.Def_StrictCQ_AGP_Conditions

open Filter Topology InnerProductSpace

namespace RRAux_StrictCQ_AGP_theorem_4_2

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (u : κ → E)

def coneS (s : Finset κ) : Set E :=
  {x | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ x = ∑ k, c k • u k}

lemma sum_sub_eq (s : Finset κ) (c : κ → ℝ) (hc : ∀ k ∉ s, c k = 0) :
    ∑ k : s, c k • u k = ∑ k, c k • u k := by
  rw [Finset.sum_coe_sort s (fun k => c k • u k)]
  exact Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by rw [hc k hk, zero_smul])

lemma coneS_LI_closed (s : Finset κ) (hli : LinearIndependent ℝ (fun k : s => u k)) :
    IsClosed (coneS u s) := by
  set Λ := Fintype.linearCombination ℝ (fun k : s => u k) with hΛ
  have hker : LinearMap.ker Λ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hΛ, Fintype.linearCombination_apply] at hc
    funext k
    exact Fintype.linearIndependent_iff.1 hli c hc k
  have heq : coneS u s = Λ '' {c | ∀ k, 0 ≤ c k} := by
    ext x
    constructor
    · rintro ⟨c, hc0, hcs, rfl⟩
      refine ⟨fun k => c k, fun k => hc0 k, ?_⟩
      rw [hΛ, Fintype.linearCombination_apply]
      exact sum_sub_eq u s c hcs
    · rintro ⟨c, hc0, rfl⟩
      refine ⟨fun k => if h : k ∈ s then c ⟨k, h⟩ else 0, fun k => ?_, fun k hk => ?_, ?_⟩
      · by_cases h : k ∈ s
        · simp only [h, dif_pos]; exact hc0 _
        · simp [h]
      · simp [hk]
      · rw [hΛ, Fintype.linearCombination_apply, ← sum_sub_eq u s _ (fun k hk => by simp [hk])]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp
  have hQ : {c : s → ℝ | ∀ k, 0 ≤ c k} = ⋂ k, {c : s → ℝ | 0 ≤ c k} := by ext; simp
  rw [heq, hQ]
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap _
    (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k))

lemma cara_step (s : Finset κ) (hdep : ¬ LinearIndependent ℝ (fun k : s => u k)) :
    coneS u s ⊆ ⋃ k ∈ s, coneS u (s.erase k) := by
  rintro x ⟨c, hc0, hcs, rfl⟩
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  set a0 : κ → ℝ := fun k => if h : k ∈ s then g ⟨k, h⟩ else 0 with ha0
  have ha0s : ∀ k ∉ s, a0 k = 0 := fun k hk => by simp [ha0, hk]
  have ha0sum : ∑ k, a0 k • u k = 0 := by
    rw [← sum_sub_eq u s a0 ha0s, ← hg]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ha0]
  have ha0i : a0 i ≠ 0 := by simpa [ha0] using hi
  -- get a with a positive entry
  obtain ⟨a, has, hasum, k1, hk1⟩ : ∃ a : κ → ℝ, (∀ k ∉ s, a k = 0) ∧ ∑ k, a k • u k = 0 ∧
      ∃ k1, 0 < a k1 := by
    rcases lt_or_gt_of_ne ha0i with h | h
    · refine ⟨-a0, fun k hk => by simp [ha0s k hk], ?_, i, by simp; linarith⟩
      simp [neg_smul, Finset.sum_neg_distrib, ha0sum]
    · exact ⟨a0, ha0s, ha0sum, i, h⟩
  have hk1s : k1 ∈ s := by by_contra h; rw [has k1 h] at hk1; exact lt_irrefl _ hk1
  set P := s.filter (fun k => 0 < a k) with hP
  have hPne : P.Nonempty := ⟨k1, Finset.mem_filter.2 ⟨hk1s, hk1⟩⟩
  obtain ⟨k0, hk0P, hmin⟩ := Finset.exists_min_image P (fun k => c k / a k) hPne
  have hk0 := Finset.mem_filter.1 hk0P
  set t := c k0 / a k0 with ht
  have ht0 : 0 ≤ t := div_nonneg (hc0 k0) hk0.2.le
  refine Set.mem_biUnion hk0.1 ⟨fun k => c k - t * a k, fun k => ?_, fun k hk => ?_, ?_⟩
  · by_cases hak : 0 < a k
    · by_cases hks : k ∈ s
      · have := hmin k (Finset.mem_filter.2 ⟨hks, hak⟩)
        rw [div_le_div_iff₀ hk0.2 hak] at this
        have : t * a k ≤ c k := by
          rw [ht, div_mul_eq_mul_div, div_le_iff₀ hk0.2]; linarith
        linarith
      · rw [has k hks] at hak; exact absurd hak (lt_irrefl _)
    · push Not at hak
      nlinarith [hc0 k]
  · rcases Finset.mem_erase.not.1 hk |> not_and_or.1 with h | h
    · push Not at h; subst h
      show c k - t * a k = 0
      rw [ht, div_mul_cancel₀ _ hk0.2.ne', sub_self]
    · show c k - t * a k = 0
      rw [hcs k h, has k h]; ring
  · simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hasum, smul_zero,
      sub_zero]

lemma coneS_closed : ∀ s : Finset κ, IsClosed (coneS u s) := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hli : LinearIndependent ℝ (fun k : s => u k)
    · exact coneS_LI_closed u s hli
    · have heq : coneS u s = ⋃ k ∈ s, coneS u (s.erase k) := by
        refine Set.Subset.antisymm (cara_step u s hli) ?_
        refine Set.iUnion₂_subset fun k _ => ?_
        rintro x ⟨c, hc0, hcs, rfl⟩
        exact ⟨c, hc0, fun j hj => hcs j (fun h => hj (Finset.mem_of_mem_erase h)), rfl⟩
      rw [heq]
      exact isClosed_biUnion_finset fun k hk => ih _ (Finset.erase_ssubset hk)

/-- Farkas' lemma for a finite family. -/
lemma farkas (w : E) (h : ∀ d : E, (∀ k, ⟪u k, d⟫_ℝ ≤ 0) → ⟪w, d⟫_ℝ ≤ 0) :
    ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ w = ∑ k, c k • u k := by
  by_contra hw
  have hK : IsClosed (coneS u Finset.univ) := coneS_closed u _
  have hcv : Convex ℝ (coneS u Finset.univ) := by
    rintro a ⟨ca, ha0, -, rfl⟩ b ⟨cb, hb0, -, rfl⟩ s t hs ht hst
    refine ⟨fun k => s * ca k + t * cb k, fun k => by have := ha0 k; have := hb0 k; positivity,
      fun k hk => absurd (Finset.mem_univ k) hk, ?_⟩
    simp [add_smul, mul_smul, Finset.smul_sum, Finset.sum_add_distrib]
  have hnot : w ∉ coneS u Finset.univ := by
    rintro ⟨c, hc0, -, rfl⟩; exact hw ⟨c, hc0, rfl⟩
  obtain ⟨F, s, hFw, hFb⟩ := geometric_hahn_banach_point_closed hcv hK hnot
  have h0mem : (0 : E) ∈ coneS u Finset.univ := ⟨0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩
  have hs0 : s < 0 := by simpa using hFb 0 h0mem
  have hFnn : ∀ b ∈ coneS u Finset.univ, 0 ≤ F b := by
    rintro b ⟨c, hc0, -, rfl⟩
    by_contra hneg
    push Not at hneg
    set b := ∑ k, c k • u k
    have hmem : (s / F b) • b ∈ coneS u Finset.univ :=
      ⟨fun k => (s / F b) * c k, fun k => mul_nonneg (div_nonneg_of_nonpos hs0.le hneg.le) (hc0 k),
        fun k hk => absurd (Finset.mem_univ k) hk, by simp [b, Finset.smul_sum, smul_smul]⟩
    have := hFb _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  set d := -(InnerProductSpace.toDual ℝ E).symm F
  have hd : ∀ v, ⟪v, d⟫_ℝ = -F v := by
    intro v
    rw [inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have := h d (fun k => by
    rw [hd]
    have : u k ∈ coneS u Finset.univ := ⟨Pi.single k 1, fun j => by
        by_cases hj : j = k
        · subst hj; simp
        · simp [hj], fun j hj => absurd (Finset.mem_univ j) hj, by simp [Pi.single_apply]⟩
    linarith [hFnn _ this])
  rw [hd] at this
  linarith

end

open StrictCQ.AGP

abbrev EE (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma grad_cont {n : ℕ} (f : EE n → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  show Continuous fun x => (InnerProductSpace.toDual ℝ (EE n)).symm (fderiv ℝ f x)
  exact (LinearIsometryEquiv.continuous _).comp (hf.continuous_fderiv one_ne_zero)

lemma lin_grad {n : ℕ} (c z : EE n) : gradient (fun z : EE n => ⟪c, z⟫_ℝ) z = c := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (InnerProductSpace.toDual ℝ (EE n) c).hasFDerivAt

lemma lin_C1 {n : ℕ} (c : EE n) : ContDiff ℝ 1 (fun z : EE n => ⟪c, z⟫_ℝ) :=
  (InnerProductSpace.toDual ℝ (EE n) c).contDiff

lemma comb_sub {n : ℕ} (a b x : EE n) (s t : ℝ) (hst : s + t = 1) :
    (s • a + t • b) - x = s • (a - x) + t • (b - x) := by
  obtain rfl : t = 1 - s := by linarith
  module

lemma linSet_convex {n m p : ℕ} (C : Constraints n m p) (x : EE n) (γ : EReal) :
    Convex ℝ (C.linSet x γ) := by
  intro a ha b hb s t hs ht hst
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨fun i => ?_, fun j hj => ?_, fun j hj1 hj2 => ?_⟩
  · rw [comb_sub a b x s t hst, inner_add_right, inner_smul_right, inner_smul_right, ha1, hb1]
    ring
  · rw [comb_sub a b x s t hst, inner_add_right, inner_smul_right, inner_smul_right]
    have := ha2 j hj; have := hb2 j hj
    nlinarith
  · rw [comb_sub a b x s t hst, inner_add_right, inner_smul_right, inner_smul_right]
    have h1 := ha3 j hj1 hj2; have h2 := hb3 j hj1 hj2
    have e : C.g j x + (s * ⟪gradient (C.g j) x, a - x⟫_ℝ + t * ⟪gradient (C.g j) x, b - x⟫_ℝ)
        = s * (C.g j x + ⟪gradient (C.g j) x, a - x⟫_ℝ) +
          t * (C.g j x + ⟪gradient (C.g j) x, b - x⟫_ℝ) := by
      linear_combination (-(C.g j x)) * hst
    rw [e]
    nlinarith

lemma linSet_closed {n m p : ℕ} (C : Constraints n m p) (x : EE n) (γ : EReal) :
    IsClosed (C.linSet x γ) := by
  have e : C.linSet x γ =
      (⋂ i, {z | ⟪gradient (C.h i) x, z - x⟫_ℝ = 0}) ∩
      ((⋂ j, {z | 0 ≤ C.g j x → ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0}) ∩
      (⋂ j, {z | γ < (C.g j x : EReal) → C.g j x < 0 →
        C.g j x + ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0})) := by
    ext z; simp [Constraints.linSet]
  rw [e]
  refine (isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
    ((isClosed_iInter fun j => ?_).inter (isClosed_iInter fun j => ?_))
  · by_cases h : 0 ≤ C.g j x
    · simp only [h, true_implies]; exact isClosed_le (by fun_prop) continuous_const
    · simp only [h, false_implies, Set.setOf_true]; exact isClosed_univ
  · by_cases h : γ < (C.g j x : EReal) ∧ C.g j x < 0
    · have e2 : {z : EE n | γ < (C.g j x : EReal) → C.g j x < 0 →
          C.g j x + ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0} =
          {z : EE n | C.g j x + ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0} := by
        ext z; simp only [Set.mem_setOf_eq]
        exact ⟨fun hz => hz h.1 h.2, fun hz _ _ => hz⟩
      rw [e2]; exact isClosed_le (by fun_prop) continuous_const
    · have e2 : {z : EE n | γ < (C.g j x : EReal) → C.g j x < 0 →
          C.g j x + ⟪gradient (C.g j) x, z - x⟫_ℝ ≤ 0} = Set.univ := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h1 h2; exact absurd ⟨h1, h2⟩ h
      rw [e2]; exact isClosed_univ

lemma proj_VI {n : ℕ} {S : Set (EE n)} (hS : Convex ℝ S) {z y : EE n} (h : IsProj S z y) :
    ∀ w ∈ S, ⟪z - y, w - y⟫_ℝ ≤ 0 := by
  have hbdd : BddBelow (Set.range fun w : S => ‖z - (w : EE n)‖) :=
    ⟨0, fun _ hr => by obtain ⟨w, rfl⟩ := hr; exact norm_nonneg _⟩
  refine (norm_eq_iInf_iff_real_inner_le_zero hS h.1).1 (le_antisymm ?_ ?_)
  · haveI : Nonempty S := ⟨⟨y, h.1⟩⟩
    exact le_ciInf fun w => h.2 w w.2
  · exact ciInf_le hbdd (⟨y, h.1⟩ : S)

lemma proj_exists {n : ℕ} {S : Set (EE n)} (hc : IsClosed S) (hS : Convex ℝ S) (hne : S.Nonempty)
    (z : EE n) : ∃ y, IsProj S z y := by
  obtain ⟨y, hy, hyeq⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hS z
  have hbdd : BddBelow (Set.range fun w : S => ‖z - (w : EE n)‖) :=
    ⟨0, fun _ hr => by obtain ⟨w, rfl⟩ := hr; exact norm_nonneg _⟩
  refine ⟨y, hy, fun w hw => ?_⟩
  rw [hyeq]
  exact ciInf_le hbdd (⟨w, hw⟩ : S)

lemma nonexp {n : ℕ} {S : Set (EE n)} (hS : Convex ℝ S) {z1 y1 z2 y2 : EE n}
    (h1 : IsProj S z1 y1) (hy2 : y2 ∈ S) (h2 : ∀ w ∈ S, ⟪z2 - y2, w - y2⟫_ℝ ≤ 0) :
    ‖y1 - y2‖ ≤ ‖z1 - z2‖ := by
  have a1 := proj_VI hS h1 y2 hy2
  have a2 := h2 y1 h1.1
  have key : ‖y1 - y2‖ ^ 2 ≤ ⟪z1 - z2, y1 - y2⟫_ℝ := by
    have hneg : y2 - y1 = -(y1 - y2) := by abel
    rw [hneg, inner_neg_right] at a1
    have hz : z1 - z2 = (z1 - y1) - (z2 - y2) + (y1 - y2) := by abel
    rw [hz, inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq]
    linarith
  have hcs := real_inner_le_norm (z1 - z2) (y1 - y2)
  by_cases h0 : ‖y1 - y2‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖y1 - y2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma polar_of_normal {n m p : ℕ} (C : Constraints n m p) (xs : EE n) (hxs : xs ∈ C.feasible)
    (w : EE n) (hw : w ∈ normalCone (C.linSet xs ⊥) xs) (d : EE n)
    (hd1 : ∀ i, ⟪gradient (C.h i) xs, d⟫_ℝ = 0)
    (hd2 : ∀ j, C.g j xs = 0 → ⟪gradient (C.g j) xs, d⟫_ℝ ≤ 0) : ⟪w, d⟫_ℝ ≤ 0 := by
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, C.g j xs < 0 →
      C.g j xs + t * ⟪gradient (C.g j) xs, d⟫_ℝ < 0 := by
    rw [eventually_all]
    intro j
    by_cases hj : C.g j xs < 0
    · have ht : Tendsto (fun t : ℝ => C.g j xs + t * ⟪gradient (C.g j) xs, d⟫_ℝ) (𝓝 0)
          (𝓝 (C.g j xs + 0 * ⟪gradient (C.g j) xs, d⟫_ℝ)) :=
        tendsto_const_nhds.add (tendsto_id.mul_const _)
      rw [zero_mul, add_zero] at ht
      filter_upwards [ht.eventually (gt_mem_nhds hj)] with t h _
      exact h
    · exact Eventually.of_forall fun t h => absurd h hj
  obtain ⟨t, ht1, ht2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioi 0)).exists
  have ht2' : 0 < t := ht2
  have hmem : xs + t • d ∈ C.linSet xs ⊥ := by
    refine ⟨fun i => ?_, fun j hj => ?_, fun j _ hj => ?_⟩
    · rw [add_sub_cancel_left, inner_smul_right, hd1, mul_zero]
    · rw [add_sub_cancel_left, inner_smul_right]
      have : C.g j xs = 0 := le_antisymm (hxs.2 j) hj
      exact mul_nonpos_of_nonneg_of_nonpos ht2'.le (hd2 j this)
    · rw [add_sub_cancel_left, inner_smul_right]
      exact (ht1 j hj).le
  have := hw.2 _ hmem
  rw [add_sub_cancel_left, inner_smul_right] at this
  by_contra hc
  push Not at hc
  have := mul_pos ht2' hc
  linarith

lemma kkt_of_polar {n m p : ℕ} (C : Constraints n m p) (xs : EE n) (f : EE n → ℝ)
    (h : ∀ d, (∀ i, ⟪gradient (C.h i) xs, d⟫_ℝ = 0) →
      (∀ j, C.g j xs = 0 → ⟪gradient (C.g j) xs, d⟫_ℝ ≤ 0) → ⟪-gradient f xs, d⟫_ℝ ≤ 0) :
    C.IsKKT f xs := by
  classical
  set u : (Fin m ⊕ Fin m) ⊕ Fin p → EE n :=
    Sum.elim (Sum.elim (fun i => gradient (C.h i) xs) (fun i => -gradient (C.h i) xs))
      (fun j => if C.g j xs = 0 then gradient (C.g j) xs else 0) with hu
  obtain ⟨c, hc0, hc⟩ := farkas u (-gradient f xs) (fun d hd => h d
    (fun i => le_antisymm (by simpa only [hu, Sum.elim_inl] using hd (Sum.inl (Sum.inl i)))
      (by have := hd (Sum.inl (Sum.inr i))
          simp only [hu, Sum.elim_inl, Sum.elim_inr, inner_neg_left] at this; linarith))
    (fun j hj => by
      have := hd (Sum.inr j); simpa only [hu, Sum.elim_inr, hj, if_true] using this))
  refine ⟨fun i => c (Sum.inl (Sum.inl i)) - c (Sum.inl (Sum.inr i)),
    fun j => if C.g j xs = 0 then c (Sum.inr j) else 0, fun j => ?_, fun j hj => by simp [hj], ?_⟩
  · show 0 ≤ (if C.g j xs = 0 then c (Sum.inr j) else 0)
    split_ifs
    · exact hc0 _
    · exact le_rfl
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hc
    simp only [hu, Sum.elim_inl, Sum.elim_inr] at hc
    have e : ∑ i, (c (Sum.inl (Sum.inl i)) - c (Sum.inl (Sum.inr i))) • gradient (C.h i) xs +
        ∑ j, (if C.g j xs = 0 then c (Sum.inr j) else 0) • gradient (C.g j) xs
        = -gradient f xs := by
      rw [hc]
      have e2 : ∑ j, (if C.g j xs = 0 then c (Sum.inr j) else 0) • gradient (C.g j) xs
          = ∑ j, c (Sum.inr j) • (if C.g j xs = 0 then gradient (C.g j) xs else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [e2]
      simp only [sub_eq_add_neg, add_smul, neg_smul, Finset.sum_add_distrib,
        Finset.sum_neg_distrib, smul_neg]
    rw [add_assoc, e, add_neg_cancel]

lemma normal_of_kkt {n m p : ℕ} (C : Constraints n m p) (xs : EE n) (hxs : xs ∈ C.feasible)
    (w : EE n) (hK : C.IsKKT (fun z => ⟪-w, z⟫_ℝ) xs) : w ∈ normalCone (C.linSet xs ⊥) xs := by
  obtain ⟨lam, mu, h0, hc, heq⟩ := hK
  rw [lin_grad] at heq
  have hw : w = ∑ i, lam i • gradient (C.h i) xs + ∑ j, mu j • gradient (C.g j) xs := by
    rw [add_assoc, neg_add_eq_zero] at heq
    exact heq
  refine ⟨⟨fun i => by simp, fun j _ => by simp, fun j _ hj => by simpa using hj.le⟩,
    fun z hz => ?_⟩
  rw [hw, inner_add_left, sum_inner, sum_inner]
  simp only [real_inner_smul_left, hz.1, mul_zero, Finset.sum_const_zero, zero_add]
  apply Finset.sum_nonpos
  intro j _
  by_cases hj : C.g j xs = 0
  · exact mul_nonpos_of_nonneg_of_nonpos (h0 j) (hz.2.1 j hj.ge)
  · rw [hc j hj, zero_mul]

end RRAux_StrictCQ_AGP_theorem_4_2

open StrictCQ.AGP in
theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    C.AGPRegular xs ↔
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f → C.AGP ⊥ f xs → C.IsKKT f xs := by
  open RRAux_StrictCQ_AGP_theorem_4_2 in
  constructor
  · intro hreg f hf hagp
    obtain ⟨x, y, hx, hproj, hyx⟩ := hagp
    have hw : -gradient f xs ∈ outerLimitWithin
        (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          normalCone (C.linSet q.1 ⊥) (q.1 + q.2)) Set.univ (xs, 0) := by
      refine ⟨fun k => (x k, y k - x k), fun k => x k - gradient f (x k) - y k,
        fun _ => trivial, hx.prodMk_nhds hyx, ?_, fun k => ?_⟩
      · have hg := ((grad_cont f hf).tendsto xs).comp hx
        have h2 : Tendsto (fun k => -(y k - x k) - gradient f (x k)) atTop
            (𝓝 (-0 - gradient f xs)) := hyx.neg.sub hg
        rw [neg_zero, zero_sub] at h2
        refine h2.congr fun k => ?_
        abel
      · show _ ∈ normalCone (C.linSet (x k) ⊥) (x k + (y k - x k))
        rw [add_sub_cancel]
        exact ⟨(hproj k).1, proj_VI (linSet_convex C (x k) ⊥) (hproj k)⟩
    have hN := hreg hw
    exact kkt_of_polar C xs f (fun d hd1 hd2 => polar_of_normal C xs hxs _ hN d hd1 hd2)
  · intro H w hw
    obtain ⟨z, v, -, hz, hv, hvN⟩ := hw
    have hS : ∀ k, (C.linSet (z k).1 ⊥).Nonempty := fun k => ⟨_, (hvN k).1⟩
    choose y hy using fun k => proj_exists (linSet_closed C (z k).1 ⊥) (linSet_convex C _ _) (hS k)
      ((z k).1 - gradient (fun z : EuclideanSpace ℝ (Fin n) => ⟪-w, z⟫_ℝ) (z k).1)
    have hz1 : Tendsto (fun k => (z k).1) atTop (𝓝 xs) := (continuous_fst.tendsto _).comp hz
    have hz2 : Tendsto (fun k => (z k).2) atTop (𝓝 0) := (continuous_snd.tendsto _).comp hz
    have hbound : ∀ k, ‖y k - ((z k).1 + (z k).2)‖ ≤ ‖w - (z k).2 - v k‖ := by
      intro k
      have h := nonexp (linSet_convex C (z k).1 ⊥) (hy k) (hvN k).1
        (z2 := (z k).1 + (z k).2 + v k) (by rw [add_sub_cancel_left]; exact (hvN k).2)
      rw [lin_grad] at h
      refine h.trans (le_of_eq ?_)
      congr 1
      abel
    have hlim0 : Tendsto (fun k => w - (z k).2 - v k) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := w)).sub hz2 |>.sub hv
      simpa using this
    have hd : Tendsto (fun k => y k - ((z k).1 + (z k).2)) atTop (𝓝 0) :=
      squeeze_zero_norm hbound (by simpa using hlim0.norm)
    have hK := H (fun z : EuclideanSpace ℝ (Fin n) => ⟪-w, z⟫_ℝ) (lin_C1 _)
      ⟨fun k => (z k).1, y, hz1, hy, ?_⟩
    · exact normal_of_kkt C xs hxs w hK
    · have := hd.add hz2
      rw [add_zero] at this
      refine this.congr fun k => ?_
      abel

#print axioms solution
