-- Prove2me | solution 1 for StrictCQ.SAKKT.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:21:22.260347+00:00
-- url     : https://prove2.me/submissions/204ae593-a8a5-43cf-8d0a-c3eace5052dd

import Mathlib
import Definitions.Def_StrictCQ_SAKKT_Conditions

open Filter Topology InnerProductSpace

namespace RRAux_StrictCQ_SAKKT_theorem_4_5

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

open StrictCQ.SAKKT

abbrev EE (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma lin_grad {n : ℕ} (c z : EE n) : gradient (fun z : EE n => ⟪c, z⟫_ℝ) z = c := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  exact (InnerProductSpace.toDual ℝ (EE n) c).hasFDerivAt

lemma lin_C1 {n : ℕ} (c : EE n) : ContDiff ℝ 1 (fun z : EE n => ⟪c, z⟫_ℝ) :=
  (InnerProductSpace.toDual ℝ (EE n) c).contDiff

lemma grad_cont {n : ℕ} (f : EE n → ℝ) (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  show Continuous fun x => (InnerProductSpace.toDual ℝ (EE n)).symm (fderiv ℝ f x)
  exact (LinearIsometryEquiv.continuous _).comp (hf.continuous_fderiv one_ne_zero)

lemma normal_iff_comb {n m p : ℕ} (C : Constraints n m p) (x w : EE n) :
    w ∈ StrictCQ.AGP.normalCone (C.linSet x 0) x ↔
      ∃ (a : Fin m → ℝ) (b : Fin p → ℝ), (∀ j, 0 ≤ b j) ∧ (∀ j, C.g j x < 0 → b j = 0) ∧
        w = ∑ i, a i • gradient (C.h i) x + ∑ j, b j • gradient (C.g j) x := by
  classical
  constructor
  · rintro ⟨-, hw⟩
    set u : (Fin m ⊕ Fin m) ⊕ Fin p → EE n :=
      Sum.elim (Sum.elim (fun i => gradient (C.h i) x) (fun i => -gradient (C.h i) x))
        (fun j => if 0 ≤ C.g j x then gradient (C.g j) x else 0) with hu
    obtain ⟨c, hc0, hc⟩ := farkas u w (fun d hd => by
      have hmem : x + d ∈ C.linSet x 0 := by
        refine ⟨fun i => ?_, fun j hj => ?_, fun j hj1 hj2 => ?_⟩
        · rw [add_sub_cancel_left]
          refine le_antisymm (by simpa only [hu, Sum.elim_inl] using hd (Sum.inl (Sum.inl i))) ?_
          have := hd (Sum.inl (Sum.inr i))
          simp only [hu, Sum.elim_inl, Sum.elim_inr, inner_neg_left] at this
          linarith
        · rw [add_sub_cancel_left]
          have := hd (Sum.inr j)
          simpa only [hu, Sum.elim_inr, hj, if_true] using this
        · exact absurd (EReal.coe_pos.1 hj1) (not_lt.2 hj2.le)
      have := hw _ hmem
      rwa [add_sub_cancel_left] at this)
    refine ⟨fun i => c (Sum.inl (Sum.inl i)) - c (Sum.inl (Sum.inr i)),
      fun j => if 0 ≤ C.g j x then c (Sum.inr j) else 0, fun j => ?_, fun j hj => ?_, ?_⟩
    · show 0 ≤ (if 0 ≤ C.g j x then c (Sum.inr j) else 0)
      split_ifs
      · exact hc0 _
      · exact le_rfl
    · show (if 0 ≤ C.g j x then c (Sum.inr j) else 0) = 0
      rw [if_neg (not_le.2 hj)]
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hc
      simp only [hu, Sum.elim_inl, Sum.elim_inr] at hc
      rw [hc]
      have e2 : ∑ j, (if 0 ≤ C.g j x then c (Sum.inr j) else 0) • gradient (C.g j) x
          = ∑ j, c (Sum.inr j) • (if 0 ≤ C.g j x then gradient (C.g j) x else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> simp
      rw [e2]
      simp only [sub_eq_add_neg, add_smul, neg_smul, Finset.sum_add_distrib,
        Finset.sum_neg_distrib, smul_neg]
  · rintro ⟨a, b, hb0, hbc, rfl⟩
    refine ⟨⟨fun i => by simp, fun j _ => by simp, fun j hj1 hj2 => ?_⟩, fun z hz => ?_⟩
    · exact absurd (EReal.coe_pos.1 hj1) (not_lt.2 hj2.le)
    rw [inner_add_left, sum_inner, sum_inner]
    simp only [real_inner_smul_left, hz.1, mul_zero, Finset.sum_const_zero, zero_add]
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : 0 ≤ C.g j x
    · exact mul_nonpos_of_nonneg_of_nonpos (hb0 j) (hz.2.1 j hj)
    · rw [hbc j (not_le.1 hj), zero_mul]

end RRAux_StrictCQ_SAKKT_theorem_4_5

open StrictCQ.SAKKT in
theorem solution {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    C.SAKKTRegular xs ↔
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 f → C.SAKKT f xs → C.IsKKT f xs := by
  open RRAux_StrictCQ_SAKKT_theorem_4_5 in
  constructor
  · intro hreg f hf hS
    obtain ⟨x, lam, mu, hx, hmu0, hmuc, hres⟩ := hS
    have hw : -gradient f xs ∈ StrictCQ.AGP.outerLimitWithin
        (fun x => StrictCQ.AGP.normalCone (C.linSet x 0) x) Set.univ xs := by
      refine ⟨x, fun k => ∑ i, lam k i • gradient (C.h i) (x k) +
        ∑ j, mu k j • gradient (C.g j) (x k), fun _ => trivial, hx, ?_, fun k => ?_⟩
      · have hg := ((grad_cont f hf).tendsto xs).comp hx
        have h2 := hres.sub hg
        rw [zero_sub] at h2
        refine h2.congr fun k => ?_
        simp only [Function.comp_apply]
        abel
      · exact (normal_iff_comb C (x k) _).2 ⟨lam k, mu k, hmu0 k, hmuc k, rfl⟩
    obtain ⟨a, b, hb0, hbc, heq⟩ := (normal_iff_comb C xs _).1 (hreg hw)
    refine ⟨a, b, hb0, fun j hj => hbc j (lt_of_le_of_ne (hxs.2 j) hj), ?_⟩
    rw [add_assoc, ← heq, add_neg_cancel]
  · intro H w hw
    obtain ⟨z, v, -, hz, hv, hvN⟩ := hw
    choose a b hb0 hbc hveq using fun k => (normal_iff_comb C (z k) (v k)).1 (hvN k)
    have hK := H (fun y : EuclideanSpace ℝ (Fin n) => ⟪-w, y⟫_ℝ) (lin_C1 _)
      ⟨z, a, b, hz, hb0, hbc, ?_⟩
    · obtain ⟨lam, mu, h0, hc, heq⟩ := hK
      rw [lin_grad, add_assoc, neg_add_eq_zero] at heq
      exact (normal_iff_comb C xs w).2 ⟨lam, mu, h0, fun j hj => hc j hj.ne, heq⟩
    · have h2 := (tendsto_const_nhds (x := -w)).add hv
      rw [neg_add_cancel] at h2
      refine h2.congr fun k => ?_
      rw [lin_grad, add_assoc, ← hveq k]

#print axioms solution
