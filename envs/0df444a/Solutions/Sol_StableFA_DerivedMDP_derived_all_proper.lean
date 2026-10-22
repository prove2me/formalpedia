-- Prove2me | solution 1 for StableFA.DerivedMDP.derived_all_proper
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:26:42.404664+00:00
-- url     : https://prove2.me/submissions/afa2b2d4-466d-4814-89d0-8b277611db5a

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting



namespace StableFA.DerivedMDP

open Filter Topology

variable {n : ℕ} {C : Type} [Fintype C]

lemma h53_surv_bounds (N : BertsekasSSPModel n C) :
    ∀ (m : ℕ) (π : ℕ → Fin n → C), BertsekasSSPAdmissible N π →
      ∀ i, 0 ≤ BertsekasSSPSurvival N π m i ∧ BertsekasSSPSurvival N π m i ≤ 1 := by
  intro m
  induction m with
  | zero => intro π _ i; simp [BertsekasSSPSurvival]
  | succ m ih =>
    intro π hπ i
    have hπ' : BertsekasSSPAdmissible N (fun k => π (k+1)) := fun k i => hπ (k+1) i
    simp only [BertsekasSSPSurvival]
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (N.hp_nonneg _ _ _) (ih _ hπ' j).1
    · calc ∑ j, N.p i (π 0 i) j * BertsekasSSPSurvival N (fun k => π (k+1)) m j
          ≤ ∑ j, N.p i (π 0 i) j * 1 :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (ih _ hπ' j).2 (N.hp_nonneg _ _ _)
        _ ≤ 1 := by simpa using N.hp_sum i _ (hπ 0 i)

lemma h53_exists_adm (N : BertsekasSSPModel n C) :
    ∃ π : ℕ → Fin n → C, BertsekasSSPAdmissible N π := by
  have : ∀ i, ∃ u, u ∈ N.U i := fun i => N.hU i
  choose μ hμ using this
  exact ⟨fun _ => μ, fun _ i => hμ i⟩

lemma h53_bellman_diff (N : BertsekasSSPModel n C) (J J' : Fin n → ℝ) (d : ℝ)
    (h : ∀ j, J j - J' j ≤ d) :
    ∀ a : ℕ, ∃ π : ℕ → Fin n → C, BertsekasSSPAdmissible N π ∧
      ∀ i, (BertsekasSSPBellmanOp N)^[a] J i - (BertsekasSSPBellmanOp N)^[a] J' i
        ≤ d * BertsekasSSPSurvival N π a i := by
  intro a
  induction a with
  | zero =>
    obtain ⟨π, hπ⟩ := h53_exists_adm N
    exact ⟨π, hπ, fun i => by simpa [BertsekasSSPSurvival] using h i⟩
  | succ a ih =>
    obtain ⟨π', hπ', hb⟩ := ih
    have hex : ∀ i, ∃ u ∈ N.U i, BertsekasSSPBellmanOp N ((BertsekasSSPBellmanOp N)^[a] J') i
        = N.g i u + ∑ j, N.p i u j * (BertsekasSSPBellmanOp N)^[a] J' j := fun i =>
      Finset.exists_mem_eq_inf' (N.hU i) _
    choose μ hμ hμeq using hex
    refine ⟨fun k => match k with | 0 => μ | k+1 => π' k, ?_, ?_⟩
    · intro k i
      cases k with
      | zero => exact hμ i
      | succ k => exact hπ' k i
    · intro i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have h1 : BertsekasSSPBellmanOp N ((BertsekasSSPBellmanOp N)^[a] J) i ≤
          N.g i (μ i) + ∑ j, N.p i (μ i) j * (BertsekasSSPBellmanOp N)^[a] J j :=
        Finset.inf'_le _ (hμ i)
      have h2 := hμeq i
      have h3 : BertsekasSSPSurvival N (fun k => match k with | 0 => μ | k+1 => π' k) (a+1) i
          = ∑ j, N.p i (μ i) j * BertsekasSSPSurvival N π' a j := rfl
      rw [h3]
      have h4 : ∑ j, N.p i (μ i) j * ((BertsekasSSPBellmanOp N)^[a] J j
            - (BertsekasSSPBellmanOp N)^[a] J' j)
          ≤ ∑ j, N.p i (μ i) j * (d * BertsekasSSPSurvival N π' a j) :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hb j) (N.hp_nonneg _ _ _)
      have h5 : ∑ j, N.p i (μ i) j * (d * BertsekasSSPSurvival N π' a j)
          = d * ∑ j, N.p i (μ i) j * BertsekasSSPSurvival N π' a j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      have h6 : ∑ j, N.p i (μ i) j * ((BertsekasSSPBellmanOp N)^[a] J j
            - (BertsekasSSPBellmanOp N)^[a] J' j)
          = ∑ j, N.p i (μ i) j * (BertsekasSSPBellmanOp N)^[a] J j
            - ∑ j, N.p i (μ i) j * (BertsekasSSPBellmanOp N)^[a] J' j := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
      linarith

lemma h53_iter_dist (N : BertsekasSSPModel n C) (a : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ π, BertsekasSSPAdmissible N π → ∀ i, BertsekasSSPSurvival N π a i ≤ ρ)
    (J J' : Fin n → ℝ) :
    dist ((BertsekasSSPBellmanOp N)^[a] J) ((BertsekasSSPBellmanOp N)^[a] J') ≤ ρ * dist J J' := by
  have hd : 0 ≤ dist J J' := dist_nonneg
  have key : ∀ J J' : Fin n → ℝ, ∀ i, (BertsekasSSPBellmanOp N)^[a] J i - (BertsekasSSPBellmanOp N)^[a] J' i
        ≤ ρ * dist J J' := by
    intro J J' i
    have hd : 0 ≤ dist J J' := dist_nonneg
    obtain ⟨π, hπ, hb⟩ := h53_bellman_diff N J J' (dist J J')
      (fun j => (le_abs_self _).trans (by simpa [Real.dist_eq] using dist_le_pi_dist J J' j)) a
    calc _ ≤ _ := hb i
      _ ≤ dist J J' * ρ := mul_le_mul_of_nonneg_left (hρ π hπ i) hd
      _ = _ := by ring
  rw [dist_pi_le_iff (mul_nonneg hρ0 hd)]
  intro i
  rw [Real.dist_eq, abs_le]
  constructor
  · have := key J' J i
    rw [dist_comm J' J] at this
    linarith
  · exact key J J' i

lemma h53_layer_disjoint (M : BertsekasSSPModel n C) {a b : ℕ} (hab : a < b)
    {x : Option (Fin n)} (hb : x ∈ layer M b) : x ∉ layer M a := by
  rcases b with _ | _ | k
  · omega
  · obtain rfl : a = 0 := by omega
    simp [layer]
  · have := ((mem_layer_iff M k x).1 hb).1
    intro ha
    exact this (Set.mem_iUnion₂.2 ⟨a, hab, ha⟩)

lemma h53_layer_unique (M : BertsekasSSPModel n C) {a b : ℕ} {x : Option (Fin n)}
    (ha : x ∈ layer M a) (hb : x ∈ layer M b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd ha (h53_layer_disjoint M h hb)
  · exact h
  · exact absurd hb (h53_layer_disjoint M h ha)

lemma h53_below_mono (M : BertsekasSSPModel n C) : Monotone (below M) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [below_eq_iUnion, below_eq_iUnion]
  intro x hx
  simp only [Set.mem_iUnion, exists_prop] at hx ⊢
  obtain ⟨j, hj, hx⟩ := hx
  exact ⟨j, by omega, hx⟩

lemma h53_exhaustive (M : BertsekasSSPModel n C)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ) :
    ∀ i : Fin n, ∃ k : ℕ, some i ∈ layer M k := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i0, hi0⟩ := hcon
  -- stabilization
  have hwf : WellFoundedGT (Set (Option (Fin n))) := Finite.to_wellFoundedGT
  obtain ⟨N0, hN0⟩ := (wellFoundedGT_iff_monotone_chain_condition.1 hwf)
    ⟨below M, h53_below_mono M⟩
  have hstab : ∀ m, N0 + 2 ≤ m → below M m = below M (N0 + 2) := by
    intro m hm
    have h1 := hN0 m (by omega)
    have h2 := hN0 (N0 + 2) (by omega)
    simp only [OrderHom.coe_mk] at h1 h2
    rw [← h1, ← h2]
  set K := N0 + 2 with hK
  -- everything in some layer lies below K
  have hcover : ∀ x, (∃ k, x ∈ layer M k) → x ∈ below M K := by
    rintro x ⟨k, hk⟩
    have h1 : x ∈ below M (k + 1) := by
      rw [below_eq_iUnion]
      exact Set.mem_iUnion₂.2 ⟨k, by omega, hk⟩
    have h2 : below M (k + 1) ⊆ below M (max (k + 1) K) :=
      h53_below_mono M (le_max_left _ _)
    rw [hstab _ (le_max_right _ _)] at h2
    exact h2 h1
  have hnone : (none : Option (Fin n)) ∈ below M K := by
    rw [below_eq_iUnion]
    exact Set.mem_iUnion₂.2 ⟨1, by omega, by simp [layer]⟩
  -- the bad set R
  have hR : ∀ i, (∀ k, some i ∉ layer M k) → ∃ u ∈ M.U i,
      ∀ y ∈ below M K, ¬ 0 < stepProb M i u y := by
    intro i hi
    by_contra hcon
    push_neg at hcon
    apply hi (N0 + 2)
    refine ⟨?_, i, rfl, hcon⟩
    intro hmem
    rw [below_eq_iUnion] at hmem
    obtain ⟨j, _, hj⟩ := Set.mem_iUnion₂.1 hmem
    exact hi j hj
  have hex : ∀ i, ∃ u ∈ M.U i, ((∀ k, some i ∉ layer M k) →
      ∀ y ∈ below M K, ¬ 0 < stepProb M i u y) := by
    intro i
    by_cases h : ∀ k, some i ∉ layer M k
    · obtain ⟨u, hu, h2⟩ := hR i h
      exact ⟨u, hu, fun _ => h2⟩
    · obtain ⟨u, hu⟩ := M.hU i
      exact ⟨u, hu, fun h' => absurd h' h⟩
  choose μ hμU hμ using hex
  have hsurv : ∀ t, ∀ i, (∀ k, some i ∉ layer M k) →
      BertsekasSSPSurvival M (fun _ => μ) t i = 1 := by
    intro t
    induction t with
    | zero => intro i _; simp [BertsekasSSPSurvival]
    | succ t ih =>
      intro i hi
      have hz : ∀ j, ¬ (∀ k, some j ∉ layer M k) → M.p i (μ i) j = 0 := by
        intro j hj
        push_neg at hj
        have hjb : some j ∈ below M K := hcover _ hj
        have h1 := hμ i hi _ hjb
        have h0 := M.hp_nonneg i (μ i) j
        simp only [stepProb, not_lt] at h1
        linarith
      have hsum : ∑ j, M.p i (μ i) j = 1 := by
        have h1 := hμ i hi none hnone
        simp only [stepProb, not_lt] at h1
        have h2 := M.hp_sum i _ (hμU i)
        linarith
      show ∑ j, M.p i (μ i) j * BertsekasSSPSurvival M (fun _ => μ) t j = 1
      calc _ = ∑ j, M.p i (μ i) j := Finset.sum_congr rfl fun j _ => by
            by_cases hj : ∀ k, some j ∉ layer M k
            · rw [ih j hj, mul_one]
            · rw [hz j hj, zero_mul]
        _ = 1 := hsum
  have hp := hproper μ hμU i0
  have h1 : Tendsto (fun t => BertsekasSSPSurvival M (fun _ => μ) t i0) atTop (𝓝 1) := by
    simp only [hsurv _ i0 hi0]; exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique h1 hp)

lemma h53_exists_eps {ι : Type} [Finite ι] (f : ι → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ i, 0 < f i → ε ≤ f i := by
  classical
  haveI := Fintype.ofFinite ι
  by_cases h : (Finset.univ.filter (fun i => 0 < f i)).Nonempty
  · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ f h
    refine ⟨min 1 (f i0), lt_min one_pos (Finset.mem_filter.1 hi0).2, min_le_left _ _,
      fun i hi => ?_⟩
    exact (min_le_right _ _).trans (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩))
  · exact ⟨1, one_pos, le_rfl, fun i hi =>
      absurd ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩ h⟩

lemma h53_term_mass (M : BertsekasSSPModel n C) (A : Averager n) (x : Fin n) (u : C) :
    stepProb (derivedModel M A 1) x u none =
      (1 - ∑ y, M.p x u y) + ∑ y, M.p x u y * (A.βc y + A.β y none) := by
  simp only [stepProb, derivedModel]
  have h1 : ∀ y, ∑ z : Fin n, A.β y (some z) = 1 - A.βc y - A.β y none := by
    intro y; have h := A.sum_eq_one y; rw [Fintype.sum_option] at h; linarith
  have e : ∑ z, ∑ y, M.p x u y * A.β y (some z)
      = ∑ y, M.p x u y * (1 - A.βc y - A.β y none) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, h1]
  rw [e]
  have e2 : ∑ y, M.p x u y * (1 - A.βc y - A.β y none)
      = ∑ y, M.p x u y - ∑ y, M.p x u y * (A.βc y + A.β y none) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun y _ => by ring
  linarith

lemma h53_dichotomy (M : BertsekasSSPModel n C) (A : Averager n) (hself : SelfWeighted M A)
    {k : ℕ} {x : Fin n} (hx : some x ∈ layer M (k + 2)) {u : C} (hu : u ∈ M.U x) :
    0 < stepProb (derivedModel M A 1) x u none ∨
      ∃ z, 0 < (derivedModel M A 1).p x u z ∧ ∃ k', k' < k + 2 ∧ some z ∈ layer M k' := by
  obtain ⟨_, i, hi, hall⟩ := (mem_layer_iff M k (some x)).1 hx
  obtain rfl : x = i := Option.some_injective _ hi
  obtain ⟨y, hy, hpos⟩ := hall u hu
  obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.1 hy
  have hsum := M.hp_sum x u hu
  have hnn : ∀ y, 0 ≤ M.p x u y * (A.βc y + A.β y none) := fun y =>
    mul_nonneg (M.hp_nonneg _ _ _) (add_nonneg (A.βc_nonneg y) (A.β_nonneg y none))
  have hterm : ∀ y, 0 < M.p x u y * (A.βc y + A.β y none) →
      0 < stepProb (derivedModel M A 1) x u none := by
    intro y hy
    rw [h53_term_mass]
    have := Finset.single_le_sum (fun y _ => hnn y) (Finset.mem_univ y)
    linarith
  cases y with
  | none =>
    left
    rw [h53_term_mass]
    simp only [stepProb] at hpos
    have := Finset.sum_nonneg (fun y (_ : y ∈ Finset.univ) => hnn y)
    linarith
  | some y' =>
    simp only [stepProb] at hpos
    rcases hself y' with hb | ⟨x', hβ, kx, ky, hkx, hky, hle⟩
    · left; exact hterm y' (mul_pos hpos (by linarith [A.β_nonneg y' none]))
    · have : ky = j := h53_layer_unique M hky hyj
      subst this
      cases x' with
      | none => left; exact hterm y' (mul_pos hpos (by linarith [A.βc_nonneg y']))
      | some z =>
        right
        refine ⟨z, ?_, kx, by omega, hkx⟩
        show 0 < ∑ y, M.p x u y * A.β y (some z)
        have h1 := Finset.single_le_sum
          (f := fun y => M.p x u y * A.β y (some z))
          (fun y _ => mul_nonneg (M.hp_nonneg _ _ _) (A.β_nonneg _ _)) (Finset.mem_univ y')
        have h2 := mul_pos hpos hβ
        linarith

lemma h53_main_bound_gen (N : BertsekasSSPModel n C) (L : ℕ → Set (Option (Fin n)))
    (hL0 : ∀ z, some z ∉ L 0) (hL1 : ∀ z, some z ∉ L 1)
    (hdich : ∀ (k : ℕ) (x : Fin n), some x ∈ L (k + 2) → ∀ u ∈ N.U x,
      0 < stepProb N x u none ∨
        ∃ z, 0 < N.p x u z ∧ ∃ k', k' < k + 2 ∧ some z ∈ L k')
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεp : ∀ x u y, 0 < stepProb N x u y → ε ≤ stepProb N x u y) :
    ∀ k : ℕ, ∀ x : Fin n, some x ∈ L (k + 2) → ∀ π, BertsekasSSPAdmissible N π →
      ∀ m, k + 1 ≤ m → BertsekasSSPSurvival N π m x ≤ 1 - ε ^ (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hx π hπ m hm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hπ' : BertsekasSSPAdmissible N (fun k => π (k+1)) := fun k i => hπ (k+1) i
  have hu : π 0 x ∈ N.U x := hπ 0 x
  have hq0 : ∀ j, 0 ≤ N.p x (π 0 x) j := fun j => N.hp_nonneg _ _ _
  have hsum : ∑ j, N.p x (π 0 x) j ≤ 1 := N.hp_sum x _ hu
  have hs := h53_surv_bounds N m' (fun k => π (k+1)) hπ'
  have hεk : ε ^ (k + 1) ≤ ε := pow_le_of_le_one hε0.le hε1 (Nat.succ_ne_zero k)
  show ∑ j, N.p x (π 0 x) j * BertsekasSSPSurvival N (fun k => π (k+1)) m' j ≤ _
  rcases hdich k x hx _ hu with hterm | ⟨z, hz, k', hk', hzl⟩
  · have h1 : ε ≤ 1 - ∑ j, N.p x (π 0 x) j := by
      have := hεp x (π 0 x) none hterm
      simpa [stepProb] using this
    calc _ ≤ ∑ j, N.p x (π 0 x) j * 1 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hs j).2 (hq0 j)
      _ ≤ 1 - ε ^ (k + 1) := by simp only [mul_one]; linarith
  · obtain ⟨k1, rfl⟩ : ∃ k1, k' = k1 + 2 := by
      rcases k' with _ | _ | k1
      · exact absurd hzl (hL0 z)
      · exact absurd hzl (hL1 z)
      · exact ⟨k1, rfl⟩
    have hk1 : k1 < k := by omega
    have IH := ih k1 hk1 z hzl (fun k => π (k+1)) hπ' m' (by omega)
    have hqz : ε ≤ N.p x (π 0 x) z := hεp x (π 0 x) (some z) hz
    have hpow : ε ^ k ≤ ε ^ (k1 + 1) := pow_le_pow_of_le_one hε0.le hε1 (by omega)
    have h1 : ε * ε ^ k ≤ N.p x (π 0 x) z * (1 - BertsekasSSPSurvival N (fun k => π (k+1)) m' z) :=
      mul_le_mul hqz (by linarith) (pow_nonneg hε0.le _) (hq0 z)
    have h2 : N.p x (π 0 x) z * (1 - BertsekasSSPSurvival N (fun k => π (k+1)) m' z)
        ≤ ∑ j, N.p x (π 0 x) j * (1 - BertsekasSSPSurvival N (fun k => π (k+1)) m' j) :=
      Finset.single_le_sum (f := fun j => N.p x (π 0 x) j *
          (1 - BertsekasSSPSurvival N (fun k => π (k+1)) m' j))
        (fun j _ => mul_nonneg (hq0 j) (by linarith [(hs j).2])) (Finset.mem_univ z)
    have h3 : ∑ j, N.p x (π 0 x) j * BertsekasSSPSurvival N (fun k => π (k+1)) m' j
        = ∑ j, N.p x (π 0 x) j
          - ∑ j, N.p x (π 0 x) j * (1 - BertsekasSSPSurvival N (fun k => π (k+1)) m' j) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
    have h4 : ε ^ (k + 1) = ε * ε ^ k := pow_succ' ε k
    linarith

lemma h53_unif_bound (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    ∃ m : ℕ, 0 < m ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ π, BertsekasSSPAdmissible (derivedModel M A 1) π →
        ∀ i, BertsekasSSPSurvival (derivedModel M A 1) π m i ≤ ρ := by
  obtain ⟨ε, hε0, hε1, hεp⟩ := h53_exists_eps
    (fun t : Fin n × C × Option (Fin n) => stepProb (derivedModel M A 1) t.1 t.2.1 t.2.2)
  have hex := h53_exhaustive M hproper
  have hex2 : ∀ i, ∃ k0, some i ∈ layer M (k0 + 2) := by
    intro i
    obtain ⟨k, hk⟩ := hex i
    rcases k with _ | _ | k0
    · simp [layer] at hk
    · simp [layer] at hk
    · exact ⟨k0, hk⟩
  choose k0 hk0 using hex2
  have hmain := h53_main_bound_gen (derivedModel M A 1) (layer M)
    (fun z => by simp [layer]) (fun z => by simp [layer])
    (fun k x hx u hu => h53_dichotomy M A hself hx hu) ε hε0 hε1
    (fun x u y h => hεp (x, u, y) h)
  set K := Finset.univ.sup k0 with hK
  have hpowK : ε ^ (K + 1) ≤ 1 := pow_le_one₀ hε0.le hε1
  refine ⟨K + 1, by omega, 1 - ε ^ (K + 1), by linarith, ?_, ?_⟩
  · have := pow_pos hε0 (K + 1); linarith
  · intro π hπ i
    have h1 := hmain (k0 i) i (hk0 i) π hπ (K + 1)
      (by have := Finset.le_sup (f := k0) (Finset.mem_univ i); omega)
    have h2 : ε ^ (K + 1) ≤ ε ^ (k0 i + 1) :=
      pow_le_pow_of_le_one hε0.le hε1
        (by have := Finset.le_sup (f := k0) (Finset.mem_univ i); omega)
    linarith

lemma h53_stat_proper (N : BertsekasSSPModel n C) (m : ℕ) (hm : 0 < m) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hb : ∀ π, BertsekasSSPAdmissible N π → ∀ i, BertsekasSSPSurvival N π m i ≤ ρ)
    (μ : Fin n → C) (hμ : ∀ i, μ i ∈ N.U i) :
    ∀ i, Tendsto (fun t => BertsekasSSPSurvival N (fun _ => μ) t i) atTop (𝓝 0) := by
  set W : (Fin n → ℝ) → (Fin n → ℝ) := fun v i => ∑ j, N.p i (μ i) j * v j with hW
  have hadm : BertsekasSSPAdmissible N (fun _ => μ) := fun _ i => hμ i
  have hS : ∀ t, (fun i => BertsekasSSPSurvival N (fun _ => μ) t i) = W^[t] (fun _ => 1) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', ← ih]
      rfl
  have hmono : ∀ v w : Fin n → ℝ, v ≤ w → W v ≤ W w := by
    intro v w h i
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h j) (N.hp_nonneg _ _ _)
  have hmonoit : ∀ (a : ℕ) (v w : Fin n → ℝ), v ≤ w → W^[a] v ≤ W^[a] w := by
    intro a
    induction a with
    | zero => intro v w h; exact h
    | succ a ih =>
      intro v w h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hmono _ _ (ih v w h)
  have hWc : ∀ (c : ℝ) (v : Fin n → ℝ), W (fun j => c * v j) = fun i => c * W v i := by
    intro c v
    funext i
    simp only [hW, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hhom : ∀ (a : ℕ) (c : ℝ) (v : Fin n → ℝ),
      W^[a] (fun j => c * v j) = fun i => c * W^[a] v i := by
    intro a
    induction a with
    | zero => intro c v; rfl
    | succ a ih =>
      intro c v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hWc]
  have hA : ∀ k : ℕ, (W^[m])^[k] (fun _ => 1) ≤ fun _ => ρ ^ k := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h1 : W^[m] ((W^[m])^[k] (fun _ => (1:ℝ))) ≤ W^[m] (fun j => ρ ^ k * 1) :=
        hmonoit m _ _ (fun j => by simpa using ih j)
      rw [hhom] at h1
      intro i
      have h2 : W^[m] (fun _ => (1:ℝ)) i ≤ ρ := by
        have := hb _ hadm i
        rw [← congrFun (hS m) i] at *
        simpa using this
      calc _ ≤ ρ ^ k * W^[m] (fun _ => (1:ℝ)) i := h1 i
        _ ≤ ρ ^ k * ρ := mul_le_mul_of_nonneg_left h2 (pow_nonneg hρ0 _)
        _ = ρ ^ (k + 1) := by ring
  have hB : ∀ t, (fun i => BertsekasSSPSurvival N (fun _ => μ) (t + 1) i)
      ≤ fun i => BertsekasSSPSurvival N (fun _ => μ) t i := by
    intro t
    induction t with
    | zero =>
      intro i
      have := (h53_surv_bounds N 1 (fun _ => μ) hadm i).2
      simpa [BertsekasSSPSurvival] using this
    | succ t ih =>
      intro i
      show ∑ j, N.p i (μ i) j * BertsekasSSPSurvival N (fun _ => μ) (t + 1) j
        ≤ ∑ j, N.p i (μ i) j * BertsekasSSPSurvival N (fun _ => μ) t j
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (ih j) (N.hp_nonneg _ _ _)
  have hanti : ∀ i, Antitone (fun t => BertsekasSSPSurvival N (fun _ => μ) t i) := fun i =>
    antitone_nat_of_succ_le fun t => hB t i
  intro i
  have hlim : Tendsto (fun t : ℕ => ρ ^ (t / m)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
      (Nat.tendsto_div_const_atTop hm.ne')
  refine squeeze_zero (fun t => (h53_surv_bounds N t _ hadm i).1) (fun t => ?_) hlim
  have h1 : BertsekasSSPSurvival N (fun _ => μ) t i
      ≤ BertsekasSSPSurvival N (fun _ => μ) (m * (t / m)) i :=
    hanti i (Nat.mul_div_le t m)
  have h2 : BertsekasSSPSurvival N (fun _ => μ) (m * (t / m)) i ≤ ρ ^ (t / m) := by
    have := hA (t / m) i
    rw [← Function.iterate_mul, ← congrFun (hS (m * (t / m))) i] at this
    exact this
  exact h1.trans h2

lemma h53_iter_conv (T : (Fin n → ℝ) → (Fin n → ℝ)) (m : ℕ) (hm : 0 < m) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hnon : ∀ r J J', dist (T^[r] J) (T^[r] J') ≤ dist J J')
    (hcon : ∀ J J', dist (T^[m] J) (T^[m] J') ≤ ρ * dist J J') :
    ∀ x, ∃ x', Tendsto (fun k => T^[k] x) atTop (𝓝 x') := by
  intro x
  let K : NNReal := ⟨ρ, hρ0⟩
  have hf : ContractingWith K (T^[m]) :=
    ⟨by rw [← NNReal.coe_lt_coe]; exact hρ1,
      LipschitzWith.of_dist_le_mul fun a b => hcon a b⟩
  set x' := ContractingWith.fixedPoint (T^[m]) hf with hx'
  have hfix : Function.IsFixedPt (T^[m]) x' := ContractingWith.fixedPoint_isFixedPt hf
  have hfix2 : Function.IsFixedPt (T^[m]) (T x') := by
    unfold Function.IsFixedPt
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hfix.eq]
  have hTx : T x' = x' := hf.fixedPoint_unique' hfix2 hfix
  have hTr : ∀ r, T^[r] x' = x' := fun r => Function.iterate_fixed hTx r
  have hgeo : ∀ (q : ℕ) (a b : Fin n → ℝ),
      dist ((T^[m])^[q] a) ((T^[m])^[q] b) ≤ ρ ^ q * dist a b := by
    intro q
    induction q with
    | zero => intro a b; simp
    | succ q ih =>
      intro a b
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc _ ≤ ρ * dist ((T^[m])^[q] a) ((T^[m])^[q] b) := hcon _ _
        _ ≤ ρ * (ρ ^ q * dist a b) := mul_le_mul_of_nonneg_left (ih a b) hρ0
        _ = _ := by ring
  refine ⟨x', ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun t : ℕ => ρ ^ (t / m) * dist x x') atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
      (Nat.tendsto_div_const_atTop hm.ne')).mul_const (dist x x')
    simpa using this
  refine squeeze_zero (fun t => dist_nonneg) (fun t => ?_) hlim
  have hk : t = m * (t / m) + t % m := (Nat.div_add_mod t m).symm
  have e : T^[t] x = (T^[m])^[t / m] (T^[t % m] x) := by
    conv_lhs => rw [hk]
    rw [Function.iterate_add_apply, Function.iterate_mul]
  have e2 : x' = (T^[m])^[t / m] (T^[t % m] x') := by
    rw [hTr, Function.iterate_fixed hfix.eq]
  calc dist (T^[t] x) x' = dist ((T^[m])^[t / m] (T^[t % m] x))
        ((T^[m])^[t / m] (T^[t % m] x')) := by rw [← e2, ← e]
    _ ≤ ρ ^ (t / m) * dist (T^[t % m] x) (T^[t % m] x') := hgeo _ _ _
    _ ≤ ρ ^ (t / m) * dist x x' :=
        mul_le_mul_of_nonneg_left (hnon _ _ _) (pow_nonneg hρ0 _)

lemma h53_bellman_derived (M : BertsekasSSPModel n C) (A : Averager n) :
    BertsekasSSPBellmanOp (derivedModel M A 1) = BertsekasSSPBellmanOp M ∘ A.apply := by
  funext J i
  simp only [BertsekasSSPBellmanOp, Function.comp]
  refine Finset.inf'_congr _ rfl fun u _ => ?_
  simp only [derivedModel, Averager.apply]
  have e1 : ∑ z, (∑ y, M.p i u y * A.β y (some z)) * J z
      = ∑ y, M.p i u y * ∑ z, A.β y (some z) * J z := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring
  have e2 : ∑ y, M.p i u y * (A.βc y * A.k y + ∑ z, A.β y (some z) * J z)
      = ∑ y, M.p i u y * A.βc y * A.k y + ∑ y, M.p i u y * ∑ z, A.β y (some z) * J z := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [e1, e2]; ring

lemma h53_apply_continuous (A : Averager n) : Continuous A.apply := by
  unfold Averager.apply
  fun_prop

lemma h53_iterate_swap {α : Type*} (f g : α → α) :
    ∀ (k : ℕ) (x : α), (f ∘ g)^[k + 1] x = f ((g ∘ f)^[k] (g x)) := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply, ih]
    rfl

lemma h53_value_iteration (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    ∀ x : Fin n → ℝ, ∃ x', Tendsto (fun k => (BertsekasSSPBellmanOp (derivedModel M A 1))^[k] x)
      atTop (𝓝 x') := by
  obtain ⟨m, hm, ρ, hρ0, hρ1, hb⟩ := h53_unif_bound M A hproper hself
  refine h53_iter_conv _ m hm ρ hρ0 hρ1 ?_ ?_
  · intro r J J'
    have := h53_iter_dist (derivedModel M A 1) r 1 zero_le_one
      (fun π hπ i => (h53_surv_bounds _ r π hπ i).2) J J'
    simpa using this
  · intro J J'
    exact h53_iter_dist (derivedModel M A 1) m ρ hρ0 hb J J'

theorem H53_corollary_core {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    StableFA.Discounted.Compatible A.apply (BertsekasSSPBellmanOp M) ∧
      StableFA.Discounted.Compatible (BertsekasSSPBellmanOp M) A.apply := by
  have hvi := h53_value_iteration M A hproper hself
  have hT := h53_bellman_derived M A
  constructor
  · intro x0
    obtain ⟨x', hx'⟩ := hvi (BertsekasSSPBellmanOp M x0)
    refine ⟨A.apply x', ?_⟩
    rw [hT] at hx'
    have h1 : Tendsto (fun k => A.apply ((BertsekasSSPBellmanOp M ∘ A.apply)^[k]
        (BertsekasSSPBellmanOp M x0))) atTop (𝓝 (A.apply x')) :=
      ((h53_apply_continuous A).tendsto x').comp hx'
    rw [← tendsto_add_atTop_iff_nat 1]
    refine h1.congr fun k => ?_
    rw [h53_iterate_swap]
  · intro x0
    obtain ⟨x', hx'⟩ := hvi x0
    rw [hT] at hx'
    exact ⟨x', hx'⟩

theorem H53_proper_core {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    (∃ m : ℕ, 0 < m ∧ ∀ π : ℕ → Fin n → C, BertsekasSSPAdmissible (derivedModel M A 1) π →
        ∀ i, BertsekasSSPSurvival (derivedModel M A 1) π m i < 1) ∧
      ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper (derivedModel M A 1) μ := by
  obtain ⟨m, hm, ρ, hρ0, hρ1, hb⟩ := h53_unif_bound M A hproper hself
  exact ⟨⟨m, hm, fun π hπ i => lt_of_le_of_lt (hb π hπ i) hρ1⟩,
    fun μ hμ => h53_stat_proper (derivedModel M A 1) m hm ρ hρ0 hρ1 hb μ hμ⟩

end StableFA.DerivedMDP

open StableFA.DerivedMDP


theorem solution {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C) (A : Averager n)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ)
    (hself : SelfWeighted M A) :
    (∃ m : ℕ, 0 < m ∧ ∀ π : ℕ → Fin n → C, BertsekasSSPAdmissible (derivedModel M A 1) π →
        ∀ i, BertsekasSSPSurvival (derivedModel M A 1) π m i < 1) ∧
      ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper (derivedModel M A 1) μ := by
  exact H53_proper_core M A hproper hself
