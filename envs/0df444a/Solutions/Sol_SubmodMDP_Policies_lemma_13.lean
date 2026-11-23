-- Prove2me | solution 1 for SubmodMDP.Policies.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:49:38.305798+00:00
-- url     : https://prove2.me/submissions/debdbab1-bafd-4510-9793-2bd1c37c0e12

import Definitions.Def_SubmodMDP_Policies_GraphMDP

open SubmodMDP.Policies

namespace Lemma13Aux

noncomputable def condSet {N : ℕ} (x : Finset (Fin N) → ℝ) (I : Finset (Fin N)) :
    Finset (Fin N) → ℝ :=
  fun J => x (J ∪ I) / x I

lemma condSet_empty (G : LGraph) (r : ℕ) (x : Finset (Fin G.N) → ℝ) (hx : InQ G r x) :
    condSet x ∅ = x := by
  funext J
  simp [condSet, hx.2.2.2.1]

lemma cond_condSet {N : ℕ} (x : Finset (Fin N) → ℝ) (I : Finset (Fin N)) (u : Fin N)
    (hxI : x I ≠ 0) :
    SubmodMDP.Policies.cond (condSet x I) u = condSet x (insert u I) := by
  funext J
  simp only [SubmodMDP.Policies.cond, condSet]
  rw [div_div_div_cancel_right₀ hxI]
  have h1 : insert u J ∪ I = J ∪ insert u I := by
    ext v
    simp
  have h2 : ({u} : Finset (Fin N)) ∪ I = insert u I := Finset.singleton_union u I
  rw [h1, h2]

lemma inQ_condSet (G : LGraph) (r h : ℕ) (hhr : h ≤ r) (x : Finset (Fin G.N) → ℝ)
    (hx : InQ G r x) (I : Finset (Fin G.N)) (hI : I.card ≤ r - h) (hxI : 0 < x I) :
    InQ G h (condSet x I) := by
  rcases hx with ⟨h1, h2, h3, _, h5⟩
  have hcard : ∀ J : Finset (Fin G.N), J.card ≤ h → (J ∪ I).card ≤ r := by
    intro J hJ
    have := Finset.card_union_le J I
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi2 u v hu hv harc J hJ
    simp only [condSet, Finset.insert_union]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (h1 i hi1 hi2 u v hu hv harc (J ∪ I) (hcard J hJ)) hxI.le
  · intro i hi1 hi2 J hJ
    simp only [condSet, Finset.insert_union, ← Finset.sum_div]
    rw [h2 i hi1 hi2 (J ∪ I) (hcard J hJ)]
  · intro v J hJ
    simp only [condSet, Finset.insert_union]
    exact div_le_div_of_nonneg_right (h3 v (J ∪ I) (hcard J hJ)) hxI.le
  · simp [condSet, div_self hxI.ne']
  · intro J hJ
    simp only [condSet]
    have hJI : (J ∪ I).card ≤ r + 1 := by
      have := Finset.card_union_le J I
      omega
    exact div_nonneg (h5 (J ∪ I) hJI) hxI.le

lemma mem_alg4K_pos_le (d ℓ i : ℕ) (hi : i ∈ alg4K d ℓ) : 1 ≤ i ∧ i ≤ ℓ := by
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hi
  rcases hi with ⟨hi0, j, _, rfl⟩
  exact ⟨Nat.pos_of_ne_zero hi0, Nat.div_mul_le_self ℓ (d ^ j)⟩

lemma alg4K_subset_Ico (d r h off : ℕ) (hd : 2 ≤ d) (hdvd : d ^ h ∣ off)
    (hoff : off + d ^ h ≤ d ^ r) :
    alg4K d off ⊆ (Finset.Ico h r).image (fun j => (off / d ^ j) * d ^ j) := by
  intro m hm
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hm
  rcases hm with ⟨hm0, j, _, rfl⟩
  have hoff_pos : 0 < off := by
    by_contra h0
    have : off = 0 := by omega
    simp [this] at hm0
  have hd_le_off : d ^ h ≤ off := Nat.le_of_dvd hoff_pos hdvd
  have h_lt_r : h < r := by
    by_contra hge
    have hr_le : r ≤ h := Nat.le_of_not_lt hge
    have hpow : d ^ r ≤ d ^ h := Nat.pow_le_pow_right (by omega) hr_le
    have hdh_pos : 1 ≤ d ^ h := Nat.one_le_pow h d (by omega)
    omega
  simp only [Finset.mem_image, Finset.mem_Ico]
  by_cases hjh : j < h
  · refine ⟨h, ⟨le_refl h, h_lt_r⟩, ?_⟩
    have hdvd_j : d ^ j ∣ off := dvd_trans (Nat.pow_dvd_pow d hjh.le) hdvd
    rw [Nat.div_mul_cancel hdvd, Nat.div_mul_cancel hdvd_j]
  · refine ⟨j, ⟨Nat.le_of_not_lt hjh, ?_⟩, rfl⟩
    by_contra hjr
    have hr_le_j : r ≤ j := Nat.le_of_not_lt hjr
    have hpow : d ^ r ≤ d ^ j := Nat.pow_le_pow_right (by omega) hr_le_j
    have hdh_pos : 1 ≤ d ^ h := Nat.one_le_pow h d (by omega)
    have hdiv0 : off / d ^ j = 0 := Nat.div_eq_of_lt (by omega)
    simp [hdiv0] at hm0

lemma card_alg4I_le_sub {N : ℕ} (d r h : ℕ) (hd : 2 ≤ d) (τ : List (Fin N))
    (hdvd : d ^ h ∣ τ.length) (hoff : τ.length + d ^ h ≤ d ^ r) :
    (alg4I d τ).card ≤ r - h := by
  calc
    (alg4I d τ).card
      ≤ ∑ i ∈ alg4K d τ.length, (τ[i - 1]?).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ alg4K d τ.length, 1 := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases τ[i - 1]? <;> simp
    _ = (alg4K d τ.length).card := by simp
    _ ≤ ((Finset.Ico h r).image (fun j => (τ.length / d ^ j) * d ^ j)).card :=
      Finset.card_le_card (alg4K_subset_Ico d r h τ.length hd hdvd hoff)
    _ ≤ (Finset.Ico h r).card := Finset.card_image_le
    _ = r - h := Nat.card_Ico h r

lemma alg4K_succ_subset (d k : ℕ) (hd : 2 ≤ d) :
    alg4K d (k + 1) ⊆ insert (k + 1) (alg4K d k) := by
  intro m hm
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hm
  rcases hm with ⟨hm0, j, _, rfl⟩
  set D := d ^ j
  have hDpos : 0 < D := Nat.pow_pos (by omega)
  have hrem_lt : k % D < D := Nat.mod_lt k hDpos
  by_cases hrem : k % D + 1 = D
  · have hk1 : k + 1 = D * (k / D + 1) := by
      have hdivmod := Nat.div_add_mod k D
      calc
        k + 1 = D * (k / D) + (k % D + 1) := by omega
        _ = D * (k / D) + D := by rw [hrem]
        _ = D * (k / D + 1) := by ring
    have hdiv : (k + 1) / D = k / D + 1 := by
      rw [hk1, Nat.mul_div_right _ hDpos]
    have hm_eq : (k + 1) / D * D = k + 1 := by
      rw [hdiv]
      linarith [hk1]
    rw [hm_eq]
    exact Finset.mem_insert_self _ _
  · have hrem_lt' : k % D + 1 < D := by omega
    have hk1 : k + 1 = (k % D + 1) + D * (k / D) := by
      have hdivmod := Nat.div_add_mod k D
      omega
    have hdiv : (k + 1) / D = k / D := by
      rw [hk1, Nat.add_mul_div_left _ _ hDpos, Nat.div_eq_of_lt hrem_lt', zero_add]
    rw [hdiv] at hm0 ⊢
    apply Finset.mem_insert_of_mem
    simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range]
    refine ⟨hm0, j, ?_, rfl⟩
    have hDk : D ≤ k := by
      by_contra hlt
      have h0 : k / D = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_le hlt)
      simp [h0] at hm0
    have hjD : j < D := Nat.lt_pow_self (by omega)
    omega

lemma alg4I_append_singleton_subset {N : ℕ} (d : ℕ) (hd : 2 ≤ d) (τ : List (Fin N)) (u : Fin N) :
    alg4I d (τ ++ [u]) ⊆ insert u (alg4I d τ) := by
  intro v hv
  simp only [alg4I, List.length_append, List.length_singleton, Finset.mem_biUnion,
    Option.mem_toFinset, Option.mem_def] at hv
  rcases hv with ⟨i, hiK, hvi⟩
  have hi' := alg4K_succ_subset d τ.length hd hiK
  rcases Finset.mem_insert.mp hi' with rfl | hiK0
  · simp only [Nat.add_sub_cancel, List.getElem?_append_right (le_refl τ.length),
      Nat.sub_self, List.getElem?_cons_zero] at hvi
    cases hvi
    exact Finset.mem_insert_self u _
  · obtain ⟨hi1, hi2⟩ := mem_alg4K_pos_le d τ.length i hiK0
    have hilt : i - 1 < τ.length := by omega
    rw [List.getElem?_append_left hilt] at hvi
    apply Finset.mem_insert_of_mem
    simp only [alg4I, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
    exact ⟨i, hiK0, hvi⟩

lemma div_subblock_eq (d h off s j : ℕ) (hd : 2 ≤ d) (hdvd : d ^ (h + 1) ∣ off)
    (hs : s < d) (hj : h + 1 ≤ j) :
    (off + s * d ^ h) / d ^ j = off / d ^ j := by
  rcases hdvd with ⟨A, hA⟩
  set t := j - (h + 1)
  have hj_eq : j = h + 1 + t := by omega
  have hdh_pos : 0 < d ^ h := Nat.pow_pos (by omega)
  have hd_pos : 0 < d := by omega
  have hdj : d ^ j = d ^ h * (d * d ^ t) := by
    rw [hj_eq, Nat.pow_add, Nat.pow_succ]
    ring
  have hoff_eq : off = d ^ h * (d * A) := by
    rw [hA, Nat.pow_succ]
    ring
  have hsum_eq : off + s * d ^ h = d ^ h * (s + d * A) := by
    rw [hA, Nat.pow_succ]
    ring
  calc
    (off + s * d ^ h) / d ^ j
      = (d ^ h * (s + d * A)) / (d ^ h * (d * d ^ t)) := by rw [hsum_eq, hdj]
    _ = (s + d * A) / (d * d ^ t) := Nat.mul_div_mul_left _ _ hdh_pos
    _ = ((s + d * A) / d) / d ^ t := (Nat.div_div_eq_div_mul _ _ _).symm
    _ = A / d ^ t := by rw [Nat.add_mul_div_left _ _ hd_pos, Nat.div_eq_of_lt hs, zero_add]
    _ = (d * A) / (d * d ^ t) := (Nat.mul_div_mul_left _ _ hd_pos).symm
    _ = (d ^ h * (d * A)) / (d ^ h * (d * d ^ t)) := (Nat.mul_div_mul_left _ _ hdh_pos).symm
    _ = off / d ^ j := by rw [← hoff_eq, ← hdj]

lemma alg4K_add_subblock (d h off s : ℕ) (hd : 2 ≤ d) (hdvd : d ^ (h + 1) ∣ off)
    (hs1 : 1 ≤ s) (hs2 : s < d) :
    alg4K d (off + s * d ^ h) = insert (off + s * d ^ h) (alg4K d off) := by
  have hspos : 0 < off + s * d ^ h := by
    have := Nat.mul_pos hs1 (Nat.pow_pos (a := d) (n := h) (by omega))
    omega
  ext m
  constructor
  · intro hm
    simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hm
    rcases hm with ⟨hm0, j, _, rfl⟩
    by_cases hj : j ≤ h
    · have hdvd1 : d ^ j ∣ d ^ h := Nat.pow_dvd_pow d hj
      have hdvd2 : d ^ j ∣ off + s * d ^ h :=
        dvd_add (dvd_trans hdvd1 (dvd_trans (Nat.pow_dvd_pow d (Nat.le_succ h)) hdvd))
          (dvd_trans hdvd1 (dvd_mul_left _ _))
      rw [Nat.div_mul_cancel hdvd2]
      exact Finset.mem_insert_self _ _
    · have hj' : h + 1 ≤ j := by omega
      have hdiv := div_subblock_eq d h off s j hd hdvd hs2 hj'
      rw [hdiv] at hm0 ⊢
      apply Finset.mem_insert_of_mem
      simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range]
      refine ⟨hm0, j, ?_, rfl⟩
      have hle : d ^ j ≤ off := by
        by_contra hlt
        simp [Nat.div_eq_of_lt (Nat.lt_of_not_le hlt)] at hm0
      have hj_lt : j < d ^ j := Nat.lt_pow_self (by omega)
      omega
  · intro hm
    rcases Finset.mem_insert.mp hm with rfl | hm0
    · simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range]
      exact ⟨by omega, 0, by omega, by simp⟩
    · simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hm0 ⊢
      rcases hm0 with ⟨hm_ne, j, hj_lt, rfl⟩
      have hoff_pos : 0 < off := by
        by_contra h0
        have : off = 0 := by omega
        simp [this] at hm_ne
      by_cases hj : j ≤ h
      · have hdvd_j : d ^ j ∣ off :=
          dvd_trans (Nat.pow_dvd_pow d (le_trans hj (Nat.le_succ h))) hdvd
        rw [Nat.div_mul_cancel hdvd_j]
        refine ⟨by omega, h + 1, ?_, ?_⟩
        · have hle : d ^ (h + 1) ≤ off := Nat.le_of_dvd hoff_pos hdvd
          have hlt : h + 1 < d ^ (h + 1) := Nat.lt_pow_self (by omega)
          omega
        · rw [div_subblock_eq d h off s (h + 1) hd hdvd hs2 (le_refl _),
            Nat.div_mul_cancel hdvd]
      · have hj' : h + 1 ≤ j := by omega
        refine ⟨hm_ne, j, by omega, ?_⟩
        rw [div_subblock_eq d h off s j hd hdvd hs2 hj']

lemma alg4I_append_subblock {N : ℕ} (d h : ℕ) (hd : 2 ≤ d) (τ P : List (Fin N)) (s : ℕ)
    (hdvd : d ^ (h + 1) ∣ τ.length) (hs1 : 1 ≤ s) (hs2 : s < d)
    (hPlen : P.length = s * d ^ h) (u : Fin N) (hlast : P.getLast? = some u) :
    alg4I d (τ ++ P) = insert u (alg4I d τ) := by
  have hspos : 1 ≤ s * d ^ h := Nat.mul_pos hs1 (Nat.pow_pos (by omega))
  have hlen_app : (τ ++ P).length = τ.length + s * d ^ h := by simp [hPlen]
  conv_lhs =>
    simp only [alg4I, hlen_app, alg4K_add_subblock d h τ.length s hd hdvd hs1 hs2,
      Finset.biUnion_insert]
  have hhead : ((τ ++ P)[τ.length + s * d ^ h - 1]?).toFinset = {u} := by
    have hge : τ.length ≤ τ.length + s * d ^ h - 1 := by omega
    rw [List.getElem?_append_right hge]
    have hsub : τ.length + s * d ^ h - 1 - τ.length = P.length - 1 := by omega
    rw [hsub, ← List.getLast?_eq_getElem?, hlast]
    rfl
  have htail : (alg4K d τ.length).biUnion (fun i => ((τ ++ P)[i - 1]?).toFinset) =
      alg4I d τ := by
    refine Finset.biUnion_congr rfl fun i hi => ?_
    obtain ⟨hi1, hi2⟩ := mem_alg4K_pos_le d τ.length i hi
    have hilt : i - 1 < τ.length := by omega
    rw [List.getElem?_append_left hilt]
  rw [hhead, htail, Finset.singleton_union]

lemma inQ_antimono (G : LGraph) (r : ℕ) (x : Finset (Fin G.N) → ℝ) (hx : InQ G r x) :
    ∀ {A B : Finset (Fin G.N)}, A ⊆ B → B.card ≤ r + 1 → x B ≤ x A := by
  suffices h : ∀ (s : Finset (Fin G.N)) (A : Finset (Fin G.N)),
      Disjoint A s → (A ∪ s).card ≤ r + 1 → x (A ∪ s) ≤ x A by
    intro A B hAB hB
    have hdisj : Disjoint A (B \ A) := disjoint_sdiff_self_right
    have hunion : A ∪ (B \ A) = B := Finset.union_sdiff_of_subset hAB
    simpa [hunion] using h (B \ A) A hdisj (by simpa [hunion] using hB)
  intro s
  induction s using Finset.induction_on with
  | empty => intro A _ _; simp
  | @insert v s hvs ih =>
    intro A hdisj hcard
    rw [Finset.disjoint_insert_right] at hdisj
    rcases hdisj with ⟨hvA, hdisj'⟩
    have hvAs : v ∉ A ∪ s := by simp [hvA, hvs]
    have hunion_eq : A ∪ insert v s = insert v (A ∪ s) := Finset.union_insert v A s
    rw [hunion_eq] at hcard ⊢
    have hcard_ins : (insert v (A ∪ s)).card = (A ∪ s).card + 1 :=
      Finset.card_insert_of_notMem hvAs
    calc
      x (insert v (A ∪ s)) ≤ x (A ∪ s) := hx.2.2.1 v (A ∪ s) (by omega)
      _ ≤ x A := ih A hdisj' (by omega)

noncomputable def mdpOneStep (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) :
    Option (List (Fin M.G.N)) → PMF (Option (List (Fin M.G.N)))
  | none => PMF.pure none
  | some τ =>
    match alg4 M d x τ with
    | none => PMF.pure none
    | some q =>
      match nextDist q with
      | none => PMF.pure none
      | some μ => μ.map (fun u => some (τ ++ [u]))

noncomputable def mdpIter (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) :
    ℕ → PMF (Option (List (Fin M.G.N))) → PMF (Option (List (Fin M.G.N)))
  | 0, ν => ν
  | m + 1, ν => (mdpIter M d x m ν).bind (mdpOneStep M d x)

lemma mdpIter_pure_nil (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) (k : ℕ) :
    mdpIter M d x k (PMF.pure (some [])) = mdpPrefix M d x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [mdpIter, mdpPrefix, ih]
    rfl

lemma mdpIter_add (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) (a b : ℕ)
    (ν : PMF (Option (List (Fin M.G.N)))) :
    mdpIter M d x (a + b) ν = mdpIter M d x b (mdpIter M d x a ν) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.add_succ, mdpIter, mdpIter, ih]

lemma mdpIter_bind {α : Type} (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) (m : ℕ)
    (μ : PMF α) (f : α → PMF (Option (List (Fin M.G.N)))) :
    mdpIter M d x m (μ.bind f) = μ.bind (fun a => mdpIter M d x m (f a)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [mdpIter, ih, PMF.bind_bind]
    rfl

lemma mdpIter_pure_none (M : GMDP) (d : ℕ) (x : Finset (Fin M.G.N) → ℝ) (m : ℕ) :
    mdpIter M d x m (PMF.pure none) = PMF.pure none := by
  induction m with
  | zero => rfl
  | succ m ih => simp [mdpIter, ih, mdpOneStep]

lemma pmf_map_eq_bind {α β : Type} (μ : PMF α) (f : α → β) :
    μ.map f = μ.bind (fun a => PMF.pure (f a)) := rfl

lemma pmf_bind_congr {α β : Type} (μ : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ μ.support, f a = g a) : μ.bind f = μ.bind g := by
  ext b
  simp only [PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ μ.support
  · rw [h a ha]
  · simp only [PMF.mem_support_iff, not_not] at ha
    simp [ha]

lemma mdpIter_support_len_pos (M : GMDP) (d r : ℕ) (hd : 2 ≤ d)
    (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x)
    (τ₀ : List (Fin M.G.N)) (hpos₀ : 0 < x (alg4I d τ₀)) :
    ∀ m, τ₀.length + m ≤ d ^ r →
      ∀ τ' : List (Fin M.G.N), some τ' ∈ (mdpIter M d x m (PMF.pure (some τ₀))).support →
        τ'.length = τ₀.length + m ∧ (τ₀.length + m < d ^ r → 0 < x (alg4I d τ')) := by
  intro m
  induction m with
  | zero =>
    intro _ τ' hτ'
    simp only [mdpIter, PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq] at hτ'
    subst hτ'
    exact ⟨by simp, fun _ => hpos₀⟩
  | succ m ih =>
    intro hm1 τ' hτ'
    simp only [mdpIter, PMF.mem_support_bind_iff] at hτ'
    rcases hτ' with ⟨o, ho, hstep⟩
    cases o with
    | none => simp [mdpOneStep] at hstep
    | some τ =>
      obtain ⟨hlen, hpos_prev⟩ := ih (by omega) τ ho
      have hxI_pos : 0 < x (alg4I d τ) := hpos_prev (by omega)
      simp only [mdpOneStep] at hstep
      cases halg : alg4 M d x τ with
      | none => simp [halg] at hstep
      | some q =>
        cases hnd : nextDist q with
        | none => simp [halg, hnd] at hstep
        | some μ =>
          simp only [halg, hnd, PMF.mem_support_map_iff, Option.some.injEq] at hstep
          rcases hstep with ⟨u, hu, rfl⟩
          refine ⟨by simp [hlen]; omega, fun hlt => ?_⟩
          unfold nextDist at hnd
          split_ifs at hnd with hprob
          cases hnd
          simp only [PMF.mem_support_iff, PMF.ofFintype_apply, ne_eq, ENNReal.ofReal_eq_zero,
            not_le] at hu
          simp only [alg4, hxI_pos.ne', ↓reduceIte, Option.some.injEq] at halg
          subst halg
          dsimp only at hu
          split_ifs at hu with hlay
          · have hxu_pos : 0 < x (insert u (alg4I d τ)) := by
              by_contra hnp
              have hdiv : x (insert u (alg4I d τ)) / x (alg4I d τ) ≤ 0 :=
                div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnp) hxI_pos.le
              linarith
            have hcardI : (alg4I d τ).card ≤ r := by
              have hsub := card_alg4I_le_sub d r 0 hd τ (by simp) (by simp; omega)
              omega
            have hcardB : (insert u (alg4I d τ)).card ≤ r + 1 := by
              have := Finset.card_insert_le u (alg4I d τ)
              omega
            have hle_x := inQ_antimono M.G r x hx (alg4I_append_singleton_subset d hd τ u) hcardB
            linarith
          · linarith

noncomputable def rrrStep (G : LGraph) (_blk : ℕ)
    (sub : ℕ → (Finset (Fin G.N) → ℝ) → PMF (Option (List (Fin G.N))))
    (x : Finset (Fin G.N) → ℝ) (off : ℕ) :
    Option (List (Fin G.N)) → PMF (Option (List (Fin G.N)))
  | none => PMF.pure none
  | some P =>
    match P.getLast? with
    | none => PMF.pure none
    | some u =>
      if x {u} = 0 then PMF.pure none
      else (sub off (SubmodMDP.Policies.cond x u)).bind (fun o =>
        match o with
        | none => PMF.pure none
        | some Pi => PMF.pure (some (P ++ Pi)))

lemma rrrTail_succ_eq_bind (G : LGraph) (blk : ℕ)
    (sub : ℕ → (Finset (Fin G.N) → ℝ) → PMF (Option (List (Fin G.N))))
    (x : Finset (Fin G.N) → ℝ) :
    ∀ (k off : ℕ) (acc : List (Fin G.N)),
      rrrTail G blk sub x (k + 1) off acc =
        (rrrTail G blk sub x k off acc).bind (rrrStep G blk sub x (off + k * blk))
  | 0, off, acc => by
    simp only [rrrTail, Nat.zero_mul, add_zero, PMF.pure_bind]
    rfl
  | k + 1, off, acc => by
    rw [rrrTail.eq_2, rrrTail.eq_2]
    cases acc.getLast? with
    | none => simp [rrrStep]
    | some u =>
      by_cases hxu : x {u} = 0
      · simp [hxu, rrrStep]
      · simp only [hxu, ↓reduceIte, PMF.bind_bind]
        congr 1
        funext o
        cases o with
        | none => simp [rrrStep]
        | some Pi =>
          dsimp only
          rw [rrrTail_succ_eq_bind G blk sub x k (off + blk) (acc ++ Pi)]
          have heq : off + blk + k * blk = off + (k + 1) * blk := by ring
          rw [heq]

lemma mdpIter_eq_rrr (M : GMDP) (d r : ℕ) (hd : 2 ≤ d) (hH : M.G.H = d ^ r)
    (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x) :
    ∀ (h : ℕ), h ≤ r → ∀ (off : ℕ), d ^ h ∣ off → off + d ^ h ≤ d ^ r →
      ∀ (τ : List (Fin M.G.N)), τ.length = off → 0 < x (alg4I d τ) →
        mdpIter M d x (d ^ h) (PMF.pure (some τ)) =
          (rrr M.G d h off (condSet x (alg4I d τ))).map (Option.map (τ ++ ·))
  | 0, h0r, off, _, hoff, τ, hτlen, hxI => by
    rw [Nat.pow_zero] at hoff ⊢
    set y := condSet x (alg4I d τ)
    have hcard : (alg4I d τ).card ≤ r - 0 :=
      card_alg4I_le_sub d r 0 hd τ (by simp) (by rw [hτlen, Nat.pow_zero]; exact hoff)
    have hy : InQ M.G 0 y := inQ_condSet M.G r 0 h0r x hx (alg4I d τ) hcard hxI
    set q : Fin M.G.N → ℝ := fun u =>
      if M.G.layer u = off + 1 then x (insert u (alg4I d τ)) / x (alg4I d τ) else 0
    have halg : alg4 M d x τ = some q := by
      simp [alg4, hxI.ne', hτlen, q]
    have hq_eq_y : ∀ u, q u = if M.G.layer u = off + 1 then y {u} else 0 := by
      intro u
      simp [q, y, condSet, Finset.singleton_union]
    have hnonneg_y : ∀ w, M.G.layer w = off + 1 → 0 ≤ y {w} :=
      fun w _ => hy.2.2.2.2 {w} (by simp)
    have hnonneg_q : ∀ u, 0 ≤ q u := by
      intro u
      rw [hq_eq_y]
      by_cases hu : M.G.layer u = off + 1
      · simp [hu, hnonneg_y u hu]
      · simp [hu]
    have hofReal_q : ∀ u, ENNReal.ofReal (q u) =
        if M.G.layer u = off + 1 then ENNReal.ofReal (y {u}) else 0 := by
      intro u
      rw [hq_eq_y]
      by_cases hu : M.G.layer u = off + 1 <;> simp [hu]
    have hsum_y : ∑ w : Fin M.G.N,
        (if M.G.layer w = off + 1 then ENNReal.ofReal (y {w}) else 0) = 1 := by
      rw [← Finset.sum_filter]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun w hw => hnonneg_y w (Finset.mem_filter.mp hw).2)]
      have h2 := hy.2.1 (off + 1) (by omega) (by omega) ∅ (by simp)
      simp [hy.2.2.2.1] at h2
      simp [h2]
    have hsum_q : ∑ u : Fin M.G.N, ENNReal.ofReal (q u) = 1 := by
      simp_rw [hofReal_q]
      exact hsum_y
    let hp_q : (∀ u, 0 ≤ q u) ∧ ∑ u, ENNReal.ofReal (q u) = 1 := ⟨hnonneg_q, hsum_q⟩
    let hp_y : (∀ w, M.G.layer w = off + 1 → 0 ≤ y {w}) ∧
        ∑ w, (if M.G.layer w = off + 1 then ENNReal.ofReal (y {w}) else 0) = 1 :=
      ⟨hnonneg_y, hsum_y⟩
    have hnd : nextDist q = some (PMF.ofFintype (fun u => ENNReal.ofReal (q u)) hp_q.2) := by
      unfold nextDist
      rw [dif_pos hp_q]
    have hld : layerDist M.G y (off + 1) =
        some (PMF.ofFintype (fun w => if M.G.layer w = off + 1 then ENNReal.ofReal (y {w}) else 0)
          hp_y.2) := by
      unfold layerDist
      rw [dif_pos hp_y]
    have hpmf_eq : PMF.ofFintype (fun u => ENNReal.ofReal (q u)) hp_q.2 =
        PMF.ofFintype (fun w => if M.G.layer w = off + 1 then ENNReal.ofReal (y {w}) else 0)
          hp_y.2 := by
      ext u
      simp [hofReal_q]
    simp only [mdpIter, PMF.pure_bind, mdpOneStep, halg, hnd, rrr, hld, hpmf_eq, PMF.map_comp]
    rfl
  | h + 1, hhr, off, hdvd, hoff, τ, hτlen, hxI => by
    set blk := d ^ h with hblk_def
    have hblk_pos : 1 ≤ blk := Nat.one_le_pow h d (by omega)
    have hdh1 : d ^ (h + 1) = d * blk := by rw [Nat.pow_succ, hblk_def, mul_comm]
    have hoff_d : off + d * blk ≤ d ^ r := by rwa [← hdh1]
    set y := condSet x (alg4I d τ)
    let pref : ℕ → PMF (Option (List (Fin M.G.N))) := fun m =>
      (rrr M.G d h off y).bind (fun o =>
        match o with
        | none => PMF.pure none
        | some P₁ => rrrTail M.G blk (rrr M.G d h) y m (off + blk) P₁)
    have hpref_zero : pref 0 = rrr M.G d h off y := by
      dsimp [pref]
      have hfun : (fun o : Option (List (Fin M.G.N)) =>
          match o with
          | none => PMF.pure none
          | some P₁ => rrrTail M.G blk (rrr M.G d h) y 0 (off + blk) P₁) = PMF.pure := by
        funext o
        cases o <;> rfl
      rw [hfun, PMF.bind_pure]
    have hpref_succ : ∀ m, pref (m + 1) =
        (pref m).bind (rrrStep M.G blk (rrr M.G d h) y (off + (m + 1) * blk)) := by
      intro m
      dsimp [pref]
      rw [PMF.bind_bind]
      congr 1
      funext o
      cases o with
      | none => simp [rrrStep]
      | some P₁ =>
        dsimp only
        rw [rrrTail_succ_eq_bind]
        have heq : off + blk + m * blk = off + (m + 1) * blk := by ring
        rw [heq]
    have h_inner : ∀ m ≤ d - 1,
        mdpIter M d x ((m + 1) * blk) (PMF.pure (some τ)) =
          (pref m).map (Option.map (τ ++ ·)) := by
      intro m
      induction m with
      | zero =>
        intro _
        rw [Nat.zero_add, one_mul, hpref_zero]
        have hdvd_h : d ^ h ∣ off := dvd_trans (Nat.pow_dvd_pow d (Nat.le_succ h)) hdvd
        have hoff_h : off + d ^ h ≤ d ^ r := by
          rw [← hblk_def]
          have : 1 * blk ≤ d * blk := Nat.mul_le_mul_right blk (by omega)
          omega
        exact mdpIter_eq_rrr M d r hd hH x hx h (by omega) off hdvd_h hoff_h τ hτlen hxI
      | succ m ih =>
        intro hm1
        have heq_mul : (m + 1 + 1) * blk = (m + 1) * blk + blk := by ring
        rw [heq_mul, mdpIter_add, ih (by omega), hpref_succ]
        conv_lhs => rw [pmf_map_eq_bind (pref m), mdpIter_bind M d x blk (pref m)]
        conv_rhs => rw [pmf_map_eq_bind, PMF.bind_bind]
        refine pmf_bind_congr (pref m) _ _ fun o ho => ?_
        cases o with
        | none =>
          simp [mdpIter_pure_none, rrrStep]
        | some P =>
          have hmem_map : some (τ ++ P) ∈ ((pref m).map (Option.map (τ ++ ·))).support := by
            rw [PMF.mem_support_map_iff]
            exact ⟨some P, ho, rfl⟩
          rw [← ih (by omega)] at hmem_map
          have hlen_lt : τ.length + (m + 1) * blk < d ^ r := by
            have : (m + 1) * blk < d * blk :=
              Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
            omega
          obtain ⟨hτPlen, hx_τP⟩ :=
            mdpIter_support_len_pos M d r hd x hx τ hxI ((m + 1) * blk) hlen_lt.le (τ ++ P) hmem_map
          have hx_τP_pos : 0 < x (alg4I d (τ ++ P)) := hx_τP hlen_lt
          have hPlen : P.length = (m + 1) * blk := by
            simp only [List.length_append] at hτPlen
            omega
          have hPlen_pos : 1 ≤ P.length := by
            rw [hPlen]
            exact Nat.mul_pos (by omega) hblk_pos
          have hidx : P.length - 1 < P.length := by omega
          set u := P[P.length - 1]
          have hlast : P.getLast? = some u := by
            rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hidx]
          have hI_eq : alg4I d (τ ++ P) = insert u (alg4I d τ) :=
            alg4I_append_subblock d h hd τ P (m + 1) (by simpa [hτlen] using hdvd)
              (by omega) (by omega) (by simpa [← hblk_def] using hPlen) u hlast
          rw [hI_eq] at hx_τP_pos
          have hyu_pos : 0 < y {u} := by
            simp only [y, condSet, Finset.singleton_union]
            exact div_pos hx_τP_pos hxI
          have hdvd_next : d ^ h ∣ off + (m + 1) * blk := by
            refine dvd_add (dvd_trans (Nat.pow_dvd_pow d (Nat.le_succ h)) hdvd) ?_
            rw [← hblk_def]
            exact dvd_mul_left _ _
          have hoff_next : (off + (m + 1) * blk) + d ^ h ≤ d ^ r := by
            rw [← hblk_def]
            have h1 : (m + 2) * blk ≤ d * blk := Nat.mul_le_mul_right blk (by omega)
            have h2 : (off + (m + 1) * blk) + blk = off + (m + 2) * blk := by ring
            omega
          have hih_outer := mdpIter_eq_rrr M d r hd hH x hx h (by omega) (off + (m + 1) * blk)
            hdvd_next hoff_next (τ ++ P) (by simpa [hτlen] using hτPlen)
            (by rwa [hI_eq])
          dsimp only [Function.comp_apply, Option.map_some]
          rw [hblk_def] at *
          rw [hih_outer, hI_eq, ← cond_condSet x (alg4I d τ) u hxI.ne']
          simp only [rrrStep, hlast, hyu_pos.ne', ↓reduceIte, PMF.bind_bind, pmf_map_eq_bind]
          refine pmf_bind_congr _ _ _ fun o2 _ => ?_
          cases o2 <;> simp [List.append_assoc]
    have hfinal := h_inner (d - 1) (le_refl _)
    have hdm1 : (d - 1 + 1) * blk = d ^ (h + 1) := by
      have : d - 1 + 1 = d := by omega
      rw [this, hdh1]
    rw [hdm1] at hfinal
    have hpref_eq : pref (d - 1) = rrr M.G d (h + 1) off (condSet x (alg4I d τ)) := by
      dsimp only [pref, rrr, blk, y]
      congr 1
      funext o
      cases o <;> rfl
    rwa [hpref_eq] at hfinal

end Lemma13Aux

set_option linter.unusedVariables false in
theorem solution (M : GMDP) (hM : M.WF) (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hH : M.G.H = d ^ r) (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x) (h7 : Sat7 M r x) :
    MDPlaw M d x = RRR M.G d r x := by
  rw [MDPlaw, hH, ← Lemma13Aux.mdpIter_pure_nil]
  have hI0 : alg4I d ([] : List (Fin M.G.N)) = ∅ := by simp [alg4I, alg4K]
  have hx0 : 0 < x (alg4I d ([] : List (Fin M.G.N))) := by
    rw [hI0, hx.2.2.2.1]
    exact zero_lt_one
  have heq := Lemma13Aux.mdpIter_eq_rrr M d r hd hH x hx r (le_refl r) 0 (dvd_zero _)
    (by simp) [] rfl hx0
  rw [heq, hI0, Lemma13Aux.condSet_empty M.G r x hx, RRR]
  have hmap_id : (Option.map (([] : List (Fin M.G.N)) ++ ·)) = id := by
    funext o
    cases o <;> simp
  rw [hmap_id, PMF.map_id]
