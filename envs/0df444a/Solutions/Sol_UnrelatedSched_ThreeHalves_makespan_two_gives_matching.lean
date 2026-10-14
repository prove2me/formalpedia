-- Prove2me | solution 1 for UnrelatedSched.ThreeHalves.makespan_two_gives_matching
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:02:05.942049+00:00
-- url     : https://prove2.me/submissions/1d789ebc-1c27-4fdf-8838-175a14a6cdb4

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
import Definitions.Def_UnrelatedSched_ThreeHalves_Theorem5Instance

open MatousekLP.Scheduling


namespace UnrelatedSched.ThreeHalves

lemma sum_typeCount {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    ∑ j : Fin n, typeCount T j = m := by
  unfold typeCount
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun i : Fin m => (T i).1) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  simp

lemma sum_succ_eq {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    ∑ j : Fin n, (typeCount T j - 1 + 1) = (∑ j : Fin n, (typeCount T j - 1)) + n := by
  simp [Finset.sum_add_distrib]

lemma m_le {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    m ≤ (∑ j : Fin n, (typeCount T j - 1)) + n := by
  calc m = ∑ j : Fin n, typeCount T j := (sum_typeCount T).symm
    _ ≤ ∑ j : Fin n, (typeCount T j - 1 + 1) := Finset.sum_le_sum (fun j _ => by omega)
    _ = _ := sum_succ_eq T

lemma m_lt {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (j0 : Fin n) (h : typeCount T j0 = 0) :
    m < (∑ j : Fin n, (typeCount T j - 1)) + n := by
  calc m = ∑ j : Fin n, typeCount T j := (sum_typeCount T).symm
    _ < ∑ j : Fin n, (typeCount T j - 1 + 1) :=
        Finset.sum_lt_sum (fun j _ => by omega) ⟨j0, Finset.mem_univ _, by omega⟩
    _ = _ := sum_succ_eq T

theorem dummy_count_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : ∀ j : Fin n, 1 ≤ typeCount T j) :
    (∑ j : Fin n, (typeCount T j - 1)) + n = m := by
  calc _ = ∑ j : Fin n, (typeCount T j - 1 + 1) := (sum_succ_eq T).symm
    _ = ∑ j : Fin n, typeCount T j := Finset.sum_congr rfl (fun j _ => by have := hT j; omega)
    _ = m := sum_typeCount T

lemma load_eq {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (σ' : Job T → Fin m) (i : Fin m) :
    load (fun i r => (P T i r : ℝ)) (fun r => σ' ((jobEnum T).symm r)) i
      = ∑ x ∈ Finset.univ.filter (fun x => σ' x = i), (procTime T i x : ℝ) := by
  unfold load
  refine Finset.sum_equiv (jobEnum T).symm ?_ ?_
  · intro r; simp
  · intro r hr; simp [P]

lemma makespan_le_iff {m k : ℕ} (d : Matrix (Fin m) (Fin k) ℝ) (σ : Fin k → Fin m) :
    makespan d σ ≤ 2 ↔ ∀ i, load d σ i ≤ 2 := by
  unfold makespan
  constructor
  · intro h i; exact le_trans (le_ciSup (f := fun i => load d σ i) (Set.finite_range _).bddAbove i) h
  · intro h; exact Real.iSup_le h (by norm_num)

lemma makespan_iff_job {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (σ : Fin (numJobs T) → Fin m) :
    makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 ↔
      ∀ i, ∑ x ∈ Finset.univ.filter (fun x => (σ (jobEnum T x)) = i), (procTime T i x : ℝ) ≤ 2 := by
  refine Iff.trans (makespan_le_iff (fun i r => (P T i r : ℝ)) σ) ?_
  have : ∀ i, load (fun i r => (P T i r : ℝ)) σ i
      = ∑ x ∈ Finset.univ.filter (fun x => (σ (jobEnum T x)) = i), (procTime T i x : ℝ) := by
    intro i
    have h := load_eq T (fun x => σ (jobEnum T x)) i
    simpa using h
  simp only [this]

lemma exists_sched {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (σ' : Job T → Fin m)
    (hs : ∀ i, ∑ x ∈ Finset.univ.filter (fun x => σ' x = i), (procTime T i x : ℝ) ≤ 2) :
    ∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 := by
  refine ⟨fun r => σ' ((jobEnum T).symm r), ?_⟩
  refine (makespan_le_iff (fun i r => (P T i r : ℝ)) _).2 ?_
  intro i
  rw [load_eq]
  exact hs i

lemma procTime_pos {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m) (x : Job T) :
    1 ≤ procTime T i x := by
  rcases x with k | l | ⟨j, r⟩ <;> simp only [procTime] <;> split_ifs <;> omega

lemma procTime_dummy {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (i : Fin m)
    (y : Σ j : Fin n, Fin (typeCount T j - 1)) :
    2 ≤ procTime T i (Sum.inr (Sum.inr y)) := by
  obtain ⟨j, r⟩ := y
  simp only [procTime]; split_ifs <;> omega

lemma matching_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (hT : HasMatching T) :
    ∃ σ' : Job T → Fin m, ∀ i,
      ∑ x ∈ Finset.univ.filter (fun x => σ' x = i), (procTime T i x : ℝ) ≤ 2 := by
  obtain ⟨F', hcard, ha, hb, hc⟩ := hT
  have hinj : Set.InjOn (fun i => (T i).1) (F' : Set (Fin m)) := by
    rw [← Finset.card_image_iff]
    have : F'.image (fun i => (T i).1) = Finset.univ := by
      ext j; simp only [Finset.mem_image, Finset.mem_univ, iff_true]
      obtain ⟨i, hi, hij⟩ := ha j
      exact ⟨i, hi, hij⟩
    rw [this]; simp [hcard]
  choose fa hfaF hfa using ha
  choose fb hfbF hfb using hb
  choose fc hfcF hfc using hc
  have hE : ∀ j : Fin n, ∃ e : Fin (typeCount T j - 1) → Fin m, Function.Injective e ∧
      ∀ r, (T (e r)).1 = j ∧ e r ∉ F' := by
    intro j
    set S := (Finset.univ.filter (fun i : Fin m => (T i).1 = j)).erase (fa j) with hS
    have hcS : S.card = typeCount T j - 1 := by
      rw [hS, Finset.card_erase_of_mem (by simp [hfa])]; rfl
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
      (α := Fin (typeCount T j - 1)) (β := S) (by simp [hcS])
    refine ⟨fun r => (f r).1, ?_, ?_⟩
    · intro a b hab; exact f.injective (Subtype.ext hab)
    · intro r
      have hm : (f r).1 ∈ (Finset.univ.filter (fun i : Fin m => (T i).1 = j)).erase (fa j) := (f r).2
      rw [Finset.mem_erase, Finset.mem_filter] at hm
      refine ⟨hm.2.2, fun hF => hm.1 ?_⟩
      exact hinj hF (hfaF j) (by simp [hm.2.2, hfa])
  choose e he1 he2 using hE
  refine ⟨fun x => Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x, ?_⟩
  intro i
  by_cases hi : i ∈ F'
  · have hsub : Finset.univ.filter (fun x : Job T =>
        Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x = i)
        ⊆ {Sum.inl (T i).2.1, Sum.inr (Sum.inl (T i).2.2)} := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases x with k | l | ⟨j, r⟩
      · have := hfb k; simp only [Sum.elim_inl] at hx
        rw [hx.2] at this; simp [this]
      · have := hfc l; simp only [Sum.elim_inr, Sum.elim_inl] at hx
        rw [hx.2] at this; simp [this]
      · simp only [Sum.elim_inr] at hx
        exact absurd (hx.2 ▸ hi) ((he2 j r).2)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)) ?_
    rw [Finset.sum_pair (by simp)]
    simp [procTime]
    norm_num
  · by_cases hex : ∃ x : Job T, Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x = i
    · obtain ⟨x0, hx0⟩ := hex
      rcases x0 with k | l | ⟨j0, r0⟩
      · exact absurd (by simpa using hx0 ▸ hfbF k) hi
      · exact absurd (by simpa using hx0 ▸ hfcF l) hi
      · simp only [Sum.elim_inr] at hx0
        have hj0 : (T i).1 = j0 := hx0 ▸ (he2 j0 r0).1
        have hsub : Finset.univ.filter (fun x : Job T =>
            Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x = i)
            ⊆ {Sum.inr (Sum.inr ⟨j0, r0⟩)} := by
          intro x hx
          rw [Finset.mem_filter] at hx
          rcases x with k | l | ⟨j, r⟩
          · exact absurd (by simpa using hx.2 ▸ hfbF k) hi
          · exact absurd (by simpa using hx.2 ▸ hfcF l) hi
          · simp only [Sum.elim_inr] at hx
            have hj : (T i).1 = j := hx.2 ▸ (he2 j r).1
            obtain rfl : j = j0 := hj.symm.trans hj0
            have : r = r0 := (he1 j) (hx.2.trans hx0.symm)
            subst this; simp
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)) ?_
        simp [procTime, hj0]
    · have : Finset.univ.filter (fun x : Job T =>
          Sum.elim fb (Sum.elim fc (fun y => e y.1 y.2)) x = i) = ∅ := by
        ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hex ⟨x, h⟩
      rw [this]; simp

theorem matching_gives_makespan_two_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (hT : HasMatching T) :
    ∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 := by
  obtain ⟨σ', h⟩ := matching_core T hT
  exact exists_sched T σ' h

lemma matching_of_job {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (σ' : Job T → Fin m)
    (hs : ∀ i, ∑ x ∈ Finset.univ.filter (fun x => σ' x = i), (procTime T i x : ℝ) ≤ 2) :
    HasMatching T := by
  have single : ∀ x, procTime T (σ' x) x ≤ 2 := by
    intro x
    have h := le_trans (Finset.single_le_sum (f := fun y => (procTime T (σ' x) y : ℝ))
      (s := Finset.univ.filter (fun y => σ' y = σ' x)) (a := x)
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_filter.2 ⟨Finset.mem_univ x, rfl⟩)) (hs (σ' x))
    exact_mod_cast h
  have pair : ∀ (i : Fin m) (x y : Job T), x ≠ y → σ' x = i → σ' y = i →
      procTime T i x + procTime T i y ≤ 2 := by
    intro i x y hxy hx hy
    have hsub : ({x, y} : Finset (Job T)) ⊆ Finset.univ.filter (fun z => σ' z = i) := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> simp [*]
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun z => (procTime T i z : ℝ)) (fun _ _ _ => Nat.cast_nonneg _)
    rw [Finset.sum_pair hxy] at h1
    have h2 := le_trans h1 (hs i)
    exact_mod_cast h2
  obtain ⟨d, hd⟩ : ∃ d : (Σ j : Fin n, Fin (typeCount T j - 1)) → Fin m,
      ∀ x, d x = σ' (Sum.inr (Sum.inr x)) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin n → Fin m, ∀ k, β k = σ' (Sum.inl k) := ⟨_, fun _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → Fin m, ∀ l, γ l = σ' (Sum.inr (Sum.inl l)) := ⟨_, fun _ => rfl⟩
  have hdT : ∀ x : (Σ j : Fin n, Fin (typeCount T j - 1)), (T (d x)).1 = x.1 := by
    intro x
    have h := single (Sum.inr (Sum.inr x))
    rw [← hd x] at h
    obtain ⟨j, r⟩ := x
    simp only [procTime] at h ⊢
    by_contra hne; rw [if_neg hne] at h; omega
  have hβT : ∀ k, (T (β k)).2.1 = k := by
    intro k
    have h := single (Sum.inl k)
    rw [← hβ k] at h
    simp only [procTime] at h
    by_contra hne; rw [if_neg hne] at h; omega
  have hγT : ∀ l, (T (γ l)).2.2 = l := by
    intro l
    have h := single (Sum.inr (Sum.inl l))
    rw [← hγ l] at h
    simp only [procTime] at h
    by_contra hne; rw [if_neg hne] at h; omega
  have hdinj : Function.Injective d := by
    intro x y hxy
    by_contra hne
    have hne' : (Sum.inr (Sum.inr x) : Job T) ≠ Sum.inr (Sum.inr y) := by simp [hne]
    have h1 := pair (d x) _ _ hne' (hd x).symm (by rw [← hd y]; exact hxy.symm)
    have h2 := procTime_dummy T (d x) x
    have h3 := procTime_dummy T (d x) y
    omega
  have hβinj : Function.Injective β := fun a b h => by rw [← hβT a, ← hβT b, h]
  have hγinj : Function.Injective γ := fun a b h => by rw [← hγT a, ← hγT b, h]
  have hβF : ∀ k x, d x ≠ β k := by
    intro k x h
    have hne : (Sum.inl k : Job T) ≠ Sum.inr (Sum.inr x) := by simp
    have h1 := pair (β k) _ _ hne (hβ k).symm (by rw [← hd x]; exact h)
    have h2 := procTime_dummy T (β k) x
    have h3 := procTime_pos T (β k) (Sum.inl k)
    omega
  have hγF : ∀ l x, d x ≠ γ l := by
    intro l x h
    have hne : (Sum.inr (Sum.inl l) : Job T) ≠ Sum.inr (Sum.inr x) := by simp
    have h1 := pair (γ l) _ _ hne (hγ l).symm (by rw [← hd x]; exact h)
    have h2 := procTime_dummy T (γ l) x
    have h3 := procTime_pos T (γ l) (Sum.inr (Sum.inl l))
    omega
  set F' : Finset (Fin m) := (Finset.univ.image d)ᶜ with hF'
  have hmem : ∀ i, i ∈ F' ↔ ∀ x, d x ≠ i := by
    intro i; simp only [hF', Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  have hD : (Finset.univ.image d).card = ∑ j : Fin n, (typeCount T j - 1) := by
    rw [Finset.card_image_of_injective _ hdinj]; simp [Fintype.card_sigma]
  have hsum : (Finset.univ.image d).card + F'.card = m := by
    rw [hF']; simpa using Finset.card_add_card_compl (Finset.univ.image d)
  have hn : n ≤ F'.card := by
    have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n))) (t := F') β
      (fun k _ => (hmem _).2 (fun x => hβF k x)) (hβinj.injOn)
    simpa using this
  have hml := m_le T
  have hcardn : F'.card = n := by omega
  have hT1 : ∀ j, 1 ≤ typeCount T j := by
    intro j
    by_contra hlt
    have := m_lt T j (by omega)
    omega
  refine ⟨F', hcardn, ?_, ?_, ?_⟩
  · intro j
    by_contra hno
    push_neg at hno
    have hsub : Finset.univ.filter (fun i : Fin m => (T i).1 = j) ⊆
        Finset.univ.image (fun r : Fin (typeCount T j - 1) => d ⟨j, r⟩) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      have hiF : i ∉ F' := fun h => hno i h hi.2
      have : i ∈ Finset.univ.image d := by
        by_contra hh; exact hiF (by simpa [hF'] using hh)
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 this
      obtain ⟨j', r⟩ := x
      have h3 := hdT ⟨j', r⟩
      rw [hx] at h3
      have hj' : j' = j := h3.symm.trans hi.2
      subst hj'
      exact Finset.mem_image.2 ⟨r, Finset.mem_univ _, hx⟩
    have h1 : typeCount T j ≤ (Finset.univ.image
        (fun r : Fin (typeCount T j - 1) => d ⟨j, r⟩)).card := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin (typeCount T j - 1))))
      (f := fun r : Fin (typeCount T j - 1) => d ⟨j, r⟩)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have := hT1 j
    omega
  · intro k; exact ⟨β k, (hmem _).2 (fun x => hβF k x), hβT k⟩
  · intro l; exact ⟨γ l, (hmem _).2 (fun x => hγF l x), hγT l⟩

theorem makespan_two_gives_matching_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (σ : Fin (numJobs T) → Fin m) (hσ : makespan (fun i r => (P T i r : ℝ)) σ ≤ 2) :
    HasMatching T :=
  matching_of_job T (fun x => σ (jobEnum T x)) ((makespan_iff_job T σ).1 hσ)

theorem theorem_5_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) :
    (∃ σ : Fin (numJobs T) → Fin m, makespan (fun i r => (P T i r : ℝ)) σ ≤ 2) ↔
      HasMatching T :=
  ⟨fun ⟨σ, h⟩ => makespan_two_gives_matching_core T σ h, matching_gives_makespan_two_core T⟩

theorem corollary_2_core {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (ρ : ℝ) (hρ : ρ < 3 / 2)
    (σ : Fin (numJobs T) → Fin m)
    (hσ : ∀ τ : Fin (numJobs T) → Fin m,
      makespan (fun i r => (P T i r : ℝ)) σ ≤ ρ * makespan (fun i r => (P T i r : ℝ)) τ) :
    makespan (fun i r => (P T i r : ℝ)) σ ≤ 2 ↔ HasMatching T := by
  constructor
  · intro h; exact makespan_two_gives_matching_core T σ h
  · intro hM
    obtain ⟨τ, hτ⟩ := matching_gives_makespan_two_core T hM
    have h0 : 0 ≤ makespan (fun i r => (P T i r : ℝ)) τ := by
      unfold makespan
      exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
    have h1 := hσ τ
    have h3 : makespan (fun i r => (P T i r : ℝ)) σ < 3 := by
      rcases le_or_gt 0 ρ with hρ0 | hρ0 <;> nlinarith
    refine (makespan_le_iff (fun i r => (P T i r : ℝ)) σ).2 ?_
    intro i
    have hl : load (fun i r => (P T i r : ℝ)) σ i ≤ makespan (fun i r => (P T i r : ℝ)) σ :=
      le_ciSup (f := fun i => load (fun i r => (P T i r : ℝ)) σ i) (Set.finite_range _).bddAbove i
    have hnat : load (fun i r => (P T i r : ℝ)) σ i
        = ((∑ r ∈ Finset.univ.filter (fun r => σ r = i), P T i r : ℕ) : ℝ) := by
      unfold load; push_cast; rfl
    rw [hnat] at hl ⊢
    generalize (∑ r ∈ Finset.univ.filter (fun r => σ r = i), P T i r : ℕ) = N at hl ⊢
    have h4 : (N : ℝ) < 3 := lt_of_le_of_lt hl h3
    have h5 : N < 3 := by exact_mod_cast h4
    have h6 : N ≤ 2 := by omega
    exact_mod_cast h6

end UnrelatedSched.ThreeHalves

open UnrelatedSched.ThreeHalves


theorem solution {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n)
    (σ : Fin (numJobs T) → Fin m) (hσ : makespan (fun i r => (P T i r : ℝ)) σ ≤ 2) :
    HasMatching T := by
  exact makespan_two_gives_matching_core T σ hσ
