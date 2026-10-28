-- Prove2me | solution 1 for OSPMech.SqrtLB.lemma_13_part_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:47:40.757112+00:00
-- url     : https://prove2.me/submissions/6513f7d0-2136-42db-b91c-906f5b832874

import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB

variable {n : ℕ} {X : Type}

theorem e11_compat_iff (t : ImplTree n X) (pos : List ℕ) (b : Fin n → ℝ) :
    Compatible t pos b ↔ ∃ v, subtreeAt t pos = some v ∧ path t b = pos ++ path v b := by
  unfold Compatible
  induction pos generalizing t with
  | nil => simp [subtreeAt]
  | cons a pos ih =>
    cases t with
    | leaf x => simp [subtreeAt, path]
    | node i act ch =>
      simp only [subtreeAt, path, List.cons_prefix_cons, List.cons_append, List.cons.injEq]
      constructor
      · rintro ⟨h1, h2⟩
        subst h1
        obtain ⟨v, hv, hp⟩ := (ih (ch (act (b i)))).1 h2
        exact ⟨v, hv, rfl, hp⟩
      · rintro ⟨v, hv, rfl, hp⟩
        exact ⟨rfl, (ih _).2 ⟨v, hv, hp⟩⟩


theorem e11_outcome_eq_of_path_eq (t : ImplTree n X) (b b' : Fin n → ℝ)
    (h : path t b = path t b') : outcome t b = outcome t b' := by
  induction t with
  | leaf x => simp [outcome]
  | node i act ch ih =>
    simp only [path, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [outcome]
    rw [← h1] at h2 ⊢
    exact ih _ h2

theorem e11_path_prefix_eq (t : ImplTree n X) (b b' : Fin n → ℝ)
    (h : path t b <+: path t b') : path t b = path t b' := by
  induction t with
  | leaf x => simp [path]
  | node i act ch ih =>
    simp only [path, List.cons_prefix_cons] at h ⊢
    obtain ⟨h1, h2⟩ := h
    rw [← h1] at h2 ⊢
    rw [ih _ h2]

theorem e11_diverge_symm {t : ImplTree n X} {pos : List ℕ} {i : Fin n} {b b' : Fin n → ℝ}
    (h : DivergeAt t pos i b b') : DivergeAt t pos i b' b := by
  obtain ⟨h1, h2, act, ch, h3, h4⟩ := h
  exact ⟨h2, h1, act, ch, h3, h4.symm⟩

theorem e11_weak_mono {D : Fin n → Finset ℝ} {t : ImplTree n (Fin n → ℕ)}
    {p : (Fin n → ℝ) → Fin n → ℝ} (hosp : IsOSP D schedCost t p) {pos : List ℕ} {i : Fin n}
    {b b' : Fin n → ℝ} (hb : InDomain D b) (hb' : InDomain D b') (hd : DivergeAt t pos i b b') :
    0 ≤ (b i - b' i) * ((outcome t b' i : ℝ) - outcome t b i) := by
  have h1 := hosp pos i b b' hb hb' hd
  have h2 := hosp pos i b' b hb' hb (e11_diverge_symm hd)
  simp only [schedCost] at h1 h2
  nlinarith

theorem e11_makespan_nonneg {b : Fin n → ℝ} (hb : ∀ i, 0 ≤ b i) (x : Fin n → ℕ) :
    0 ≤ makespan b x :=
  Real.iSup_nonneg (fun i => mul_nonneg (hb i) (Nat.cast_nonneg _))

theorem e11_le_makespan (b : Fin n → ℝ) (x : Fin n → ℕ) (j : Fin n) :
    b j * (x j : ℝ) ≤ makespan b x :=
  le_ciSup (f := fun i => b i * (x i : ℝ)) (Finite.bddAbove_range _) j

theorem e11_makespan_le {b : Fin n → ℝ} {x : Fin n → ℕ} {M : ℝ} (h0 : 0 ≤ M)
    (hM : ∀ j, b j * (x j : ℝ) ≤ M) : makespan b x ≤ M :=
  Real.iSup_le hM h0

theorem e11_opt_le {m : ℕ} {b : Fin n → ℝ} (hb : ∀ i, 0 ≤ b i) (x : Fin n → ℕ)
    (hx : ∑ i, x i = m) {M : ℝ} (hM : makespan b x ≤ M) : optMakespan m b ≤ M := by
  unfold optMakespan
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨x, hx, rfl⟩) hM
  rintro _ ⟨y, _, rfl⟩
  exact e11_makespan_nonneg hb y

theorem e11_opt_pos {m : ℕ} (hm : 0 < m) {L : ℝ} (hL : 0 < L) (i₀ : Fin n) {b : Fin n → ℝ}
    (hb : ∀ i, L ≤ b i) : L ≤ optMakespan m b := by
  unfold optMakespan
  apply le_csInf
  · refine ⟨_, fun j => if j = i₀ then m else 0, ?_, rfl⟩
    simp
  · rintro _ ⟨x, hx, rfl⟩
    have : ∑ i, x i ≠ 0 := by simp only [Set.mem_setOf_eq] at hx; omega
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero this
    have h1 : (1 : ℝ) ≤ x j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    calc L ≤ b j := hb j
      _ = b j * 1 := by ring
      _ ≤ b j * x j := by
        apply mul_le_mul_of_nonneg_left h1; linarith [hb j]
      _ ≤ _ := e11_le_makespan b x j


theorem e11_opt_le_cL (c : ℕ) {L : ℝ} (hL : 0 ≤ L) (b : Fin (c ^ 2) → ℝ) (hb : ∀ i, 0 ≤ b i)
    (A : Finset (Fin (c ^ 2))) (hA : A.card = c) (hAL : ∀ j ∈ A, b j = L) :
    optMakespan (c ^ 2) b ≤ c * L := by
  classical
  refine e11_opt_le hb (fun j => if j ∈ A then c else 0) ?_ ?_
  · simp [Finset.sum_ite_mem, hA, sq]
  · apply e11_makespan_le (by positivity)
    intro j
    by_cases hj : j ∈ A
    · simp [hj, hAL j hj, mul_comm]
    · simp [hj]; positivity

theorem e11_opt_le_one (c : ℕ) (H : ℝ) (b : Fin (c ^ 2) → ℝ) (hb : ∀ i, 0 ≤ b i) (hH : 0 ≤ H)
    (hbH : ∀ j, b j = H) : optMakespan (c ^ 2) b ≤ H := by
  refine e11_opt_le hb (fun _ => 1) ?_ ?_
  · simp
  · apply e11_makespan_le hH
    intro j; simp [hbH j]

theorem e11_opt_le_all (c : ℕ) (Mid : ℝ) (i : Fin (c ^ 2)) (b : Fin (c ^ 2) → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hMid : 0 ≤ Mid) (hbi : b i = Mid) :
    optMakespan (c ^ 2) b ≤ (c ^ 2 : ℕ) * Mid := by
  classical
  refine e11_opt_le hb (fun j => if j = i then c ^ 2 else 0) ?_ ?_
  · simp
  · apply e11_makespan_le (by positivity)
    intro j
    by_cases hj : j = i
    · subst hj; simp [hbi, mul_comm]
    · simp [hj]; positivity

theorem e11_exists_A (c r : ℕ) (S : Set (Fin (c ^ 2))) (hS : S.ncard = r)
    (E : Finset (Fin (c ^ 2))) (h : c + r + E.card ≤ c ^ 2) :
    ∃ A : Finset (Fin (c ^ 2)), A.card = c ∧ ∀ j ∈ A, j ∉ S ∧ j ∉ E := by
  classical
  have hfin : S.Finite := Set.toFinite S
  have hcard : hfin.toFinset.card = r := by rw [← Set.ncard_eq_toFinset_card S hfin, hS]
  have h1 : (Finset.univ \ (hfin.toFinset ∪ E)).card ≥ c := by
    rw [Finset.card_univ_diff]
    have := Finset.card_union_le hfin.toFinset E
    simp only [Fintype.card_fin]
    omega
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq h1
  refine ⟨A, hAc, fun j hj => ?_⟩
  have := hA hj
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or,
    Set.Finite.mem_toFinset] at this
  exact this


theorem e11_compat_of (D : Fin n → Finset ℝ) (t : ImplTree n X) (H : ℝ)
    (hHD : InDomain D (fun _ => H)) (pos : List ℕ) (hpos : pos <+: path t (fun _ => H))
    (b : Fin n → ℝ) (hb : InDomain D b)
    (hS : ∀ pos', pos' <+: pos → pos' ≠ pos → ∀ j, IsDivergentNode D t pos' j → b j = H) :
    pos <+: path t b := by
  induction pos using List.reverseRecOn with
  | nil => exact List.nil_prefix
  | append_singleton pos₀ a ih =>
    have hpre : pos₀ <+: pos₀ ++ [a] := List.prefix_append _ _
    have ih' := ih (hpre.trans hpos) (fun pos' h1 _ j hj =>
      hS pos' (h1.trans hpre) (fun h => by
        have := h1.length_le
        rw [h] at this
        simp at this) j hj)
    obtain ⟨v, hv, hpv⟩ := (e11_compat_iff t pos₀ b).1 ih'
    obtain ⟨v', hv', hpv'⟩ := (e11_compat_iff t pos₀ (fun _ => H)).1 (hpre.trans hpos)
    rw [hv] at hv'
    cases hv'
    cases v with
    | leaf x =>
      exfalso
      rw [hpv'] at hpos
      have := (List.prefix_append_right_inj pos₀).1 hpos
      simp [path] at this
    | node i act ch =>
      have hact : act (b i) = act H := by
        by_cases hd : IsDivergentNode D t pos₀ i
        · rw [hS pos₀ hpre (fun h => by
            have := congrArg List.length h
            simp at this) i hd]
        · by_contra hne
          apply hd
          refine ⟨b, fun _ => H, hb, hHD, ?_, ?_, act, ch, hv, hne⟩
          · exact (e11_compat_iff t pos₀ b).2 ⟨_, hv, hpv⟩
          · exact (e11_compat_iff t pos₀ _).2 ⟨_, hv, hpv'⟩
      rw [hpv'] at hpos
      have h3 := (List.prefix_append_right_inj pos₀).1 hpos
      rw [hpv]
      refine (List.prefix_append_right_inj pos₀).2 ?_
      simp only [path] at h3 ⊢
      obtain ⟨l, hl⟩ := h3
      have ha : a = act H := (by simpa using hl : a = act H ∧ _).1
      rw [ha, ← hact]
      exact ⟨_, rfl⟩


theorem e11_kth_setup {D : Fin n → Finset ℝ} {t : ImplTree n X} {H : ℝ}
    (hHD : InDomain D (fun _ => H)) {r : ℕ} {i : Fin n} {pos : List ℕ}
    (hdiv : IsKthDiverger D t H r i pos) :
    ∃ S : Set (Fin n), S.ncard = r ∧ i ∉ S ∧
      ∀ b, InDomain D b → (∀ j ∈ S, b j = H) → Compatible t pos b := by
  refine ⟨{j | ∃ pos', pos' <+: pos ∧ pos' ≠ pos ∧ IsDivergentNode D t pos' j},
    hdiv.2.2.2, ?_, ?_⟩
  · rintro ⟨pos', h1, h2, h3⟩
    exact hdiv.2.2.1 pos' h1 h2 h3
  · intro b hb hS
    exact e11_compat_of D t H hHD pos hdiv.1 b hb
      (fun pos' h1 h2 j hj => hS j ⟨pos', h1, h2, hj⟩)

theorem e11_nums (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H) :
    (2 : ℝ) ≤ c ∧ c ≤ c ^ 2 ∧ 0 < Mid ∧ 0 < H ∧ L < Mid ∧ Mid < H ∧ (c : ℝ) ^ 2 * L ≤ Mid ∧
      (c : ℝ) ^ 2 * c * Mid ≤ H := by
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hcc : ((c ^ 2 : ℕ) : ℝ) = (c : ℝ) ^ 2 := by push_cast; ring
  rw [hcc] at hM hH
  have h4 : 4 ≤ (c : ℝ) ^ 2 := by nlinarith
  have hMid : 0 < Mid := by nlinarith
  have hHp : 0 < H := by nlinarith [mul_pos hMid (show (0:ℝ) < c by linarith)]
  refine ⟨hc', by nlinarith, hMid, hHp, by nlinarith, ?_, hM, hH⟩
  nlinarith [mul_pos hMid (show (0:ℝ) < c by linarith)]

theorem e11_force_all (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ))
    (hsched : IsSchedule (c ^ 2) (fun _ => {L, Mid, H}) t)
    (hstrict : ∀ b, InDomain (fun _ => {L, Mid, H}) b →
      makespan b (outcome t b) < c * optMakespan (c ^ 2) b)
    (y : Fin (c ^ 2) → ℝ) (hy : InDomain (fun _ => {L, Mid, H}) y) (i : Fin (c ^ 2))
    (hyi : y i = Mid) (hyH : ∀ j, j ≠ i → y j = H) : outcome t y i = c ^ 2 := by
  obtain ⟨hc', hcc, hMid, hHp, hLM, hMH, hM', hH'⟩ := e11_nums c hc L Mid H hL hM hH
  have hynn : ∀ j, 0 ≤ y j := by
    intro j
    have := hy j
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h <;> rw [h] <;> linarith
  have hOPT : optMakespan (c ^ 2) y ≤ ((c ^ 2 : ℕ) : ℝ) * Mid :=
    e11_opt_le_all c Mid i y hynn hMid.le hyi
  have hlt := hstrict y hy
  have hzero : ∀ j, j ≠ i → outcome t y j = 0 := by
    intro j hj
    by_contra hne
    have h1 : (1 : ℝ) ≤ outcome t y j := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
    have h2 := e11_le_makespan y (outcome t y) j
    rw [hyH j hj] at h2
    have h3 : (c : ℝ) * optMakespan (c ^ 2) y ≤ (c : ℝ) * (((c ^ 2 : ℕ) : ℝ) * Mid) :=
      mul_le_mul_of_nonneg_left hOPT (by linarith)
    push_cast at h3
    nlinarith
  have := hsched y hy
  rw [Finset.sum_eq_single i (fun j _ hj => hzero j hj) (by simp)] at this
  exact this


theorem e11_part1 (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ)) (p : (Fin (c ^ 2) → ℝ) → Fin (c ^ 2) → ℝ)
    (hsched : IsSchedule (c ^ 2) (fun _ => {L, Mid, H}) t)
    (hosp : IsOSP (fun _ => {L, Mid, H}) schedCost t p)
    (hstrict : ∀ b, InDomain (fun _ => {L, Mid, H}) b →
      makespan b (outcome t b) < c * optMakespan (c ^ 2) b)
    (r : ℕ) (i : Fin (c ^ 2)) (pos : List ℕ) (hr : r + 1 ≤ c ^ 2 - c + 1)
    (hdiv : IsKthDiverger (fun _ => {L, Mid, H}) t H r i pos) :
    ∃ act ch, subtreeAt t pos = some (.node i act ch) ∧ act Mid ≠ act H := by
  classical
  obtain ⟨hc', hcc, hMid, hHp, hLM, hMH, hM', hH'⟩ := e11_nums c hc L Mid H hL hM hH
  have hHD : InDomain (fun _ : Fin (c ^ 2) => ({L, Mid, H} : Finset ℝ)) (fun _ => H) := by
    intro j; simp
  obtain ⟨S, hScard, hiS, hcompat⟩ := e11_kth_setup hHD hdiv
  obtain ⟨_, ⟨b0, b0', hb0, hb0', hdv0⟩, _, _⟩ := hdiv
  obtain ⟨hc1, hc2, act, ch, hsub, hne⟩ := hdv0
  refine ⟨act, ch, hsub, ?_⟩
  intro heq
  have hLM' : act L ≠ act Mid := by
    intro h
    apply hne
    have hall : ∀ x, x ∈ ({L, Mid, H} : Finset ℝ) → act x = act Mid := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact h
      · rfl
      · exact heq.symm
    rw [hall _ (hb0 i), hall _ (hb0' i)]
  set y' : Fin (c ^ 2) → ℝ := fun j => if j = i then Mid else H with hy'
  set z : Fin (c ^ 2) → ℝ := fun j => if j ∈ S then H else L with hz
  have hy'D : InDomain (fun _ : Fin (c ^ 2) => ({L, Mid, H} : Finset ℝ)) y' := by
    intro j; simp only [hy']; split_ifs <;> simp
  have hzD : InDomain (fun _ : Fin (c ^ 2) => ({L, Mid, H} : Finset ℝ)) z := by
    intro j; simp only [hz]; split_ifs <;> simp
  have hy'i : y' i = Mid := by simp [hy']
  have hzi : z i = L := by simp [hz, hiS]
  have hy'c := hcompat y' hy'D (fun j hj => by
    have : j ≠ i := fun h => hiS (h ▸ hj)
    simp [hy', this])
  have hzc := hcompat z hzD (fun j hj => by simp [hz, hj])
  have hdiv' : DivergeAt t pos i y' z :=
    ⟨hy'c, hzc, act, ch, hsub, by rw [hy'i, hzi]; exact fun h => hLM' h.symm⟩
  have hmono := e11_weak_mono hosp hy'D hzD hdiv'
  rw [hy'i, hzi] at hmono
  have hforce := e11_force_all c hc L Mid H hL hM hH t hsched hstrict y' hy'D i hy'i
    (fun j hj => by simp [hy', hj])
  rw [hforce] at hmono
  have hge : ((c ^ 2 : ℕ) : ℝ) ≤ outcome t z i := by
    by_contra hlt
    rw [not_le] at hlt
    nlinarith
  have hcr : c + r + (∅ : Finset (Fin (c ^ 2))).card ≤ c ^ 2 := by simp; omega
  obtain ⟨A, hA, hAmem⟩ := e11_exists_A c r S hScard ∅ hcr
  have hznn : ∀ j, 0 ≤ z j := by
    intro j; simp only [hz]; split_ifs <;> linarith
  have hopt := e11_opt_le_cL c hL.le z hznn A hA (fun j hj => by simp [hz, (hAmem j hj).1])
  have hlt := hstrict z hzD
  have h2 := e11_le_makespan z (outcome t z) i
  rw [hzi] at h2
  have h3 : (c : ℝ) * optMakespan (c ^ 2) z ≤ (c : ℝ) * ((c : ℝ) * L) :=
    mul_le_mul_of_nonneg_left hopt (by linarith)
  have h4 : L * ((c ^ 2 : ℕ) : ℝ) ≤ L * outcome t z i := mul_le_mul_of_nonneg_left hge hL.le
  push_cast at h4
  nlinarith


theorem e11_part2 (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ)) (p : (Fin (c ^ 2) → ℝ) → Fin (c ^ 2) → ℝ)
    (hsched : IsSchedule (c ^ 2) (fun _ => {L, Mid, H}) t)
    (hosp : IsOSP (fun _ => {L, Mid, H}) schedCost t p)
    (hstrict : ∀ b, InDomain (fun _ => {L, Mid, H}) b →
      makespan b (outcome t b) < c * optMakespan (c ^ 2) b)
    (r : ℕ) (i : Fin (c ^ 2)) (pos : List ℕ) (hr : r + 1 ≤ c ^ 2 - c)
    (hdiv : IsKthDiverger (fun _ => {L, Mid, H}) t H r i pos) :
    ∀ x : Fin (c ^ 2) → ℝ, InDomain (fun _ => {L, Mid, H}) x → Compatible t pos x → x i = H →
      outcome t x i = 0 := by
  classical
  intro x hxD hxc hxi
  obtain ⟨hc', hcc, hMid, hHp, hLM, hMH, hM', hH'⟩ := e11_nums c hc L Mid H hL hM hH
  have hHD : InDomain (fun _ : Fin (c ^ 2) => ({L, Mid, H} : Finset ℝ)) (fun _ => H) := by
    intro j; simp
  obtain ⟨act, ch, hsub, hne⟩ := e11_part1 c hc L Mid H hL hM hH t p hsched hosp hstrict r i pos
    (by omega) hdiv
  obtain ⟨S, hScard, hiS, hcompat⟩ := e11_kth_setup hHD hdiv
  set y : Fin (c ^ 2) → ℝ := fun j => if j ∈ S then H else if j = i then Mid else L with hy
  have hyD : InDomain (fun _ : Fin (c ^ 2) => ({L, Mid, H} : Finset ℝ)) y := by
    intro j; simp only [hy]; split_ifs <;> simp
  have hyi : y i = Mid := by simp [hy, hiS]
  have hyc := hcompat y hyD (fun j hj => by simp [hy, hj])
  have hdiv' : DivergeAt t pos i x y :=
    ⟨hxc, hyc, act, ch, hsub, by rw [hxi, hyi]; exact fun h => hne h.symm⟩
  have hmono := e11_weak_mono hosp hxD hyD hdiv'
  rw [hxi, hyi] at hmono
  have hynn : ∀ j, 0 ≤ y j := by
    intro j; simp only [hy]; split_ifs <;> linarith
  have hy0 : outcome t y i = 0 := by
    by_contra hne0
    have h1 : (1 : ℝ) ≤ outcome t y i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne0
    have hcr : c + r + ({i} : Finset (Fin (c ^ 2))).card ≤ c ^ 2 := by simp; omega
    obtain ⟨A, hA, hAmem⟩ := e11_exists_A c r S hScard {i} hcr
    have hopt := e11_opt_le_cL c hL.le y hynn A hA (fun j hj => by
      have h1 := (hAmem j hj).1
      have h2 : j ≠ i := by simpa using (hAmem j hj).2
      simp [hy, h1, h2])
    have hlt := hstrict y hyD
    have h2 := e11_le_makespan y (outcome t y) i
    rw [hyi] at h2
    have h3 : (c : ℝ) * optMakespan (c ^ 2) y ≤ (c : ℝ) * ((c : ℝ) * L) :=
      mul_le_mul_of_nonneg_left hopt (by linarith)
    nlinarith
  rw [hy0, Nat.cast_zero] at hmono
  have hxnn : (outcome t x i : ℝ) ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    nlinarith
  have : outcome t x i ≤ 0 := by exact_mod_cast hxnn
  omega

theorem e11_strict_of_kapprox (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ)) (k : ℝ) (hk : k < c)
    (happrox : IsKApprox (c ^ 2) k (fun _ => {L, Mid, H}) t) :
    ∀ b, InDomain (fun _ => {L, Mid, H}) b →
      makespan b (outcome t b) < c * optMakespan (c ^ 2) b := by
  obtain ⟨hc', hcc, hMid, hHp, hLM, hMH, hM', hH'⟩ := e11_nums c hc L Mid H hL hM hH
  intro b hb
  have hbL : ∀ j, L ≤ b j := by
    intro j
    have := hb j
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h <;> rw [h] <;> linarith
  have hpos := e11_opt_pos (n := c ^ 2) (m := c ^ 2) (by positivity) hL ⟨0, by positivity⟩ hbL
  have := happrox b hb
  nlinarith

end OSPMech.SqrtLB

open OSPMech.SqrtLB

theorem solution (c : ℕ) (hc : 2 ≤ c) (L Mid H : ℝ) (hL : 0 < L)
    (hM : ((c ^ 2 : ℕ) : ℝ) * L ≤ Mid) (hH : ((c ^ 2 : ℕ) : ℝ) * c * Mid ≤ H)
    (t : ImplTree (c ^ 2) (Fin (c ^ 2) → ℕ)) (p : (Fin (c ^ 2) → ℝ) → Fin (c ^ 2) → ℝ)
    (hsched : IsSchedule (c ^ 2) (fun _ => {L, Mid, H}) t)
    (hosp : IsOSP (fun _ => {L, Mid, H}) schedCost t p)
    (k : ℝ) (hk : k < c) (happrox : IsKApprox (c ^ 2) k (fun _ => {L, Mid, H}) t)
    (r : ℕ) (i : Fin (c ^ 2)) (pos : List ℕ) (hr : r + 1 ≤ c ^ 2 - c + 1)
    (hdiv : IsKthDiverger (fun _ => {L, Mid, H}) t H r i pos) :
    ∃ act ch, subtreeAt t pos = some (.node i act ch) ∧ act Mid ≠ act H := by
  classical
  exact e11_part1 c hc L Mid H hL hM hH t p hsched hosp
    (e11_strict_of_kapprox c hc L Mid H hL hM hH t k hk happrox) r i pos (by omega) hdiv
