-- Prove2me | solution 1 for ReentrantScheduling.FBFS.busy_period_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:32:42.741445+00:00
-- url     : https://prove2.me/submissions/488e4fc4-a9c7-4047-94dc-9529f4a35fae

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants

open ReentrantScheduling.FBFS Finset

namespace FBFSBusyAux

open Classical

/-- buffers `j ≤ i` at the center of `i`. -/
noncomputable def J (L : Line) (i : Fin L.l) : Finset (Fin L.l) :=
  univ.filter (fun j => j ≤ i ∧ L.center j = L.center i)

/-- services at buffers of `J i` whose start lies in `(u, T₂]`. -/
def Svc {L : Line} (R : Run L) (i : Fin L.l) (u T₂ : ℝ) : Set (R.Part × Fin L.l) :=
  {x | x.2 ∈ J L i ∧ R.entry x.1 ≤ x.2 ∧ ∃ s : ℝ, R.start x.1 x.2 = (s : WithTop ℝ) ∧ u < s ∧ s ≤ T₂}

lemma tau_le_bar (L : Line) (j : Fin L.l) : L.τ j ≤ L.τbar := by
  unfold Line.τbar; exact le_sup' L.τ (mem_univ _)

lemma real_of_le (x : WithTop ℝ) (r : ℝ) (h : x ≤ (r : WithTop ℝ)) :
    ∃ s : ℝ, x = s ∧ s ≤ r := by
  cases x with
  | top => exact absurd h (by simp)
  | coe s => exact ⟨s, rfl, by exact_mod_cast h⟩

/-- number of grid points `k ≤ K` with `s ≤ u + k h < s + τ` is at most `τ / h + 1`. -/
lemma grid_window (K : ℕ) (u h s τ : ℝ) (hh : 0 < h) (hτ : 0 ≤ τ) :
    ((((range (K + 1)).filter (fun k : ℕ => s ≤ u + k * h ∧ u + k * h < s + τ)).card : ℕ) : ℝ)
      ≤ τ / h + 1 := by
  set F := (range (K + 1)).filter (fun k : ℕ => s ≤ u + k * h ∧ u + k * h < s + τ)
  by_cases hF : F.Nonempty
  · set k0 := F.min' hF
    have hk0 : k0 ∈ F := min'_mem F hF
    have hk0' := (mem_filter.mp hk0).2
    have hsub : F ⊆ Icc k0 (k0 + ⌊τ / h⌋₊) := by
      intro k hk
      have hkk := (mem_filter.mp hk).2
      have hle : k0 ≤ k := min'_le F k hk
      rw [mem_Icc]; refine ⟨hle, ?_⟩
      have h1 : ((k : ℝ) - k0) * h < τ := by nlinarith
      have h2 : ((k - k0 : ℕ) : ℝ) ≤ τ / h := by
        rw [Nat.cast_sub hle, le_div_iff₀ hh]; linarith
      have := Nat.le_floor h2
      omega
    have hc := card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hfl : (⌊τ / h⌋₊ : ℝ) ≤ τ / h := Nat.floor_le (div_nonneg hτ hh.le)
    have : (F.card : ℝ) ≤ ⌊τ / h⌋₊ + 1 := by
      have : F.card ≤ ⌊τ / h⌋₊ + 1 := by omega
      exact_mod_cast this
    linarith
  · rw [not_nonempty_iff_eq_empty] at hF
    rw [hF, card_empty, Nat.cast_zero]
    positivity

variable {L : Line} {R : Run L}

lemma arrive_entry (p : R.Part) : R.arrive p (R.entry p) = ((R.α p : ℝ) : WithTop ℝ) := by
  unfold Run.arrive; rw [if_pos rfl]

lemma arrive_succ (p : R.Part) (n : ℕ) (hn : n + 1 < L.l) (h : R.entry p < ⟨n + 1, hn⟩) :
    R.arrive p ⟨n + 1, hn⟩ = R.start p ⟨n, by omega⟩ + ((L.τ ⟨n, by omega⟩ : ℝ) : WithTop ℝ) := by
  unfold Run.arrive
  rw [if_neg (ne_of_lt h).symm, if_pos h]
  simp only [Nat.add_sub_cancel]

/-- arrival times are at least the release time. -/
lemma alpha_le_arrive (hR : R.Admissible L.fbfs) (p : R.Part) :
    ∀ (n : ℕ) (hn : n < L.l), R.entry p ≤ ⟨n, hn⟩ → ∀ a : ℝ,
      R.arrive p ⟨n, hn⟩ = (a : WithTop ℝ) → R.α p ≤ a := by
  intro n
  induction n with
  | zero =>
    intro hn hle a ha
    have he : (⟨0, hn⟩ : Fin L.l) = R.entry p :=
      le_antisymm (Fin.mk_le_mk.mpr (Nat.zero_le _)) hle
    rw [he, arrive_entry] at ha
    exact le_of_eq (by exact_mod_cast ha)
  | succ n ih =>
    intro hn hle a ha
    by_cases he : (⟨n + 1, hn⟩ : Fin L.l) = R.entry p
    · rw [he, arrive_entry] at ha
      exact le_of_eq (by exact_mod_cast ha)
    · have hlt : R.entry p < ⟨n + 1, hn⟩ := lt_of_le_of_ne hle (Ne.symm he)
      rw [arrive_succ p n hn hlt] at ha
      have hle' : R.entry p ≤ ⟨n, by omega⟩ := by
        rw [Fin.lt_def] at hlt; rw [Fin.le_def]; simp only at hlt ⊢; omega
      cases hs : R.start p ⟨n, by omega⟩ with
      | top => rw [hs] at ha; simp at ha
      | coe s =>
        rw [hs, ← WithTop.coe_add] at ha
        have has : s + L.τ ⟨n, by omega⟩ = a := by exact_mod_cast ha
        have hτ := L.τ_pos ⟨n, by omega⟩
        rcases hR.precedence p ⟨n, by omega⟩ hle' with h | h
        · rw [hs] at h
          obtain ⟨a', ha', ha's⟩ := real_of_le _ _ h
          have := ih (by omega) hle' a' ha'
          linarith
        · rw [hs] at h
          have h1 : -(L.τ ⟨n, by omega⟩) < s := by exact_mod_cast h.2.2.1
          rw [R.α_initial p h.1]; linarith

lemma arrive_le_start (hR : R.Admissible L.fbfs) (p : R.Part) (j : Fin L.l) (hj : R.entry p ≤ j)
    (s : ℝ) (hs : R.start p j = (s : WithTop ℝ)) (hpos : 0 < s) :
    ∃ a : ℝ, R.arrive p j = (a : WithTop ℝ) ∧ a ≤ s ∧ R.α p ≤ a := by
  rcases hR.precedence p j hj with h | h
  · rw [hs] at h
    obtain ⟨a, ha, has⟩ := real_of_le _ _ h
    exact ⟨a, ha, has, alpha_le_arrive hR p j.val j.isLt hj a ha⟩
  · rw [hs] at h
    have : s ≤ 0 := by exact_mod_cast h.2.2.2
    linarith

lemma svc_finite (hR : R.Admissible L.fbfs) (i : Fin L.l) (u T₂ : ℝ) (hu : 0 ≤ u) :
    (Svc R i u T₂).Finite := by
  apply Set.Finite.subset ((R.α_finite T₂).prod (Set.finite_univ (α := Fin L.l)))
  rintro ⟨q, j⟩ ⟨-, hentry, s, hs, hus, hsT⟩
  obtain ⟨a, -, has, hαa⟩ := arrive_le_start hR q j hentry s hs (by linarith)
  exact Set.mk_mem_prod (show R.α q ≤ T₂ by linarith) (Set.mem_univ _)

/-- Every service slot at the center of `i` at a time `v ∈ [u + τ̄, T₂]` of an `i`-busy interval
`(u, T₂]` belongs to `Svc`. -/
lemma slot_in (hR : R.Admissible L.fbfs) (i : Fin L.l) (u T₂ : ℝ) (hu : 0 ≤ u)
    (hbusy : ∀ t : ℝ, u < t → t ≤ T₂ → R.Busy i t) (v : ℝ) (hv1 : u + L.τbar ≤ v) (hv2 : v ≤ T₂)
    (x : R.Part × Fin L.l) (hx : x ∈ R.busySlots (L.center i) v) :
    x ∈ Svc R i u T₂ := by
  obtain ⟨hcx, hentry, hst, hfin⟩ := hx
  obtain ⟨s, hs, hsv⟩ := real_of_le _ _ hst
  rw [hs] at hfin
  have hfin' : v < s + L.τ x.2 := by exact_mod_cast hfin
  have hsu : u < s := by
    by_contra hcon; push Not at hcon
    linarith [tau_le_bar L x.2]
  refine ⟨?_, hentry, s, hs, hsu, by linarith⟩
  simp only [J, mem_filter, mem_univ, true_and]
  refine ⟨?_, hcx⟩
  by_contra hji; push Not at hji
  obtain ⟨q', j', hcj', hj'i, hw⟩ := hbusy s hsu (by linarith)
  exact hR.priority x.1 x.2 s (by linarith) hentry hs q' j' (by rw [hcj', hcx])
    (lt_of_le_of_lt hj'i hji) hw

/-- The counting lemma: during an `i`-busy interval `(u, T₂]`, the machines of the center of `i`
are saturated by services at buffers `j ≤ i` started in `(u, T₂]`. -/
lemma count (hR : R.Admissible L.fbfs) (i : Fin L.l) (u T₂ : ℝ) (hu : 0 ≤ u)
    (hbusy : ∀ t : ℝ, u < t → t ≤ T₂ → R.Busy i t) (hfin : (Svc R i u T₂).Finite) :
    (L.m (L.center i) : ℝ) * (T₂ - u - L.τbar) ≤ ∑ x ∈ hfin.toFinset, L.τ x.2 := by
  set X := hfin.toFinset with hX
  set W := ∑ x ∈ X, L.τ x.2 with hW
  set m : ℝ := (L.m (L.center i) : ℝ) with hm
  have hmpos : 0 < m := by rw [hm]; exact_mod_cast L.m_pos _
  have hWnn : 0 ≤ W := sum_nonneg fun x _ => (L.τ_pos x.2).le
  set D := T₂ - u - L.τbar with hD
  by_cases hDneg : D < 0
  · nlinarith
  push Not at hDneg
  -- start time of an element of X
  have hXs : ∀ x ∈ X, ∃ s : ℝ, R.start x.1 x.2 = (s : WithTop ℝ) := by
    intro x hx
    rw [hX, Set.Finite.mem_toFinset] at hx
    obtain ⟨-, -, s, hs, -⟩ := hx
    exact ⟨s, hs⟩
  -- the grid estimate, for every mesh h > 0
  have grid : ∀ h : ℝ, 0 < h → m * D < W + X.card * h := by
    intro h hh
    set K := ⌊D / h⌋₊ with hK
    have hKlt : D / h < (K : ℝ) + 1 := Nat.lt_floor_add_one _
    have hKle : (K : ℝ) * h ≤ D := by
      have := Nat.floor_le (div_nonneg hDneg hh.le)
      rw [← hK] at this; rwa [le_div_iff₀ hh] at this
    set t : ℕ → ℝ := fun k => (u + L.τbar) + k * h with ht
    have ht_lo : ∀ k, u + L.τbar ≤ t k := fun k => by
      simp only [ht]; have : (0 : ℝ) ≤ k * h := by positivity
      linarith
    have ht_hi : ∀ k ≤ K, t k ≤ T₂ := fun k hk => by
      simp only [ht]
      have : (k : ℝ) * h ≤ K * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh.le
      linarith
    have hcard : ∀ k ≤ K,
        (X.filter (fun x => R.InService x.1 x.2 (t k))).card = L.m (L.center i) := by
      intro k hk
      have hset : R.busySlots (L.center i) (t k) =
          ↑(X.filter (fun x => R.InService x.1 x.2 (t k))) := by
        ext x
        simp only [coe_filter, Set.mem_setOf_eq]
        constructor
        · intro hx
          refine ⟨?_, hx.2⟩
          rw [hX, Set.Finite.mem_toFinset]
          exact slot_in hR i u T₂ hu hbusy (t k) (ht_lo k) (ht_hi k hk) x hx
        · rintro ⟨hx, hs⟩
          rw [hX, Set.Finite.mem_toFinset] at hx
          have := hx.1
          simp only [J, mem_filter, mem_univ, true_and] at this
          exact ⟨this.2, hs⟩
      have htk : u < t k := by
        have h1 := ht_lo k
        have h2 := L.τ_pos ⟨0, L.l_pos⟩
        have h3 := tau_le_bar L ⟨0, L.l_pos⟩
        linarith
      obtain ⟨q, j, hcj, -, hw⟩ := hbusy (t k) htk (ht_hi k hk)
      have hfull := hR.nonidling (L.center i) (t k) (by linarith) ⟨q, j, hcj, hw⟩
      rw [hset, Set.encard_coe_eq_coe_finsetCard] at hfull
      exact_mod_cast hfull
    -- double counting
    have hdc : ∑ k ∈ range (K + 1), (X.filter (fun x => R.InService x.1 x.2 (t k))).card =
        ∑ x ∈ X, ((range (K + 1)).filter (fun k => R.InService x.1 x.2 (t k))).card := by
      simp only [card_filter]
      exact sum_comm
    have hlhs : ∑ k ∈ range (K + 1), (X.filter (fun x => R.InService x.1 x.2 (t k))).card =
        (K + 1) * L.m (L.center i) := by
      rw [sum_congr rfl (fun k hk => hcard k (by rw [mem_range] at hk; omega))]
      simp
    have hinner : ∀ x ∈ X,
        ((((range (K + 1)).filter (fun k => R.InService x.1 x.2 (t k))).card : ℕ) : ℝ) ≤
          L.τ x.2 / h + 1 := by
      intro x hx
      obtain ⟨s, hs⟩ := hXs x hx
      have hentry : R.entry x.1 ≤ x.2 := by
        rw [hX, Set.Finite.mem_toFinset] at hx; exact hx.2.1
      have hfeq : (range (K + 1)).filter (fun k => R.InService x.1 x.2 (t k)) =
          (range (K + 1)).filter (fun k : ℕ => s ≤ (u + L.τbar) + k * h ∧
            (u + L.τbar) + k * h < s + L.τ x.2) := by
        apply filter_congr
        intro k _
        simp only [Run.InService, hs, ht]
        constructor
        · rintro ⟨-, h1, h2⟩
          exact ⟨by exact_mod_cast h1, by rw [← WithTop.coe_add] at h2; exact_mod_cast h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨hentry, by exact_mod_cast h1, by rw [← WithTop.coe_add]; exact_mod_cast h2⟩
      rw [hfeq]
      exact grid_window K (u + L.τbar) h s (L.τ x.2) hh (L.τ_pos x.2).le
    have hmain : ((K : ℝ) + 1) * m ≤ ∑ x ∈ X, (L.τ x.2 / h + 1) := by
      have h1 : (((K + 1) * L.m (L.center i) : ℕ) : ℝ) =
          ∑ x ∈ X, ((((range (K + 1)).filter (fun k => R.InService x.1 x.2 (t k))).card : ℕ) : ℝ) := by
        rw [← hlhs, hdc]; push_cast; rfl
      have h2 := sum_le_sum hinner
      rw [hm]; push_cast at h1; linarith
    have hsum : ∑ x ∈ X, (L.τ x.2 / h + 1) = W / h + X.card := by
      rw [sum_add_distrib, ← sum_div]; simp [hW]
    rw [hsum] at hmain
    have hKh : D < ((K : ℝ) + 1) * h := by rwa [div_lt_iff₀ hh] at hKlt
    have e1 : m * D < m * (((K : ℝ) + 1) * h) := mul_lt_mul_of_pos_left hKh hmpos
    have e2 : ((K : ℝ) + 1) * m * h ≤ (W / h + X.card) * h :=
      mul_le_mul_of_nonneg_right hmain hh.le
    have e3 : (W / h + X.card) * h = W + X.card * h := by field_simp
    nlinarith
  by_contra hcon
  push Not at hcon
  set h := (m * D - W) / (X.card + 1) with hh
  have hpos : 0 < h := div_pos (by linarith) (by positivity)
  have := grid h hpos
  have hNh : (X.card : ℝ) * h ≤ (X.card + 1) * h := by nlinarith
  have : ((X.card : ℝ) + 1) * h = m * D - W := by
    rw [hh]; field_simp
  linarith

/-- the busy-period property for buffer `i` after time `T`. -/
def P (R : Run L) (lam γ : ℝ) (i : Fin L.l) (T : ℝ) : Prop :=
  ∀ T₁ T₂ : ℝ, T < T₁ → T₁ ≤ T₂ → (∀ t : ℝ, T₁ ≤ t → t ≤ T₂ → R.Busy i t) →
    T₂ - T₁ ≤ L.Gamma lam γ i

lemma den_lt (lam : ℝ) (hlam : 0 ≤ lam) (hload : L.load lam < 1) (i : Fin L.l) :
    lam * (∑ j ∈ J L i, L.τ j) / (L.m (L.center i) : ℝ) < 1 := by
  have hm : (0 : ℝ) < L.m (L.center i) := by exact_mod_cast L.m_pos _
  have h1 : (∑ j ∈ J L i, L.τ j) / (L.m (L.center i) : ℝ) ≤ L.w (L.center i) := by
    unfold Line.w
    rw [sum_div]
    apply sum_le_sum_of_subset_of_nonneg
    · intro j hj; simp only [J, mem_filter, mem_univ, true_and] at hj ⊢; exact hj.2
    · intro j _ _; exact div_nonneg (L.τ_pos j).le hm.le
  have h2 : L.w (L.center i) ≤ L.wbar := by
    unfold Line.wbar; exact le_sup' L.w (mem_univ _)
  have h3 : lam * L.wbar < 1 := hload
  have : lam * ((∑ j ∈ J L i, L.τ j) / (L.m (L.center i) : ℝ)) ≤ lam * L.wbar :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hlam
  rw [mul_div_assoc]; linarith

lemma gamma_formula (lam γ : ℝ) (i : Fin L.l) :
    L.Gamma lam γ i = (2 * L.τbar + (lam * L.GammaBar lam γ i + γ) * (∑ j ∈ J L i, L.τ j) /
      (L.m (L.center i) : ℝ)) / (1 - lam * (∑ j ∈ J L i, L.τ j) / (L.m (L.center i) : ℝ)) := by
  rw [Line.Gamma_eq]
  simp only [J]
  congr 2
  · rw [mul_sum, sum_div]; refine sum_congr rfl fun j _ => by ring
  · congr 1; rw [mul_sum, sum_div]

lemma gamma_nonneg (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1) :
    ∀ i : Fin L.l, 0 ≤ L.Gamma lam γ i := by
  have hτbar : 0 ≤ L.τbar := le_trans (L.τ_pos ⟨0, L.l_pos⟩).le (tau_le_bar L _)
  suffices H : ∀ n : ℕ, ∀ i : Fin L.l, i.val = n → 0 ≤ L.Gamma lam γ i from
    fun i => H _ i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro i hin
    have ih : ∀ k : Fin L.l, k < i → 0 ≤ L.Gamma lam γ k :=
      fun k hk => ihn k.val (by rw [← hin]; exact hk) k rfl
    rw [gamma_formula]
    have hden := den_lt lam hlam hload i
    apply div_nonneg _ (by linarith)
    have hGB : 0 ≤ L.GammaBar lam γ i := by
      unfold Line.GammaBar
      apply sum_nonneg
      intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      exact add_nonneg (ih k hk) (L.τ_pos k).le
    have hm : (0 : ℝ) < L.m (L.center i) := by exact_mod_cast L.m_pos _
    have hS : 0 ≤ ∑ j ∈ J L i, L.τ j := sum_nonneg fun j _ => (L.τ_pos j).le
    have : 0 ≤ (lam * L.GammaBar lam γ i + γ) * (∑ j ∈ J L i, L.τ j) / (L.m (L.center i) : ℝ) := by
      positivity
    linarith

lemma gammaBar_nonneg (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (i : Fin L.l) : 0 ≤ L.GammaBar lam γ i := by
  unfold Line.GammaBar
  exact sum_nonneg fun k _ => add_nonneg (gamma_nonneg lam γ hlam hγ hload k) (L.τ_pos k).le

lemma gammaBar_mono (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (k i : Fin L.l) (hki : k ≤ i) : L.GammaBar lam γ k ≤ L.GammaBar lam γ i := by
  unfold Line.GammaBar
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj; simp only [mem_filter, mem_univ, true_and] at hj ⊢; exact lt_of_lt_of_le hj hki
  · intro j _ _; exact add_nonneg (gamma_nonneg lam γ hlam hγ hload j) (L.τ_pos j).le

lemma gammaBar_succ (lam γ : ℝ) (n : ℕ) (hn : n + 1 < L.l) :
    L.GammaBar lam γ ⟨n + 1, hn⟩ = L.GammaBar lam γ ⟨n, by omega⟩ +
      (L.Gamma lam γ ⟨n, by omega⟩ + L.τ ⟨n, by omega⟩) := by
  unfold Line.GammaBar
  have : univ.filter (fun j : Fin L.l => j < ⟨n + 1, hn⟩) =
      insert ⟨n, by omega⟩ (univ.filter (fun j : Fin L.l => j < ⟨n, by omega⟩)) := by
    ext j; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.lt_def, Fin.ext_iff]; omega
  rw [this, sum_insert (by simp), add_comm]

lemma gammaBar_zero (lam γ : ℝ) (h0 : 0 < L.l) : L.GammaBar lam γ ⟨0, h0⟩ = 0 := by
  unfold Line.GammaBar
  apply sum_eq_zero
  intro j hj
  simp only [mem_filter, mem_univ, true_and, Fin.lt_def] at hj
  omega

/-- From the busy-period property at `j`, a part arriving at `b_j` after `T` starts service there
within `Γ^(j)`. -/
lemma delay_of_P (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (j : Fin L.l) (T : ℝ) (hP : P R lam γ j T) (p : R.Part) (hpj : R.entry p ≤ j) (a : ℝ)
    (ha : R.arrive p j = (a : WithTop ℝ)) (hTa : T < a) :
    ∃ s : ℝ, R.start p j = (s : WithTop ℝ) ∧ s ≤ a + L.Gamma lam γ j := by
  have hG := gamma_nonneg lam γ hlam hγ hload j
  have hbusy : ∀ t : ℝ, a ≤ t → (t : WithTop ℝ) < R.start p j → R.Busy j t := by
    intro t hat hts
    refine ⟨p, j, rfl, le_refl _, hpj, ?_, hts⟩
    rw [ha]; exact_mod_cast hat
  have key : R.start p j ≤ ((a + L.Gamma lam γ j : ℝ) : WithTop ℝ) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨T₂, hT₂1, hT₂2⟩ : ∃ T₂ : ℝ, a + L.Gamma lam γ j < T₂ ∧
        (T₂ : WithTop ℝ) < R.start p j := by
      cases hs : R.start p j with
      | top => exact ⟨a + L.Gamma lam γ j + 1, by linarith, by simp⟩
      | coe s =>
        rw [hs] at hcon
        have : a + L.Gamma lam γ j < s := by exact_mod_cast hcon
        exact ⟨(a + L.Gamma lam γ j + s) / 2, by linarith, by
          rw [WithTop.coe_lt_coe]; linarith⟩
    have := hP a T₂ hTa (by linarith) (fun t h1 h2 =>
      hbusy t h1 (lt_of_le_of_lt (by exact_mod_cast h2) hT₂2))
    linarith
  obtain ⟨s, hs, hsle⟩ := real_of_le _ _ key
  exact ⟨s, hs, hsle⟩

lemma finstart_of_P (lam γ : ℝ) (j : Fin L.l) (T : ℝ) (hP : P R lam γ j T) (p : R.Part)
    (hpj : R.entry p ≤ j) (a : ℝ) (ha : R.arrive p j = (a : WithTop ℝ)) :
    ∃ s : ℝ, R.start p j = (s : WithTop ℝ) := by
  cases hs : R.start p j with
  | coe s => exact ⟨s, rfl⟩
  | top =>
    exfalso
    set T₁ := max a (T + 1)
    have h := hP T₁ (T₁ + |L.Gamma lam γ j| + 1)
      (lt_of_lt_of_le (by linarith) (le_max_right _ _))
      (by linarith [abs_nonneg (L.Gamma lam γ j)])
      (fun t h1 _ => ⟨p, j, rfl, le_refl _, hpj, by
        rw [ha]; exact_mod_cast le_trans (le_max_left _ _) h1, by
          rw [hs]; exact WithTop.coe_lt_top t⟩)
    linarith [le_abs_self (L.Gamma lam γ j)]

/-- total work of a set of services is bounded by (number of parts) × (work per part). -/
lemma work_le (i : Fin L.l) (X : Finset (R.Part × Fin L.l)) (hX : ∀ x ∈ X, x.2 ∈ J L i) :
    ∑ x ∈ X, L.τ x.2 ≤ ((X.image Prod.fst).card : ℝ) * ∑ j ∈ J L i, L.τ j := by
  have hsub : X ⊆ (X.image Prod.fst) ×ˢ (J L i) := by
    intro x hx
    rw [mem_product]
    exact ⟨mem_image_of_mem _ hx, hX x hx⟩
  calc ∑ x ∈ X, L.τ x.2 ≤ ∑ x ∈ (X.image Prod.fst) ×ˢ (J L i), L.τ x.2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => (L.τ_pos x.2).le)
    _ = ((X.image Prod.fst).card : ℝ) * ∑ j ∈ J L i, L.τ j := by
        rw [sum_product]; simp

/-- arrivals bound for a finite set of parts. -/
lemma card_le_arrivals (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (harr : R.Arrivals lam γ)
    (Q E : Finset R.Part) (s₀ T₂ : ℝ) (hs₀ : 0 ≤ s₀) (hsT : s₀ ≤ T₂)
    (hQ : ∀ q ∈ Q, q ∈ E ∨ (¬ R.initial q ∧ s₀ < R.α q ∧ R.α q ≤ T₂)) :
    (Q.card : ℝ) ≤ E.card + (lam * (T₂ - s₀) + γ) := by
  set A := {p | ¬ R.initial p ∧ s₀ < R.α p ∧ R.α p ≤ T₂}
  have hsub : (Q : Set R.Part) ⊆ (E : Set R.Part) ∪ A := fun q hq => hQ q hq
  have h1 : (Q : Set R.Part).encard ≤ (E : Set R.Part).encard + A.encard :=
    (Set.encard_le_encard hsub).trans (Set.encard_union_le _ _)
  rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard] at h1
  have h2 := harr s₀ T₂ hs₀ hsT
  have h3 : ((Q.card : ℕ∞) : ENNReal) ≤ ((E.card : ℕ∞) : ENNReal) + ((A.encard : ℕ∞) : ENNReal) := by
    rw [← ENat.toENNReal_add]; exact ENat.toENNReal_le.mpr h1
  have h4 : ((Q.card : ℕ∞) : ENNReal) ≤ ENNReal.ofReal (E.card + (lam * (T₂ - s₀) + γ)) := by
    rw [ENNReal.ofReal_add (by positivity) (by nlinarith)]
    refine h3.trans (add_le_add ?_ h2)
    rw [ENat.toENNReal_coe, ENNReal.ofReal_natCast]
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_le_ofReal_iff (by nlinarith)] at h4
  exact h4

lemma svc_mem {i : Fin L.l} {u T₂ : ℝ} (hfin : (Svc R i u T₂).Finite) (x : R.Part × Fin L.l)
    (hx : x ∈ hfin.toFinset) : x ∈ Svc R i u T₂ := by
  rwa [Set.Finite.mem_toFinset] at hx

/-- An `i`-busy period cannot last forever. -/
lemma busy_not_forever (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) (i : Fin L.l) (a : ℝ) :
    ∃ t : ℝ, a ≤ t ∧ ¬ R.Busy i t := by
  by_contra hcon
  push Not at hcon
  set c := max a 0
  have hc0 : 0 ≤ c := le_max_right _ _
  set m : ℝ := (L.m (L.center i) : ℝ) with hm_def
  have hm : 0 < m := by rw [hm_def]; exact_mod_cast L.m_pos _
  set S := ∑ j ∈ J L i, L.τ j
  have hS : 0 ≤ S := sum_nonneg fun j _ => (L.τ_pos j).le
  have hden : lam * S / m < 1 := den_lt lam hlam hload i
  have hlS : lam * S < m := by rwa [div_lt_one hm] at hden
  set E := (R.α_finite c).toFinset
  have bound : ∀ T₂ : ℝ, c ≤ T₂ → m * (T₂ - c - L.τbar) ≤ S * (E.card + (lam * (T₂ - c) + γ)) := by
    intro T₂ hT₂
    have hb : ∀ t : ℝ, c < t → t ≤ T₂ → R.Busy i t := fun t h1 _ =>
      hcon t (le_trans (le_max_left _ _) h1.le)
    have hfin := svc_finite hR i c T₂ hc0
    have h1 := count hR i c T₂ hc0 hb hfin
    have h2 := work_le i hfin.toFinset (fun x hx => (svc_mem hfin x hx).1)
    have h3 := card_le_arrivals lam γ hlam hγ harr (hfin.toFinset.image Prod.fst) E c T₂ hc0 hT₂ (by
      intro q hq
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
      obtain ⟨hj, hentry, s, hs, hcs, hsT⟩ := svc_mem hfin x hx
      obtain ⟨a', -, has, hαa⟩ := arrive_le_start hR x.1 x.2 hentry s hs (by linarith)
      by_cases hα : R.α x.1 ≤ c
      · left; simp [E, hα]
      · right; push Not at hα
        refine ⟨fun hi => ?_, hα, by linarith⟩
        rw [R.α_initial _ hi] at hα; linarith)
    have : ((hfin.toFinset.image Prod.fst).card : ℝ) * S ≤ (E.card + (lam * (T₂ - c) + γ)) * S :=
      mul_le_mul_of_nonneg_right h3 hS
    linarith
  set B := m * L.τbar + S * (E.card + γ)
  have hB : 0 ≤ B := by
    have : 0 ≤ L.τbar := le_trans (L.τ_pos ⟨0, L.l_pos⟩).le (tau_le_bar L _)
    positivity
  set T₂ := c + B / (m - lam * S) + 1
  have hpos : 0 < m - lam * S := by linarith
  have hq : 0 ≤ B / (m - lam * S) := div_nonneg hB hpos.le
  have h := bound T₂ (by linarith)
  have e : (m - lam * S) * (B / (m - lam * S)) = B := by field_simp
  have : T₂ - c = B / (m - lam * S) + 1 := by ring
  rw [this] at h
  nlinarith

/-- every arrival at a buffer `k ≤ i` is finite, given the busy-period property below `i`. -/
lemma arr_fin (lam γ : ℝ) (i : Fin L.l) (Tf : Fin L.l → ℝ) (hTf : ∀ j < i, P R lam γ j (Tf j))
    (p : R.Part) : ∀ (n : ℕ) (hn : n < L.l), n ≤ i.val → R.entry p ≤ ⟨n, hn⟩ →
      ∃ a : ℝ, R.arrive p ⟨n, hn⟩ = (a : WithTop ℝ) := by
  intro n
  induction n with
  | zero =>
    intro hn _ hle
    have he : (⟨0, hn⟩ : Fin L.l) = R.entry p :=
      le_antisymm (Fin.mk_le_mk.mpr (Nat.zero_le _)) hle
    rw [he, arrive_entry]; exact ⟨_, rfl⟩
  | succ n ih =>
    intro hn hni hle
    by_cases he : (⟨n + 1, hn⟩ : Fin L.l) = R.entry p
    · rw [he, arrive_entry]; exact ⟨_, rfl⟩
    · have hlt : R.entry p < ⟨n + 1, hn⟩ := lt_of_le_of_ne hle (Ne.symm he)
      have hle' : R.entry p ≤ ⟨n, by omega⟩ := by
        rw [Fin.lt_def] at hlt; rw [Fin.le_def]; simp only at hlt ⊢; omega
      obtain ⟨a, ha⟩ := ih (by omega) (by omega) hle'
      obtain ⟨s, hs⟩ := finstart_of_P lam γ ⟨n, by omega⟩ _
        (hTf ⟨n, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)) p hle' a ha
      rw [arrive_succ p n hn hlt, hs, ← WithTop.coe_add]
      exact ⟨_, rfl⟩

/-- a part released after all `T^(j)`, `j < i`, reaches each `b_k`, `k ≤ i`, within `Γ̄_k`. -/
lemma travel (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (hR : R.Admissible L.fbfs) (i : Fin L.l) (Tf : Fin L.l → ℝ)
    (hTf : ∀ j < i, P R lam γ j (Tf j)) (p : R.Part) (hp : ¬ R.initial p)
    (hα : ∀ j : Fin L.l, Tf j < R.α p) :
    ∀ (n : ℕ) (hn : n < L.l), n ≤ i.val → ∃ a : ℝ, R.arrive p ⟨n, hn⟩ = (a : WithTop ℝ) ∧
      R.α p ≤ a ∧ a ≤ R.α p + L.GammaBar lam γ ⟨n, hn⟩ := by
  have hentry : R.entry p = ⟨0, L.l_pos⟩ := R.entry_released p hp
  intro n
  induction n with
  | zero =>
    intro hn _
    have : (⟨0, hn⟩ : Fin L.l) = R.entry p := by rw [hentry]
    rw [this, arrive_entry, hentry, gammaBar_zero]
    exact ⟨_, rfl, le_refl _, by linarith⟩
  | succ n ih =>
    intro hn hni
    obtain ⟨a, ha, hαa, haG⟩ := ih (by omega) (by omega)
    have hle' : R.entry p ≤ ⟨n, by omega⟩ := by rw [hentry]; exact Fin.mk_le_mk.mpr (Nat.zero_le _)
    have hlt : R.entry p < ⟨n + 1, hn⟩ := by rw [hentry, Fin.lt_def]; simp
    obtain ⟨s, hs, hsle⟩ := delay_of_P lam γ hlam hγ hload ⟨n, by omega⟩ _
      (hTf ⟨n, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)) p hle' a ha
      (lt_of_lt_of_le (hα _) hαa)
    have has : a ≤ s := by
      rcases hR.precedence p ⟨n, by omega⟩ hle' with h | h
      · rw [ha, hs] at h; exact_mod_cast h
      · exact absurd h.1 hp
    refine ⟨s + L.τ ⟨n, by omega⟩, by rw [arrive_succ p n hn hlt, hs, WithTop.coe_add], ?_, ?_⟩
    · linarith [L.τ_pos ⟨n, by omega⟩]
    · rw [gammaBar_succ]; linarith

/-- The induction step of the proof of Theorem 1. -/
lemma step (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) (i : Fin L.l) (Tf : Fin L.l → ℝ)
    (hTf : ∀ j < i, P R lam γ j (Tf j)) : ∃ T : ℝ, P R lam γ i T := by
  have hτbar : 0 < L.τbar := lt_of_lt_of_le (L.τ_pos ⟨0, L.l_pos⟩) (tau_le_bar L _)
  have hGB := gammaBar_nonneg lam γ hlam hγ hload i
  set Tstar := ∑ j : Fin L.l, |Tf j| + 1 with hTstar
  have hTs0 : 0 ≤ Tstar := by
    have : 0 ≤ ∑ j : Fin L.l, |Tf j| := sum_nonneg fun j _ => abs_nonneg _
    linarith
  have hTsj : ∀ j : Fin L.l, Tf j < Tstar := fun j => by
    have := single_le_sum (f := fun j => |Tf j|) (fun _ _ => abs_nonneg _) (mem_univ j)
    have := le_abs_self (Tf j)
    linarith
  set O := (R.α_finite Tstar).toFinset with hO
  set Told := ∑ p ∈ O, ∑ k : Fin L.l, |WithTop.untopD 0 (R.arrive p k)| with hTold
  have hTold0 : 0 ≤ Told := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have old_bound : ∀ p ∈ O, ∀ (k : Fin L.l) (a : ℝ), R.arrive p k = (a : WithTop ℝ) → a ≤ Told := by
    intro p hp k a ha
    have e1 : a = WithTop.untopD 0 (R.arrive p k) := by rw [ha, WithTop.untopD_coe]
    have e2 : |WithTop.untopD 0 (R.arrive p k)| ≤ ∑ k : Fin L.l, |WithTop.untopD 0 (R.arrive p k)| :=
      single_le_sum (f := fun k => |WithTop.untopD 0 (R.arrive p k)|) (fun _ _ => abs_nonneg _) (mem_univ k)
    have e3 : ∑ k : Fin L.l, |WithTop.untopD 0 (R.arrive p k)| ≤ Told :=
      single_le_sum (f := fun p => ∑ k : Fin L.l, |WithTop.untopD 0 (R.arrive p k)|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hp
    rw [e1]; linarith [le_abs_self (WithTop.untopD 0 (R.arrive p k))]
  set Tth := Tstar + Told + L.GammaBar lam γ i + L.τbar + 1 with hTth
  obtain ⟨t₀, ht₀, hnb⟩ := busy_not_forever lam γ hlam hγ hload hR harr i Tth
  refine ⟨t₀, ?_⟩
  intro T₁ T₂ hT₁ hT₁₂ hbusy
  set N := {t : ℝ | t₀ ≤ t ∧ t ≤ T₁ ∧ ¬ R.Busy i t} with hN
  have hNne : N.Nonempty := ⟨t₀, le_refl _, hT₁.le, hnb⟩
  have hNbdd : BddAbove N := ⟨T₁, fun t ht => ht.2.1⟩
  set c := sSup N with hc
  have hc0 : t₀ ≤ c := le_csSup hNbdd ⟨le_refl _, hT₁.le, hnb⟩
  have hcT : c ≤ T₁ := csSup_le hNne (fun t ht => ht.2.1)
  have hcpos : 0 ≤ c := by linarith
  have H1 : ∀ t : ℝ, c < t → t ≤ T₂ → R.Busy i t := by
    intro t h1 h2
    by_cases htT : T₁ ≤ t
    · exact hbusy t htT h2
    · by_contra hnb'
      have : t ∈ N := ⟨by linarith, by linarith, hnb'⟩
      have := le_csSup hNbdd this
      linarith
  have hfin := svc_finite hR i c T₂ hcpos
  have h1 := count hR i c T₂ hcpos H1 hfin
  have h2 := work_le i hfin.toFinset (fun x hx => (svc_mem hfin x hx).1)
  set s₀ := c - L.GammaBar lam γ i - L.τbar with hs₀
  have hs₀0 : 0 ≤ s₀ := by linarith
  have h3 := card_le_arrivals lam γ hlam hγ harr (hfin.toFinset.image Prod.fst) ∅ s₀ T₂ hs₀0
    (by linarith) (by
      intro q hq
      right
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
      obtain ⟨hj, hentry, s, hs, hcs, hsT⟩ := svc_mem hfin x hx
      have hj' := hj
      simp only [J, mem_filter, mem_univ, true_and] at hj'
      obtain ⟨a, ha, has, hαa⟩ := arrive_le_start hR x.1 x.2 hentry s hs (by linarith)
      have hac : c ≤ a := by
        by_contra hlt
        push Not at hlt
        obtain ⟨t, htN, hat⟩ := exists_lt_of_lt_csSup hNne hlt
        have htc : t ≤ c := le_csSup hNbdd htN
        apply htN.2.2
        refine ⟨x.1, x.2, hj'.2, hj'.1, hentry, ?_, ?_⟩
        · rw [ha]; exact_mod_cast hat.le
        · rw [hs]; exact_mod_cast (show t < s by linarith)
      have hnotold : Tstar < R.α x.1 := by
        by_contra hle
        push Not at hle
        have hmem : x.1 ∈ O := by simp [hO, hle]
        have := old_bound x.1 hmem x.2 a ha
        linarith
      have hni : ¬ R.initial x.1 := by
        intro hi; rw [R.α_initial _ hi] at hnotold; linarith
      obtain ⟨a', ha', -, ha'G⟩ := travel lam γ hlam hγ hload hR i Tf hTf x.1 hni
        (fun j => lt_trans (hTsj j) hnotold) x.2.val x.2.isLt hj'.1
      simp only [Fin.eta] at ha'
      rw [ha] at ha'
      have haa : a = a' := by exact_mod_cast ha'
      have hmono := gammaBar_mono lam γ hlam hγ hload x.2 i hj'.1
      refine ⟨hni, ?_, by linarith⟩
      linarith)
  -- algebra
  set m : ℝ := (L.m (L.center i) : ℝ) with hm_def
  have hm : 0 < m := by rw [hm_def]; exact_mod_cast L.m_pos _
  set S := ∑ j ∈ J L i, L.τ j with hS_def
  have hS : 0 ≤ S := sum_nonneg fun j _ => (L.τ_pos j).le
  have hden : lam * S / m < 1 := den_lt lam hlam hload i
  set Q := hfin.toFinset.image Prod.fst
  have hQ0 : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
  simp only [card_empty, Nat.cast_zero, zero_add] at h3
  set D := T₂ - c with hD
  set GB := L.GammaBar lam γ i
  have hT2s : T₂ - s₀ = D + GB + L.τbar := by rw [hs₀, hD]; ring
  rw [hT2s] at h3
  have key : m * (D - L.τbar) ≤ S * (lam * (D + GB + L.τbar) + γ) := by
    have : (Q.card : ℝ) * S ≤ (lam * (D + GB + L.τbar) + γ) * S := mul_le_mul_of_nonneg_right h3 hS
    have e : T₂ - c - L.τbar = D - L.τbar := by rw [hD]
    rw [e] at h1
    linarith
  rw [gamma_formula]
  have hden' : 0 < 1 - lam * S / m := by linarith
  rw [le_div_iff₀ hden']
  set cc := lam * S / m with hcc
  have hcc0 : 0 ≤ cc := by positivity
  have k2 : D - L.τbar ≤ cc * D + cc * GB + cc * L.τbar + γ * S / m := by
    have : D - L.τbar ≤ S * (lam * (D + GB + L.τbar) + γ) / m := by
      rw [le_div_iff₀ hm]; linarith
    have e : S * (lam * (D + GB + L.τbar) + γ) / m = cc * D + cc * GB + cc * L.τbar + γ * S / m := by
      rw [hcc]; field_simp
    linarith
  have k3 : cc * L.τbar ≤ L.τbar := by nlinarith
  have k4 : (lam * GB + γ) * S / m = cc * GB + γ * S / m := by
    rw [hcc]; field_simp
  have k5 : (T₂ - T₁) * (1 - cc) ≤ D * (1 - cc) :=
    mul_le_mul_of_nonneg_right (by linarith) hden'.le
  rw [k4]
  nlinarith

end FBFSBusyAux

open FBFSBusyAux in
theorem solution
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) :
    ∃ T : Fin L.l → ℝ, ∀ (i : Fin L.l) (T₁ T₂ : ℝ), T i < T₁ → T₁ ≤ T₂ →
      (∀ t : ℝ, T₁ ≤ t → t ≤ T₂ → R.Busy i t) →
      T₂ - T₁ ≤ L.Gamma lam γ i := by
  have H : ∀ n : ℕ, ∀ i : Fin L.l, i.val = n → ∃ T : ℝ, P R lam γ i T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro i hin
      have IH : ∀ j : Fin L.l, j < i → ∃ T : ℝ, P R lam γ j T :=
        fun j hj => ihn j.val (by rw [← hin]; exact hj) j rfl
      classical
      let Tf : Fin L.l → ℝ := fun j => if h : j < i then Classical.choose (IH j h) else 0
      refine step lam γ hlam hγ hload hR harr i Tf (fun j hj => ?_)
      have : Tf j = Classical.choose (IH j hj) := by simp only [Tf, dif_pos hj]
      rw [this]
      exact Classical.choose_spec (IH j hj)
  choose T hT using fun i : Fin L.l => H i.val i rfl
  exact ⟨T, fun i => hT i⟩
