-- Prove2me | solution 1 for ProcureAssort.Hotelling.hotDemand_isDemand
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T03:35:29.914336+00:00
-- url     : https://prove2.me/submissions/e5b312af-6e35-49c4-9167-1f98a26159a3

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

open ProcureAssort.Hotelling

namespace PAH

variable {n : ℕ}

/-- cost of buying from `k` for the consumer at `u`. -/
noncomputable def phi (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (k : Fin n) (u : ℝ) : ℝ :=
  p k + δ * |u - ℓ k|

lemma phi_cont (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (k : Fin n) : Continuous (phi ℓ δ p k) := by
  unfold phi; fun_prop

/-- cumulative sum `a m = Σ_{j < m} z_j`. -/
noncomputable def cum (z : Fin n → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < m), z j

lemma cum_zero (z : Fin n → ℝ) : cum z 0 = 0 := by
  unfold cum; simp

lemma cum_n (z : Fin n → ℝ) : cum z n = ∑ j, z j := by
  unfold cum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j; simp [j.isLt]

lemma cum_succ (z : Fin n → ℝ) (m : ℕ) (hm : m < n) : cum z (m + 1) = cum z m + z ⟨m, hm⟩ := by
  unfold cum
  have : Finset.univ.filter (fun j : Fin n => j.val < m + 1) =
      insert ⟨m, hm⟩ (Finset.univ.filter (fun j : Fin n => j.val < m)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

lemma lower_eq (z : Fin n → ℝ) (i : Fin n) :
    ∑ k ∈ Finset.univ.filter (· < i), z k = cum z i.val := by
  unfold cum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Fin.lt_def

lemma upper_eq (z : Fin n → ℝ) (i : Fin n) :
    ∑ k ∈ Finset.univ.filter (· ≤ i), z k = cum z (i.val + 1) := by
  unfold cum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]; omega

/-- consumer surplus as minus the total "cost" integral. -/
lemma CS_eq (ℓ : Fin n → ℝ) (δ : ℝ) (p z : Fin n → ℝ) :
    CS (hotGCS ℓ δ) z p = -∑ i : Fin n, ∫ u in (cum z i.val)..(cum z (i.val + 1)), phi ℓ δ p i u := by
  unfold CS hotGCS
  simp_rw [lower_eq, upper_eq]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hI : ∫ u in (cum z i.val)..(cum z (i.val + 1)), phi ℓ δ p i u =
      (cum z (i.val + 1) - cum z i.val) * p i + δ * ∫ u in (cum z i.val)..(cum z (i.val + 1)), |u - ℓ i| := by
    unfold phi
    rw [intervalIntegral.integral_add intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [hI, cum_succ z i.val i.isLt]
  simp only [Fin.eta]
  ring

lemma telescope_int (z : Fin n → ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    ∑ i : Fin n, ∫ u in (cum z i.val)..(cum z (i.val + 1)), g u = ∫ u in (0:ℝ)..(∑ j, z j), g u := by
  rw [Fin.sum_univ_eq_sum_range (fun m => ∫ u in (cum z m)..(cum z (m + 1)), g u) n,
    intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hg.intervalIntegrable _ _),
    cum_zero, cum_n]

/-- the lower envelope. -/
noncomputable def env (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (u : ℝ) : ℝ :=
  Finset.univ.inf' hne (fun k => phi ℓ δ p k u)

lemma env_cont (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    Continuous (env ℓ δ p hne) := by
  unfold env
  exact Continuous.finset_inf'_apply hne fun k _ => phi_cont ℓ δ p k

lemma env_le (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (k : Fin n) (u : ℝ) : env ℓ δ p hne u ≤ phi ℓ δ p k u :=
  Finset.inf'_le _ (Finset.mem_univ k)

/-- upper bound on consumer surplus for any consumption vector in the simplex. -/
lemma CS_le (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (z : Fin n → ℝ) (hz : z ∈ simplex n) :
    CS (hotGCS ℓ δ) z p ≤ -∫ u in (0:ℝ)..1, env ℓ δ p hne u := by
  rw [CS_eq, ← hz.2, ← telescope_int z _ (env_cont ℓ δ p hne), neg_le_neg_iff]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle : cum z i.val ≤ cum z (i.val + 1) := by
    rw [cum_succ z i.val i.isLt]; simp only [Fin.eta]; linarith [hz.1 i]
  exact intervalIntegral.integral_mono_on hle ((env_cont ℓ δ p hne).intervalIntegrable _ _)
    ((phi_cont ℓ δ p i).intervalIntegrable _ _) fun u _ => env_le ℓ δ p hne i u

end PAH


open ProcureAssort.Hotelling

namespace PAH

variable {n : ℕ}

section
variable (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ)

noncomputable def lbS (k : Fin n) (S : Finset (Fin n)) : ℝ :=
  if h : S.Nonempty then ℓ k - (p (S.max' h) - p k + δ * |ℓ k - ℓ (S.max' h)|) / (2 * δ) else 0

noncomputable def rbS (k : Fin n) (S : Finset (Fin n)) : ℝ :=
  if h : S.Nonempty then ℓ k + (p (S.min' h) - p k + δ * |ℓ (S.min' h) - ℓ k|) / (2 * δ) else 1

noncomputable def lb (k : Fin n) : ℝ := lbS ℓ δ p k ((hotQ ℓ δ p).filter (· < k))
noncomputable def rb (k : Fin n) : ℝ := rbS ℓ δ p k ((hotQ ℓ δ p).filter (k < ·))

noncomputable def G (S : Finset (Fin n)) : ℝ := if h : S.Nonempty then lb ℓ δ p (S.min' h) else 1

noncomputable def B (m : ℕ) : ℝ := G ℓ δ p ((hotQ ℓ δ p).filter (fun j => m ≤ j.val))

end

lemma mem_hotQ (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (i : Fin n) :
    i ∈ hotQ ℓ δ p ↔ ∀ j, p i - p j ≤ δ * |ℓ j - ℓ i| := by
  unfold hotQ; simp

lemma hotDemand_of_mem (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (k : Fin n) (hk : k ∈ hotQ ℓ δ p) :
    hotDemand ℓ δ p k = rb ℓ δ p k - lb ℓ δ p k := by
  unfold hotDemand rb lb rbS lbS
  rw [if_pos hk]
  split_ifs <;> ring

lemma hotDemand_of_not_mem (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (k : Fin n)
    (hk : k ∉ hotQ ℓ δ p) : hotDemand ℓ δ p k = 0 := by
  unfold hotDemand; rw [if_neg hk]

lemma lb_le (ℓ : Fin n → ℝ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ) (k : Fin n)
    (hk : k ∈ hotQ ℓ δ p) : lb ℓ δ p k ≤ ℓ k := by
  unfold lb lbS
  split_ifs with h
  · have hm := (Finset.mem_filter.mp (Finset.max'_mem _ h)).1
    have := (mem_hotQ ℓ δ p k).mp hk (((hotQ ℓ δ p).filter (· < k)).max' h)
    rw [abs_sub_comm] at this
    have : 0 ≤ (p (((hotQ ℓ δ p).filter (· < k)).max' h) - p k +
        δ * |ℓ k - ℓ (((hotQ ℓ δ p).filter (· < k)).max' h)|) / (2 * δ) :=
      div_nonneg (by linarith) (by linarith)
    linarith
  · exact hℓ0 k

lemma le_rb (ℓ : Fin n → ℝ) (hℓ1 : ∀ i, ℓ i ≤ 1) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ) (k : Fin n)
    (hk : k ∈ hotQ ℓ δ p) : ℓ k ≤ rb ℓ δ p k := by
  unfold rb rbS
  split_ifs with h
  · have := (mem_hotQ ℓ δ p k).mp hk (((hotQ ℓ δ p).filter (k < ·)).min' h)
    have : 0 ≤ (p (((hotQ ℓ δ p).filter (k < ·)).min' h) - p k +
        δ * |ℓ (((hotQ ℓ δ p).filter (k < ·)).min' h) - ℓ k|) / (2 * δ) :=
      div_nonneg (by linarith) (by linarith)
    linarith
  · exact hℓ1 k

lemma hotQ_nonempty (ℓ : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) : (hotQ ℓ δ p).Nonempty := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ p hne
  refine ⟨i, (mem_hotQ ℓ δ p i).mpr fun j => ?_⟩
  have := hi j (Finset.mem_univ j)
  have : 0 ≤ δ * |ℓ j - ℓ i| := mul_nonneg hδ.le (abs_nonneg _)
  linarith

lemma B_step (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ) (k : Fin n) :
    hotDemand ℓ δ p k = B ℓ δ p (k.val + 1) - B ℓ δ p k.val := by
  classical
  set Q := hotQ ℓ δ p with hQ
  by_cases hk : k ∈ Q
  · rw [hotDemand_of_mem ℓ δ p k hk]
    -- B k = lb k
    have hBk : B ℓ δ p k.val = lb ℓ δ p k := by
      unfold B G
      have hkm : k ∈ Q.filter (fun j => k.val ≤ j.val) := Finset.mem_filter.mpr ⟨hk, le_rfl⟩
      have hne : (Q.filter (fun j => k.val ≤ j.val)).Nonempty := ⟨k, hkm⟩
      rw [dif_pos hne]
      congr 1
      apply le_antisymm
      · exact Finset.min'_le _ _ hkm
      · have := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
        exact Fin.le_def.mpr this
    have hset : Q.filter (fun j => k.val + 1 ≤ j.val) = Q.filter (k < ·) := by
      refine Finset.filter_congr fun j _ => ?_
      rw [Fin.lt_def]; omega
    have hBk1 : B ℓ δ p (k.val + 1) = rb ℓ δ p k := by
      unfold B
      rw [hset]
      unfold G rb rbS
      by_cases hne : (Q.filter (k < ·)).Nonempty
      · rw [dif_pos hne, dif_pos hne]
        set R := (Q.filter (k < ·)).min' hne with hR
        have hRmem := Finset.mem_filter.mp (Finset.min'_mem _ hne)
        rw [← hR] at hRmem
        have hkm : k ∈ Q.filter (· < R) := Finset.mem_filter.mpr ⟨hk, hRmem.2⟩
        have hne2 : (Q.filter (· < R)).Nonempty := ⟨k, hkm⟩
        have hmax : (Q.filter (· < R)).max' hne2 = k := by
          apply le_antisymm
          · have hm := Finset.mem_filter.mp (Finset.max'_mem _ hne2)
            by_contra hlt
            push Not at hlt
            have : R ≤ (Q.filter (· < R)).max' hne2 :=
              Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hm.1, hlt⟩)
            exact absurd hm.2 (not_lt.mpr this)
          · exact Finset.le_max' _ _ hkm
        unfold lb lbS
        rw [dif_pos hne2, hmax]
        have hlt : ℓ k < ℓ R := hℓ hRmem.2
        rw [abs_of_pos (sub_pos.mpr hlt)]
        field_simp
        ring
      · rw [dif_neg hne, dif_neg hne]
    rw [hBk, hBk1]
  · rw [hotDemand_of_not_mem ℓ δ p k hk]
    have hset : Q.filter (fun j => k.val + 1 ≤ j.val) = Q.filter (fun j => k.val ≤ j.val) := by
      refine Finset.filter_congr fun j hj => ?_
      constructor
      · intro h; omega
      · intro h
        rcases eq_or_lt_of_le h with e | e
        · exact absurd (Fin.ext e ▸ hj) hk
        · omega
    unfold B
    rw [hset, sub_self]

lemma B_zero (ℓ : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) : B ℓ δ p 0 = 0 := by
  classical
  unfold B G
  have hset : (hotQ ℓ δ p).filter (fun j => 0 ≤ j.val) = hotQ ℓ δ p :=
    Finset.filter_true_of_mem fun j _ => Nat.zero_le _
  have hQ := hotQ_nonempty ℓ δ hδ p hne
  have hQ' : ((hotQ ℓ δ p).filter (fun j => 0 ≤ j.val)).Nonempty := by rw [hset]; exact hQ
  rw [dif_pos hQ']
  unfold lb lbS
  rw [dif_neg]
  rintro ⟨j, hj⟩
  rw [Finset.mem_filter] at hj
  have hjmem : j ∈ (hotQ ℓ δ p).filter (fun j => 0 ≤ j.val) :=
    Finset.mem_filter.mpr ⟨hj.1, Nat.zero_le _⟩
  have := Finset.min'_le _ j hjmem
  exact absurd hj.2 (not_lt.mpr this)

lemma B_n (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) : B ℓ δ p n = 1 := by
  classical
  unfold B G
  rw [dif_neg]
  rintro ⟨j, hj⟩
  rw [Finset.mem_filter] at hj
  exact absurd hj.2 (not_le.mpr j.isLt)

lemma cum_eq_B (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    ∀ m, m ≤ n → cum (hotDemand ℓ δ p) m = B ℓ δ p m := by
  intro m
  induction m with
  | zero => intro _; rw [cum_zero, B_zero ℓ δ hδ p hne]
  | succ m ih =>
    intro hm
    rw [cum_succ _ m (by omega), ih (by omega), B_step ℓ hℓ δ hδ p ⟨m, by omega⟩]
    ring

/-- the key pointwise optimality of `k` on its block, against active competitors. -/
lemma phi_le_active (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ)
    (k j : Fin n) (hk : k ∈ hotQ ℓ δ p) (hj : j ∈ hotQ ℓ δ p) (u : ℝ)
    (hl : lb ℓ δ p k ≤ u) (hr : u ≤ rb ℓ δ p k) : phi ℓ δ p k u ≤ phi ℓ δ p j u := by
  classical
  set Q := hotQ ℓ δ p with hQ
  have hkQ := (mem_hotQ ℓ δ p k).mp hk
  unfold phi
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · -- competitor on the left
    have hjm : j ∈ Q.filter (· < k) := Finset.mem_filter.mpr ⟨hj, hjk⟩
    have hne : (Q.filter (· < k)).Nonempty := ⟨j, hjm⟩
    set L := (Q.filter (· < k)).max' hne with hL
    have hLm := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    rw [← hL] at hLm
    have hjL : j ≤ L := Finset.le_max' _ _ hjm
    have hLQ := (mem_hotQ ℓ δ p L).mp hLm.1 j
    have hkL := hkQ L
    have h1 : ℓ L < ℓ k := hℓ hLm.2
    have h2 : ℓ j ≤ ℓ L := hℓ.monotone hjL
    rw [abs_of_nonpos (by linarith : ℓ j - ℓ L ≤ 0)] at hLQ
    rw [abs_of_neg (by linarith : ℓ L - ℓ k < 0)] at hkL
    have hlb : lb ℓ δ p k = ℓ k - (p L - p k + δ * (ℓ k - ℓ L)) / (2 * δ) := by
      unfold lb lbS
      rw [dif_pos hne, ← hL, abs_of_pos (by linarith : 0 < ℓ k - ℓ L)]
    rw [hlb] at hl
    have hl' : 2 * δ * (ℓ k - u) ≤ p L - p k + δ * (ℓ k - ℓ L) := by
      have : (ℓ k - u) ≤ (p L - p k + δ * (ℓ k - ℓ L)) / (2 * δ) := by linarith
      rwa [le_div_iff₀ (by linarith), mul_comm] at this
    have hj' : δ * (u - ℓ j) ≤ δ * |u - ℓ j| := mul_le_mul_of_nonneg_left (le_abs_self _) hδ.le
    rcases le_total u (ℓ k) with hu | hu
    · rw [abs_of_nonpos (by linarith : u - ℓ k ≤ 0)]
      nlinarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ u - ℓ k)]
      nlinarith
  · subst hjk; exact le_rfl
  · -- competitor on the right
    have hjm : j ∈ Q.filter (k < ·) := Finset.mem_filter.mpr ⟨hj, hjk⟩
    have hne : (Q.filter (k < ·)).Nonempty := ⟨j, hjm⟩
    set R := (Q.filter (k < ·)).min' hne with hR
    have hRm := Finset.mem_filter.mp (Finset.min'_mem _ hne)
    rw [← hR] at hRm
    have hRj : R ≤ j := Finset.min'_le _ _ hjm
    have hRQ := (mem_hotQ ℓ δ p R).mp hRm.1 j
    have hkR := hkQ R
    have h1 : ℓ k < ℓ R := hℓ hRm.2
    have h2 : ℓ R ≤ ℓ j := hℓ.monotone hRj
    rw [abs_of_nonneg (by linarith : 0 ≤ ℓ j - ℓ R)] at hRQ
    rw [abs_of_pos (by linarith : 0 < ℓ R - ℓ k)] at hkR
    have hrb : rb ℓ δ p k = ℓ k + (p R - p k + δ * (ℓ R - ℓ k)) / (2 * δ) := by
      unfold rb rbS
      rw [dif_pos hne, ← hR, abs_of_pos (by linarith : 0 < ℓ R - ℓ k)]
    rw [hrb] at hr
    have hr' : 2 * δ * (u - ℓ k) ≤ p R - p k + δ * (ℓ R - ℓ k) := by
      have : (u - ℓ k) ≤ (p R - p k + δ * (ℓ R - ℓ k)) / (2 * δ) := by linarith
      rwa [le_div_iff₀ (by linarith), mul_comm] at this
    have hj' : δ * (ℓ j - u) ≤ δ * |u - ℓ j| := by
      rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left (le_abs_self _) hδ.le
    rcases le_total u (ℓ k) with hu | hu
    · rw [abs_of_nonpos (by linarith : u - ℓ k ≤ 0)]
      nlinarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ u - ℓ k)]
      nlinarith

lemma phi_le (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (k j : Fin n) (hk : k ∈ hotQ ℓ δ p) (u : ℝ)
    (hl : lb ℓ δ p k ≤ u) (hr : u ≤ rb ℓ δ p k) : phi ℓ δ p k u ≤ phi ℓ δ p j u := by
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ (fun j => phi ℓ δ p j u) hne
  have hmQ : m ∈ hotQ ℓ δ p := by
    rw [mem_hotQ]
    intro i
    by_contra hlt
    push Not at hlt
    have h1 := hm i (Finset.mem_univ i)
    have h2 : |u - ℓ i| ≤ |u - ℓ m| + |ℓ i - ℓ m| := by
      calc |u - ℓ i| = |(u - ℓ m) - (ℓ i - ℓ m)| := by ring_nf
        _ ≤ |u - ℓ m| + |ℓ i - ℓ m| := abs_sub _ _
    unfold phi at h1
    nlinarith
  exact (phi_le_active ℓ hℓ δ hδ p k m hk hmQ u hl hr).trans (hm j (Finset.mem_univ j))

theorem hotDemand_isDemand' (n : ℕ) (hn : 2 ≤ n)
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ) :
    IsDemand (hotGCS ℓ δ) (simplex n) Finset.univ p (hotDemand ℓ δ p) := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set y := hotDemand ℓ δ p with hy
  have hnn : ∀ k, 0 ≤ y k := by
    intro k
    by_cases hk : k ∈ hotQ ℓ δ p
    · rw [hy, hotDemand_of_mem ℓ δ p k hk]
      linarith [lb_le ℓ hℓ0 δ hδ p k hk, le_rb ℓ hℓ1 δ hδ p k hk]
    · rw [hy, hotDemand_of_not_mem ℓ δ p k hk]
  have hsum : ∑ k, y k = 1 := by
    rw [← cum_n, cum_eq_B ℓ hℓ δ hδ p hne n le_rfl, B_n]
  have hysim : y ∈ simplex n := ⟨hnn, hsum⟩
  have hCSy : CS (hotGCS ℓ δ) y p = -∫ u in (0:ℝ)..1, env ℓ δ p hne u := by
    rw [CS_eq, ← hsum, ← telescope_int y _ (env_cont ℓ δ p hne)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cum_eq_B ℓ hℓ δ hδ p hne _ (by omega), cum_eq_B ℓ hℓ δ hδ p hne _ (by omega)]
    by_cases hk : k ∈ hotQ ℓ δ p
    · have hstep := B_step ℓ hℓ δ hδ p k
      rw [hotDemand_of_mem ℓ δ p k hk] at hstep
      -- identify the block
      have hBk : B ℓ δ p k.val = lb ℓ δ p k := by
        have := cum_eq_B ℓ hℓ δ hδ p hne k.val (by omega)
        unfold B G
        have hkm : k ∈ (hotQ ℓ δ p).filter (fun j => k.val ≤ j.val) :=
          Finset.mem_filter.mpr ⟨hk, le_rfl⟩
        have hne' : ((hotQ ℓ δ p).filter (fun j => k.val ≤ j.val)).Nonempty := ⟨k, hkm⟩
        rw [dif_pos hne']
        congr 1
        apply le_antisymm
        · exact Finset.min'_le _ _ hkm
        · exact Fin.le_def.mpr (Finset.mem_filter.mp (Finset.min'_mem _ hne')).2
      have hBk1 : B ℓ δ p (k.val + 1) = rb ℓ δ p k := by linarith
      rw [hBk, hBk1]
      have hle : lb ℓ δ p k ≤ rb ℓ δ p k :=
        (lb_le ℓ hℓ0 δ hδ p k hk).trans (le_rb ℓ hℓ1 δ hδ p k hk)
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le hle] at hu
      exact le_antisymm (Finset.le_inf' _ _ fun j _ => phi_le ℓ hℓ δ hδ p hne k j hk u hu.1 hu.2)
        (env_le ℓ δ p hne k u)
    · have hstep := B_step ℓ hℓ δ hδ p k
      rw [hotDemand_of_not_mem ℓ δ p k hk] at hstep
      have : B ℓ δ p (k.val + 1) = B ℓ δ p k.val := by linarith
      rw [this, intervalIntegral.integral_same, intervalIntegral.integral_same]
  refine ⟨hysim, fun i hi => absurd (Finset.mem_univ i) hi, fun z hz _ => ?_⟩
  rw [hCSy]
  exact CS_le ℓ δ p hne z hz

end PAH


open ProcureAssort.Hotelling

theorem solution
    (n : ℕ) (hn : 2 ≤ n)
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (p : Fin n → ℝ) :
    IsDemand (hotGCS ℓ δ) (simplex n) Finset.univ p (hotDemand ℓ δ p) :=
  PAH.hotDemand_isDemand' n hn ℓ hℓ hℓ0 hℓ1 δ hδ p
