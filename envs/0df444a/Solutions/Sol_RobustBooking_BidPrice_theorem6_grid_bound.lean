-- Prove2me | solution 1 for RobustBooking.BidPrice.theorem6_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:41:00.305986+00:00
-- url     : https://prove2.me/submissions/2573c70a-88e0-4a76-af74-8cef47014700

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls

open MeasureTheory

namespace Aux_RB_grid

open RobustBooking.BidPrice

noncomputable def fGrid (fmin fmax : ℝ) (m i : ℕ) : ℝ :=
  fmax * discountRatio fmin fmax ^ (((i : ℝ) - 1) / ((m : ℝ) - 1))

lemma discountRatio_bounds (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) :
    0 < discountRatio fmin fmax ∧ discountRatio fmin fmax < 1 := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  unfold discountRatio
  exact ⟨div_pos hfmin hfmax, (div_lt_one hfmax).mpr hf⟩

lemma fGrid_pos (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (m i : ℕ) :
    0 < fGrid fmin fmax m i := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  have hr : 0 < discountRatio fmin fmax := (discountRatio_bounds fmin fmax hfmin hf).1
  exact mul_pos hfmax (Real.rpow_pos_of_pos hr _)

lemma fGrid_one (fmin fmax : ℝ) (m : ℕ) : fGrid fmin fmax m 1 = fmax := by
  unfold fGrid
  simp

lemma fGrid_anti (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (m : ℕ) (hm : 2 ≤ m)
    {i j : ℕ} (hij : i ≤ j) : fGrid fmin fmax m j ≤ fGrid fmin fmax m i := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  obtain ⟨hr0, hr1⟩ := discountRatio_bounds fmin fmax hfmin hf
  have hm1 : 0 < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.ofNat_le_cast.mpr hm
    linarith
  have hexp : ((i : ℝ) - 1) / ((m : ℝ) - 1) ≤ ((j : ℝ) - 1) / ((m : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ hm1.le
    have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    linarith
  unfold fGrid
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hexp) hfmax.le

lemma fGrid_mem_gridFares (fmin fmax : ℝ) (m : ℕ) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) :
    fGrid fmin fmax m i ∈ gridFares fmin fmax m :=
  ⟨i, hi1, him, rfl⟩

lemma gridFares_bounds (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (m : ℕ) (hm : 2 ≤ m)
    {f : ℝ} (hf_mem : f ∈ gridFares fmin fmax m) : 0 ≤ f ∧ f ≤ fmax := by
  rcases hf_mem with ⟨i, hi1, _, rfl⟩
  change 0 ≤ fGrid fmin fmax m i ∧ fGrid fmin fmax m i ≤ fmax
  refine ⟨(fGrid_pos fmin fmax hfmin hf m i).le, ?_⟩
  calc fGrid fmin fmax m i
      ≤ fGrid fmin fmax m 1 := fGrid_anti fmin fmax hfmin hf m hm hi1
    _ = fmax := fGrid_one fmin fmax m

lemma fGrid_ratio (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (m : ℕ)
    {i : ℕ} (hi2 : 2 ≤ i) :
    fGrid fmin fmax m i / fGrid fmin fmax m (i - 1) =
      discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1)) := by
  have hr : 0 < discountRatio fmin fmax := (discountRatio_bounds fmin fmax hfmin hf).1
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]
  have hexp : ((i : ℝ) - 1) / ((m : ℝ) - 1) =
      (((i - 1 : ℕ) : ℝ) - 1) / ((m : ℝ) - 1) + 1 / ((m : ℝ) - 1) := by
    rw [hcast]; ring
  have hmul : fGrid fmin fmax m i =
      fGrid fmin fmax m (i - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1)) := by
    unfold fGrid
    rw [hexp, Real.rpow_add hr, ← mul_assoc]
  have hpos : fGrid fmin fmax m (i - 1) ≠ 0 := (fGrid_pos fmin fmax hfmin hf m (i - 1)).ne'
  rw [hmul, mul_div_cancel_left₀ _ hpos]

lemma weight_grid_pos (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (m : ℕ) (hm : 2 ≤ m) :
    0 < 1 - discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1)) := by
  obtain ⟨hr0, hr1⟩ := discountRatio_bounds fmin fmax hfmin hf
  have hm1 : 0 < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := Nat.ofNat_le_cast.mpr hm
    linarith
  have hpow : discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1)) < 1 :=
    Real.rpow_lt_one hr0.le hr1 (one_div_pos.mpr hm1)
  linarith

noncomputable def DeltaGrid (fmin fmax : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) - ((m : ℝ) - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1))

lemma deltaGrid_eq_sum (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (m : ℕ) (hm : 2 ≤ m) :
    DeltaGrid fmin fmax m =
      1 + ∑ i ∈ Finset.Icc 2 m, (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) := by
  have hcongr : ∑ i ∈ Finset.Icc 2 m, (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) =
      ∑ _i ∈ Finset.Icc 2 m, (1 - discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1))) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    rw [fGrid_ratio fmin fmax hfmin hf m hi.1]
  rw [hcongr, Finset.sum_const, Nat.card_Icc]
  have hcard : m + 1 - 2 = m - 1 := by omega
  rw [hcard, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  unfold DeltaGrid
  ring

lemma deltaGrid_pos (fmin fmax : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (m : ℕ) (hm : 2 ≤ m) : 0 < DeltaGrid fmin fmax m := by
  rw [deltaGrid_eq_sum fmin fmax hfmin hf m hm]
  have hsum : 0 ≤ ∑ i ∈ Finset.Icc 2 m, (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [fGrid_ratio fmin fmax hfmin hf m hi.1]
    exact (weight_grid_pos fmin fmax hfmin hf m hm).le
  linarith

noncomputable def instDown (fmin fmax n : ℝ) (hn : 0 < n) (m i : ℕ) : ℕ → List Request
  | 0 => []
  | k + 1 => instDown fmin fmax n hn m (i + 1) k ++ [⟨fGrid fmin fmax m i, n, hn⟩]

noncomputable def instClass (fmin fmax n : ℝ) (hn : 0 < n) (m i : ℕ) : List Request :=
  instDown fmin fmax n hn m i (m + 1 - i)

lemma instClass_top (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) :
    instClass fmin fmax n hn m (m + 1) = [] := by
  simp [instClass, instDown]

lemma instClass_step (fmin fmax n : ℝ) (hn : 0 < n) (m i : ℕ) (hi : i ≤ m) :
    instClass fmin fmax n hn m i =
      instClass fmin fmax n hn m (i + 1) ++ [⟨fGrid fmin fmax m i, n, hn⟩] := by
  have h : m + 1 - i = (m + 1 - (i + 1)) + 1 := by omega
  rw [instClass, h, instDown, ← instClass]

lemma mem_instDown (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) :
    ∀ (k i : ℕ) (r : Request),
      r ∈ instDown fmin fmax n hn m i k →
      (∃ j, i ≤ j ∧ j < i + k ∧ r.fare = fGrid fmin fmax m j) ∧ r.qty = n
  | 0, i, r, hr => by simp [instDown] at hr
  | k + 1, i, r, hr => by
    simp only [instDown, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · obtain ⟨⟨j, hj1, hj2, hfare⟩, hqty⟩ := mem_instDown fmin fmax n hn m k (i + 1) r hr
      exact ⟨⟨j, by omega, by omega, hfare⟩, hqty⟩
    · exact ⟨⟨i, le_rfl, by omega, rfl⟩, rfl⟩

lemma mem_instClass (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) {i : ℕ} (him : i ≤ m) {r : Request}
    (hr : r ∈ instClass fmin fmax n hn m i) :
    (∃ j, i ≤ j ∧ j ≤ m ∧ r.fare = fGrid fmin fmax m j) ∧ r.qty = n := by
  obtain ⟨⟨j, hj1, hj2, hfare⟩, hqty⟩ := mem_instDown fmin fmax n hn m (m + 1 - i) i r hr
  exact ⟨⟨j, hj1, by omega, hfare⟩, hqty⟩

lemma instClass_faresIn (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) :
    FaresIn (gridFares fmin fmax m) (instClass fmin fmax n hn m i) := by
  intro r hr
  obtain ⟨⟨j, hj1, hj2, hfare⟩, _⟩ := mem_instClass fmin fmax n hn m him hr
  rw [hfare]
  exact fGrid_mem_gridFares fmin fmax m (le_trans hi1 hj1) hj2

lemma offlineOpt_instClass (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (m : ℕ) (hm : 2 ≤ m) {i : ℕ} (_hi1 : 1 ≤ i) (him : i ≤ m) :
    offlineOpt n (instClass fmin fmax n hn m i) = fGrid fmin fmax m i * n := by
  have hfi : 0 < fGrid fmin fmax m i := fGrid_pos fmin fmax hfmin hf m i
  have hL : ∀ r ∈ instClass fmin fmax n hn m (i + 1),
      r.fare ≤ fGrid fmin fmax m i ∧ r.qty = n := by
    intro r hr
    by_cases hi' : i + 1 ≤ m
    · obtain ⟨⟨j, hj1, _, hfare⟩, hqty⟩ := mem_instClass fmin fmax n hn m hi' hr
      rw [hfare]
      exact ⟨fGrid_anti fmin fmax hfmin hf m hm (by omega), hqty⟩
    · have hm_eq : i + 1 = m + 1 := by omega
      rw [hm_eq, instClass_top] at hr
      simp at hr
  rw [instClass_step fmin fmax n hn m i him]
  set L := instClass fmin fmax n hn m (i + 1)
  set qLast : Request := ⟨fGrid fmin fmax m i, n, hn⟩
  set I := L ++ [qLast]
  have hlen : I.length = L.length + 1 := by simp [I]
  let k0 : Fin I.length := ⟨L.length, by rw [hlen]; omega⟩
  have hget_k0 : I.get k0 = qLast := by
    simp [I, k0, List.getElem_append_right]
  unfold offlineOpt
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun k => if k = k0 then n else 0, ⟨fun k => ?_, ?_⟩, ?_⟩
    · have hmem : I.get k ∈ I := List.get_mem I k
      have hqty : (I.get k).qty = n := by
        simp only [I, List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact (hL _ hmem).2
        · rw [hmem]
      rw [hqty]
      dsimp only
      split_ifs
      · exact ⟨hn.le, le_rfl⟩
      · exact ⟨le_rfl, hn.le⟩
    · simp [Finset.sum_ite_eq']
    · simp [mul_ite, Finset.sum_ite_eq', -List.get_eq_getElem, hget_k0, qLast]
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    calc ∑ k : Fin I.length, (I.get k).fare * x k
        ≤ ∑ k : Fin I.length, fGrid fmin fmax m i * x k := by
          refine Finset.sum_le_sum fun k _ => ?_
          apply mul_le_mul_of_nonneg_right _ (hx1 k).1
          have hmem : I.get k ∈ I := List.get_mem I k
          simp only [I, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hmem | hmem
          · exact (hL _ hmem).1
          · rw [hmem]
      _ = fGrid fmin fmax m i * ∑ k : Fin I.length, x k := (Finset.mul_sum _ _ _).symm
      _ ≤ fGrid fmin fmax m i * n := mul_le_mul_of_nonneg_left hx2 hfi.le

lemma runFrom_append (P : DetPolicy) (n : ℝ) :
    ∀ (I₁ I₂ : List Request) (hist : List (Request × ℝ)),
      runFrom P n hist (I₁ ++ I₂) = runFrom P n (runFrom P n hist I₁) I₂
  | [], I₂, hist => rfl
  | q :: qs, I₂, hist => by
    simp only [List.cons_append, runFrom]
    exact runFrom_append P n qs I₂ _

lemma runFrom_bounds (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (m : ℕ) (hm : 2 ≤ m) (P : DetPolicy) :
    ∀ (I : List Request) (hist : List (Request × ℝ)),
      FaresIn (gridFares fmin fmax m) I →
      (∀ e ∈ hist, 0 ≤ e.1.fare ∧ e.1.fare ≤ fmax ∧ 0 ≤ e.2) →
      acceptedTotal hist ≤ n →
      (∀ e ∈ runFrom P n hist I, 0 ≤ e.1.fare ∧ e.1.fare ≤ fmax ∧ 0 ≤ e.2) ∧
      acceptedTotal (runFrom P n hist I) ≤ n
  | [], hist, _, hhist, hsum => ⟨hhist, hsum⟩
  | q :: qs, hist, hI, hhist, hsum => by
    have hq_mem : q.fare ∈ gridFares fmin fmax m := hI q List.mem_cons_self
    obtain ⟨hq0, hqmax⟩ := gridFares_bounds fmin fmax hfmin hf m hm hq_mem
    have hqs : FaresIn (gridFares fmin fmax m) qs :=
      fun r hr => hI r (List.mem_cons_of_mem _ hr)
    set a := max 0 (min (P.decide hist q) (min q.qty (n - acceptedTotal hist)))
    have ha0 : 0 ≤ a := le_max_left 0 _
    have ha_le : a ≤ n - acceptedTotal hist := by
      dsimp [a]
      exact max_le (by linarith) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hhist' : ∀ e ∈ hist ++ [(q, a)], 0 ≤ e.1.fare ∧ e.1.fare ≤ fmax ∧ 0 ≤ e.2 := by
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hhist e he
      · exact ⟨hq0, hqmax, ha0⟩
    have hsum' : acceptedTotal (hist ++ [(q, a)]) ≤ n := by
      unfold acceptedTotal at ha_le hsum ⊢
      rw [List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      linarith
    exact runFrom_bounds fmin fmax n hfmin hf m hm P qs (hist ++ [(q, a)]) hqs hhist' hsum'

lemma list_sum_rev_bounds (fmax : ℝ) :
    ∀ (L : List (Request × ℝ)),
      (∀ e ∈ L, 0 ≤ e.1.fare ∧ e.1.fare ≤ fmax ∧ 0 ≤ e.2) →
      0 ≤ (L.map fun e => e.1.fare * e.2).sum ∧
      (L.map fun e => e.1.fare * e.2).sum ≤ fmax * (L.map Prod.snd).sum
  | [], _ => by simp
  | e :: es, hL => by
    have he := hL e List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := list_sum_rev_bounds fmax es (fun x hx => hL x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨add_nonneg (mul_nonneg he.1 he.2.2) ih1, ?_⟩
    have hmul : e.1.fare * e.2 ≤ fmax * e.2 := mul_le_mul_of_nonneg_right he.2.1 he.2.2
    linarith

lemma revenue_bounds (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    (m : ℕ) (hm : 2 ≤ m) (P : DetPolicy) {I : List Request}
    (hI : FaresIn (gridFares fmin fmax m) I) :
    0 ≤ revenue n P I ∧ revenue n P I ≤ fmax * n := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  obtain ⟨h1, h2⟩ := runFrom_bounds fmin fmax n hfmin hf m hm P I [] hI
    (by simp) (by simp [acceptedTotal, hn.le])
  obtain ⟨r1, r2⟩ := list_sum_rev_bounds fmax (run P n I) h1
  unfold revenue
  unfold acceptedTotal at h2
  exact ⟨r1, le_trans r2 (mul_le_mul_of_nonneg_left h2 hfmax.le)⟩

noncomputable def uClass (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) (P : DetPolicy) (i : ℕ) : ℝ :=
  acceptedTotal (run P n (instClass fmin fmax n hn m i))

noncomputable def RClass (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) (P : DetPolicy) (i : ℕ) : ℝ :=
  revenue n P (instClass fmin fmax n hn m i)

lemma uClass_top (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) (P : DetPolicy) :
    uClass fmin fmax n hn m P (m + 1) = 0 := by
  simp [uClass, acceptedTotal, instClass_top, run, runFrom]

lemma RClass_top (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) (P : DetPolicy) :
    RClass fmin fmax n hn m P (m + 1) = 0 := by
  simp [RClass, revenue, instClass_top, run, runFrom]

lemma uClass_one_le_n (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax) (hn : 0 < n)
    (m : ℕ) (hm : 2 ≤ m) (P : DetPolicy) :
    uClass fmin fmax n hn m P 1 ≤ n := by
  have hI := instClass_faresIn fmin fmax n hn m le_rfl (by omega)
  exact (runFrom_bounds fmin fmax n hfmin hf m hm P (instClass fmin fmax n hn m 1) [] hI
    (by simp) (by simp [acceptedTotal, hn.le])).2

lemma RClass_step (fmin fmax n : ℝ) (hn : 0 < n) (m : ℕ) (P : DetPolicy) {i : ℕ} (him : i ≤ m) :
    RClass fmin fmax n hn m P i =
      RClass fmin fmax n hn m P (i + 1) +
        fGrid fmin fmax m i * (uClass fmin fmax n hn m P i - uClass fmin fmax n hn m P (i + 1)) := by
  unfold RClass revenue uClass acceptedTotal run
  rw [instClass_step fmin fmax n hn m i him, runFrom_append]
  set hist := runFrom P n [] (instClass fmin fmax n hn m (i + 1))
  simp only [runFrom, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

lemma telescope_det (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (m : ℕ) (P : DetPolicy) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m →
      RClass fmin fmax n hn m P 1 / fGrid fmin fmax m 1 +
        ∑ i ∈ Finset.Icc 2 k,
          (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
            (RClass fmin fmax n hn m P i / fGrid fmin fmax m i) =
      uClass fmin fmax n hn m P 1 - uClass fmin fmax n hn m P (k + 1) +
        RClass fmin fmax n hn m P (k + 1) / fGrid fmin fmax m k
  | 0, hk1, _ => by omega
  | 1, _, h1m => by
    have hf1 : fGrid fmin fmax m 1 ≠ 0 := (fGrid_pos fmin fmax hfmin hf m 1).ne'
    have hstep := RClass_step fmin fmax n hn m P h1m
    have hIcc : (Finset.Icc 2 1 : Finset ℕ) = ∅ := rfl
    rw [hIcc, Finset.sum_empty, add_zero, hstep]
    field_simp
    ring
  | k + 1, _, hkm => by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hf1 : fGrid fmin fmax m 1 ≠ 0 := (fGrid_pos fmin fmax hfmin hf m 1).ne'
      have hstep := RClass_step fmin fmax n hn m P hkm
      have hIcc : (Finset.Icc 2 1 : Finset ℕ) = ∅ := rfl
      rw [hIcc, Finset.sum_empty, add_zero, hstep]
      field_simp
      ring
    · have ih := telescope_det fmin fmax n hfmin hf hn m P k hkpos (by omega)
      rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel, ← add_assoc, ih]
      have hfk : fGrid fmin fmax m k ≠ 0 := (fGrid_pos fmin fmax hfmin hf m k).ne'
      have hfk1 : fGrid fmin fmax m (k + 1) ≠ 0 := (fGrid_pos fmin fmax hfmin hf m (k + 1)).ne'
      have hstep := RClass_step fmin fmax n hn m P hkm
      have hcancel :
          (1 - fGrid fmin fmax m (k + 1) / fGrid fmin fmax m k) *
              (RClass fmin fmax n hn m P (k + 1) / fGrid fmin fmax m (k + 1)) =
            RClass fmin fmax n hn m P (k + 1) / fGrid fmin fmax m (k + 1) -
              RClass fmin fmax n hn m P (k + 1) / fGrid fmin fmax m k := by
        field_simp
      have hdiv :
          RClass fmin fmax n hn m P (k + 1) / fGrid fmin fmax m (k + 1) =
            RClass fmin fmax n hn m P (k + 1 + 1) / fGrid fmin fmax m (k + 1) +
              (uClass fmin fmax n hn m P (k + 1) - uClass fmin fmax n hn m P (k + 1 + 1)) := by
        rw [hstep]
        field_simp
      linarith

lemma telescope_det_full (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (m : ℕ) (hm : 2 ≤ m) (P : DetPolicy) :
    RClass fmin fmax n hn m P 1 / fGrid fmin fmax m 1 +
      ∑ i ∈ Finset.Icc 2 m,
        (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
          (RClass fmin fmax n hn m P i / fGrid fmin fmax m i) ≤ n := by
  have h := telescope_det fmin fmax n hfmin hf hn m P m (by omega) le_rfl
  rw [uClass_top, RClass_top, sub_zero, zero_div, add_zero] at h
  rw [h]
  exact uClass_one_le_n fmin fmax n hfmin hf hn m hm P

lemma sum_Icc_int_eq (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (m : ℕ) (hm : 2 ≤ m)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy)
    (hA : ∀ I : List Request, FaresIn (gridFares fmin fmax m) I →
      Measurable fun ω => revenue n (A ω) I) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m →
      Integrable (fun ω => RClass fmin fmax n hn m (A ω) 1 / fGrid fmin fmax m 1 +
        ∑ i ∈ Finset.Icc 2 k,
          (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
            (RClass fmin fmax n hn m (A ω) i / fGrid fmin fmax m i)) μ ∧
      (∫ ω, (RClass fmin fmax n hn m (A ω) 1 / fGrid fmin fmax m 1 +
        ∑ i ∈ Finset.Icc 2 k,
          (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
            (RClass fmin fmax n hn m (A ω) i / fGrid fmin fmax m i)) ∂μ) =
        (∫ ω, RClass fmin fmax n hn m (A ω) 1 ∂μ) / fGrid fmin fmax m 1 +
        ∑ i ∈ Finset.Icc 2 k,
          (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
            ((∫ ω, RClass fmin fmax n hn m (A ω) i ∂μ) / fGrid fmin fmax m i)
  | 0, hk1, _ => by omega
  | k + 1, _, hkm => by
    have hint_class : ∀ i, 1 ≤ i → i ≤ m →
        Integrable (fun ω => RClass fmin fmax n hn m (A ω) i) μ := by
      intro i hi1 him
      have hI := instClass_faresIn fmin fmax n hn m hi1 him
      exact Integrable.of_mem_Icc 0 (fmax * n) (hA _ hI).aemeasurable
        (Filter.Eventually.of_forall fun ω =>
          revenue_bounds fmin fmax n hfmin hf hn m hm (A ω) hI)
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hIcc : (Finset.Icc 2 1 : Finset ℕ) = ∅ := rfl
      simp only [hIcc, Finset.sum_empty, add_zero]
      refine ⟨(hint_class 1 le_rfl hkm).div_const (fGrid fmin fmax m 1),
        integral_div (fGrid fmin fmax m 1) _⟩
    · obtain ⟨ih_int, ih_eq⟩ := sum_Icc_int_eq fmin fmax n hfmin hf hn m hm μ A hA k hkpos (by omega)
      have hterm_int : Integrable (fun ω =>
          (1 - fGrid fmin fmax m (k + 1) / fGrid fmin fmax m k) *
            (RClass fmin fmax n hn m (A ω) (k + 1) / fGrid fmin fmax m (k + 1))) μ :=
        ((hint_class (k + 1) (by omega) hkm).div_const (fGrid fmin fmax m (k + 1))).const_mul _
      have hfun_eq :
          (fun ω => RClass fmin fmax n hn m (A ω) 1 / fGrid fmin fmax m 1 +
            ∑ i ∈ Finset.Icc 2 (k + 1),
              (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
                (RClass fmin fmax n hn m (A ω) i / fGrid fmin fmax m i)) =
          (fun ω => (RClass fmin fmax n hn m (A ω) 1 / fGrid fmin fmax m 1 +
            ∑ i ∈ Finset.Icc 2 k,
              (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
                (RClass fmin fmax n hn m (A ω) i / fGrid fmin fmax m i)) +
            (1 - fGrid fmin fmax m (k + 1) / fGrid fmin fmax m k) *
              (RClass fmin fmax n hn m (A ω) (k + 1) / fGrid fmin fmax m (k + 1))) := by
        funext ω
        rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel, add_assoc]
      rw [hfun_eq]
      refine ⟨ih_int.add hterm_int, ?_⟩
      rw [integral_add ih_int hterm_int, ih_eq, integral_const_mul, integral_div,
        Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel, add_assoc]

lemma rand_grid_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (m : ℕ) (hm : 2 ≤ m)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy)
    (hA : ∀ I : List Request, FaresIn (gridFares fmin fmax m) I →
      Measurable fun ω => revenue n (A ω) I) :
    competitiveRatioRandOn (gridFares fmin fmax m) n μ A ≤ 1 / DeltaGrid fmin fmax m := by
  have hbdd : BddBelow {c : ℝ | ∃ I : List Request,
      FaresIn (gridFares fmin fmax m) I ∧ 0 < offlineOpt n I ∧
      c = (∫ ω, revenue n (A ω) I ∂μ) / offlineOpt n I} := by
    refine ⟨0, ?_⟩
    rintro c ⟨I, hI, hopt, rfl⟩
    apply div_nonneg _ hopt.le
    exact integral_nonneg fun ω => (revenue_bounds fmin fmax n hfmin hf hn m hm (A ω) hI).1
  set c := competitiveRatioRandOn (gridFares fmin fmax m) n μ A
  have hc_le : ∀ i, 1 ≤ i → i ≤ m →
      c * n ≤ (∫ ω, RClass fmin fmax n hn m (A ω) i ∂μ) / fGrid fmin fmax m i := by
    intro i hi1 him
    have hfi : 0 < fGrid fmin fmax m i := fGrid_pos fmin fmax hfmin hf m i
    have hfin : 0 < fGrid fmin fmax m i * n := mul_pos hfi hn
    have hI := instClass_faresIn fmin fmax n hn m hi1 him
    have hopt := offlineOpt_instClass fmin fmax n hfmin hf hn m hm hi1 him
    have hmem : (∫ ω, RClass fmin fmax n hn m (A ω) i ∂μ) / (fGrid fmin fmax m i * n) ∈
        {v : ℝ | ∃ I : List Request, FaresIn (gridFares fmin fmax m) I ∧ 0 < offlineOpt n I ∧
          v = (∫ ω, revenue n (A ω) I ∂μ) / offlineOpt n I} := by
      refine ⟨instClass fmin fmax n hn m i, hI, by rw [hopt]; exact hfin, ?_⟩
      rw [hopt]; rfl
    have hle : c ≤ (∫ ω, RClass fmin fmax n hn m (A ω) i ∂μ) / (fGrid fmin fmax m i * n) :=
      csInf_le hbdd hmem
    rw [le_div_iff₀ hfin] at hle
    rw [le_div_iff₀ hfi]
    linarith
  obtain ⟨hint_tot, heq_tot⟩ := sum_Icc_int_eq fmin fmax n hfmin hf hn m hm μ A hA m (by omega) le_rfl
  have hint_le_n :
      (∫ ω, RClass fmin fmax n hn m (A ω) 1 ∂μ) / fGrid fmin fmax m 1 +
        ∑ i ∈ Finset.Icc 2 m,
          (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
            ((∫ ω, RClass fmin fmax n hn m (A ω) i ∂μ) / fGrid fmin fmax m i) ≤ n := by
    rw [← heq_tot]
    have hmono := integral_mono hint_tot (integrable_const n)
      (fun ω => telescope_det_full fmin fmax n hfmin hf hn m hm (A ω))
    simpa using hmono
  have hsum_ge :
      c * n * DeltaGrid fmin fmax m ≤
        (∫ ω, RClass fmin fmax n hn m (A ω) 1 ∂μ) / fGrid fmin fmax m 1 +
          ∑ i ∈ Finset.Icc 2 m,
            (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
              ((∫ ω, RClass fmin fmax n hn m (A ω) i ∂μ) / fGrid fmin fmax m i) := by
    rw [deltaGrid_eq_sum fmin fmax hfmin hf m hm, mul_add, mul_one, Finset.mul_sum]
    refine add_le_add (hc_le 1 le_rfl (by omega)) ?_
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    have hw : 0 ≤ 1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1) := by
      rw [fGrid_ratio fmin fmax hfmin hf m hi.1]
      exact (weight_grid_pos fmin fmax hfmin hf m hm).le
    have hci := hc_le i (by omega) hi.2
    calc c * n * (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1))
        = (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) * (c * n) := mul_comm _ _
      _ ≤ (1 - fGrid fmin fmax m i / fGrid fmin fmax m (i - 1)) *
            ((∫ ω, RClass fmin fmax n hn m (A ω) i ∂μ) / fGrid fmin fmax m i) :=
        mul_le_mul_of_nonneg_left hci hw
  have hcn : c * n * DeltaGrid fmin fmax m ≤ n := le_trans hsum_ge hint_le_n
  have hΔpos : 0 < DeltaGrid fmin fmax m := deltaGrid_pos fmin fmax hfmin hf m hm
  rw [le_div_iff₀ hΔpos]
  nlinarith

end Aux_RB_grid

namespace RobustBooking.BidPrice

open Aux_RB_grid

theorem theorem6_grid_bound (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (m : ℕ) (hm : 2 ≤ m) :
    (∀ P : DetPolicy, competitiveRatioOn (gridFares fmin fmax m) n P ≤
        1 / ((m : ℝ) - ((m : ℝ) - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1)))) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → DetPolicy),
        (∀ I : List Request, FaresIn (gridFares fmin fmax m) I →
          Measurable fun ω => revenue n (A ω) I) →
          competitiveRatioRandOn (gridFares fmin fmax m) n μ A ≤
            1 / ((m : ℝ) - ((m : ℝ) - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1))) := by
  refine ⟨?_, fun μ _ A hA => rand_grid_bound fmin fmax n hfmin hf hn m hm μ A hA⟩
  intro P
  let μ0 : Measure Unit := Measure.dirac ()
  have hprob : IsProbabilityMeasure μ0 := Measure.dirac.isProbabilityMeasure
  have h1 := rand_grid_bound fmin fmax n hfmin hf hn m hm μ0 (fun _ => P) (fun _ _ => measurable_const)
  have heq : competitiveRatioOn (gridFares fmin fmax m) n P =
      competitiveRatioRandOn (gridFares fmin fmax m) n μ0 (fun _ => P) := by
    unfold competitiveRatioOn competitiveRatioRandOn
    congr 1
    ext c
    simp [μ0]
  rw [heq]
  exact h1

end RobustBooking.BidPrice

open RobustBooking.BidPrice MeasureTheory in
theorem solution (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (m : ℕ) (hm : 2 ≤ m) :
    (∀ P : DetPolicy, competitiveRatioOn (gridFares fmin fmax m) n P ≤
        1 / ((m : ℝ) - ((m : ℝ) - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1)))) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → DetPolicy),
        (∀ I : List Request, FaresIn (gridFares fmin fmax m) I →
          Measurable fun ω => revenue n (A ω) I) →
          competitiveRatioRandOn (gridFares fmin fmax m) n μ A ≤
            1 / ((m : ℝ) - ((m : ℝ) - 1) * discountRatio fmin fmax ^ (1 / ((m : ℝ) - 1))) :=
  theorem6_grid_bound fmin fmax n hfmin hf hn m hm
