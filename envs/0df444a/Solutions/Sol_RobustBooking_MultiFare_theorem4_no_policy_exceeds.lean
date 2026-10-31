-- Prove2me | solution 1 for RobustBooking.MultiFare.theorem4_no_policy_exceeds
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:34:06.934277+00:00
-- url     : https://prove2.me/submissions/f85cd7a6-88e3-4703-8c00-c25f50027e36

import Mathlib
import Definitions.Def_RobustBooking_MultiFare_BookingModel
import Definitions.Def_RobustBooking_MultiFare_ProtectionLevels

open MeasureTheory

namespace Aux_RB_thm4

open RobustBooking.MultiFare

lemma f_pos (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) : 0 < f i := by
  rcases him.lt_or_eq with h | h
  · exact lt_trans hfm (hf ⟨hi1, him⟩ ⟨by omega, le_rfl⟩ h)
  · rw [h]; exact hfm

lemma f_le_of_le (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m))
    {i j : ℕ} (hi1 : 1 ≤ i) (hij : i ≤ j) (hjm : j ≤ m) : f j ≤ f i := by
  rcases hij.lt_or_eq with h | h
  · exact (hf ⟨hi1, le_trans hij hjm⟩ ⟨le_trans hi1 hij, hjm⟩ h).le
  · rw [h]

lemma weight_pos (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m)
    {i : ℕ} (hi2 : 2 ≤ i) (him : i ≤ m) : 0 < 1 - f i / f (i - 1) := by
  have h1 : 0 < f (i - 1) := f_pos m f hf hfm (by omega) (by omega)
  have h2 : f i < f (i - 1) := hf ⟨by omega, by omega⟩ ⟨by omega, him⟩ (by omega)
  have h3 : f i / f (i - 1) < 1 := (div_lt_one h1).mpr h2
  linarith

lemma delta_eq_one_add_sum (m : ℕ) (f : ℕ → ℝ) (hm : 2 ≤ m) :
    Delta m f = 1 + ∑ i ∈ Finset.Icc 2 m, (1 - f i / f (i - 1)) := by
  unfold Delta
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  have hcard : m + 1 - 2 = m - 1 := by omega
  rw [hcard, nsmul_eq_mul, mul_one, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  ring

lemma delta_pos (m : ℕ) (f : ℕ → ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) : 0 < Delta m f := by
  rw [delta_eq_one_add_sum m f hm]
  have hsum : 0 ≤ ∑ i ∈ Finset.Icc 2 m, (1 - f i / f (i - 1)) := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact (weight_pos m f hf hfm hi.1 hi.2).le
  linarith

def instDown (n : ℝ) (i : ℕ) : ℕ → List Request
  | 0 => []
  | k + 1 => instDown n (i + 1) k ++ [⟨i, n⟩]

def instClass (m : ℕ) (n : ℝ) (i : ℕ) : List Request :=
  instDown n i (m + 1 - i)

lemma instClass_top (m : ℕ) (n : ℝ) : instClass m n (m + 1) = [] := by
  simp [instClass, instDown]

lemma instClass_step (m : ℕ) (n : ℝ) (i : ℕ) (hi : i ≤ m) :
    instClass m n i = instClass m n (i + 1) ++ [⟨i, n⟩] := by
  have h : m + 1 - i = (m + 1 - (i + 1)) + 1 := by omega
  rw [instClass, h, instDown, ← instClass]

lemma mem_instDown (n : ℝ) :
    ∀ (k i : ℕ) (r : Request), r ∈ instDown n i k → i ≤ r.cls ∧ r.cls < i + k ∧ r.qty = n
  | 0, i, r, hr => by simp [instDown] at hr
  | k + 1, i, r, hr => by
    simp only [instDown, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · obtain ⟨h1, h2, h3⟩ := mem_instDown n k (i + 1) r hr
      exact ⟨by omega, by omega, h3⟩
    · exact ⟨le_rfl, by simp, rfl⟩

lemma mem_instClass (m : ℕ) (n : ℝ) {i : ℕ} (him : i ≤ m) {r : Request}
    (hr : r ∈ instClass m n i) : i ≤ r.cls ∧ r.cls ≤ m ∧ r.qty = n := by
  obtain ⟨h1, h2, h3⟩ := mem_instDown n (m + 1 - i) i r hr
  exact ⟨h1, by omega, h3⟩

lemma instClass_isInstance (m : ℕ) (n : ℝ) (hn : 0 < n) {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) :
    IsInstance m (instClass m n i) := by
  intro r hr
  obtain ⟨h1, h2, h3⟩ := mem_instClass m n him hr
  exact ⟨le_trans hi1 h1, h2, h3 ▸ hn⟩

lemma offlineOpt_append_singleton (m : ℕ) (f : ℕ → ℝ) (n : ℝ)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    (L : List Request) (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m)
    (hL : ∀ r ∈ L, i ≤ r.cls ∧ r.cls ≤ m ∧ r.qty = n) :
    offlineOpt f n (L ++ [⟨i, n⟩]) = f i * n := by
  have hfi : 0 < f i := f_pos m f hf hfm hi1 him
  unfold offlineOpt
  apply IsGreatest.csSup_eq
  set I := L ++ [⟨i, n⟩]
  have hlen : I.length = L.length + 1 := by simp [I]
  let k0 : Fin I.length := ⟨L.length, by rw [hlen]; omega⟩
  have hget_k0 : I.get k0 = ⟨i, n⟩ := by
    simp [I, k0, List.getElem_append_right]
  constructor
  · refine ⟨fun k => if k = k0 then n else 0, ⟨fun k => ?_, ?_, ?_⟩⟩
    · have hmem : I.get k ∈ I := List.get_mem I k
      have hqty : (I.get k).qty = n := by
        simp only [I, List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hm | hm
        · exact (hL _ hm).2.2
        · rw [hm]
      rw [hqty]
      dsimp only
      split_ifs
      · exact ⟨hn.le, le_rfl⟩
      · exact ⟨le_rfl, hn.le⟩
    · simp [Finset.sum_ite_eq']
    · simp [mul_ite, Finset.sum_ite_eq', -List.get_eq_getElem, hget_k0]
  · rintro v ⟨x, ⟨hx1, hx2, rfl⟩⟩
    calc ∑ k : Fin I.length, f (I.get k).cls * x k
        ≤ ∑ k : Fin I.length, f i * x k := by
          refine Finset.sum_le_sum fun k _ => ?_
          apply mul_le_mul_of_nonneg_right _ (hx1 k).1
          have hmem : I.get k ∈ I := List.get_mem I k
          simp only [I, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hm | hm
          · obtain ⟨hc1, hc2, _⟩ := hL _ hm
            exact f_le_of_le m f hf hi1 hc1 hc2
          · rw [hm]
      _ = f i * ∑ k : Fin I.length, x k := (Finset.mul_sum _ _ _).symm
      _ ≤ f i * n := mul_le_mul_of_nonneg_left hx2 hfi.le

lemma offlineOpt_instClass (m : ℕ) (f : ℕ → ℝ) (n : ℝ)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) :
    offlineOpt f n (instClass m n i) = f i * n := by
  rw [instClass_step m n i him]
  apply offlineOpt_append_singleton m f n hf hfm hn (instClass m n (i + 1)) i hi1 him
  intro r hr
  by_cases hi' : i + 1 ≤ m
  · obtain ⟨h1, h2, h3⟩ := mem_instClass m n hi' hr
    exact ⟨by omega, h2, h3⟩
  · have hm_eq : i + 1 = m + 1 := by omega
    rw [hm_eq, instClass_top] at hr
    simp at hr

lemma runFrom_append (n : ℝ) (B : DetPolicy) :
    ∀ (I₁ I₂ : List Request) (past : List (Request × ℝ)),
      runFrom n B past (I₁ ++ I₂) = runFrom n B (runFrom n B past I₁) I₂
  | [], I₂, past => rfl
  | r :: rs, I₂, past => by
    simp only [List.cons_append, runFrom]
    exact runFrom_append n B rs I₂ _

lemma runFrom_bounds (m : ℕ) (f : ℕ → ℝ) (n : ℝ)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (B : DetPolicy) :
    ∀ (I : List Request) (past : List (Request × ℝ)),
      IsInstance m I →
      (∀ p ∈ past, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2) →
      (past.map Prod.snd).sum ≤ n →
      (∀ p ∈ runFrom n B past I, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2) ∧
      ((runFrom n B past I).map Prod.snd).sum ≤ n
  | [], past, _, hpast, hsum => ⟨hpast, hsum⟩
  | r :: rs, past, hI, hpast, hsum => by
    have hr : 1 ≤ r.cls ∧ r.cls ≤ m ∧ 0 < r.qty := hI r List.mem_cons_self
    have hrs : IsInstance m rs := fun q hq => hI q (List.mem_cons_of_mem _ hq)
    set used := (past.map Prod.snd).sum
    set y := clip n used r (B past r)
    have hy0 : 0 ≤ y := le_max_left 0 _
    have hy_le : y ≤ n - used := by
      dsimp [y, clip]
      exact max_le (by linarith) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hpast' : ∀ p ∈ past ++ [(r, y)], 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2 := by
      intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hpast p hp
      · exact ⟨hr.1, hr.2.1, hy0⟩
    have hsum' : ((past ++ [(r, y)]).map Prod.snd).sum ≤ n := by
      rw [List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      dsimp [used] at hy_le
      linarith
    exact runFrom_bounds m f n hf hfm B rs (past ++ [(r, y)]) hrs hpast' hsum'

lemma list_sum_rev_bounds (m : ℕ) (f : ℕ → ℝ) (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) :
    ∀ (L : List (Request × ℝ)),
      (∀ p ∈ L, 1 ≤ p.1.cls ∧ p.1.cls ≤ m ∧ 0 ≤ p.2) →
      0 ≤ (L.map fun p => f p.1.cls * p.2).sum ∧
      (L.map fun p => f p.1.cls * p.2).sum ≤ f 1 * (L.map Prod.snd).sum
  | [], _ => by simp
  | p :: ps, hL => by
    have hp := hL p List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := list_sum_rev_bounds m f hf hfm ps (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.sum_cons]
    have hfp_pos : 0 < f p.1.cls := f_pos m f hf hfm hp.1 hp.2.1
    have hfp_le : f p.1.cls ≤ f 1 := f_le_of_le m f hf le_rfl hp.1 hp.2.1
    refine ⟨add_nonneg (mul_nonneg hfp_pos.le hp.2.2) ih1, ?_⟩
    have hmul : f p.1.cls * p.2 ≤ f 1 * p.2 := mul_le_mul_of_nonneg_right hfp_le hp.2.2
    linarith

lemma revenue_bounds (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    (B : DetPolicy) {I : List Request} (hI : IsInstance m I) :
    0 ≤ revenue f n B I ∧ revenue f n B I ≤ f 1 * n := by
  have hf1 : 0 < f 1 := f_pos m f hf hfm le_rfl (by omega)
  obtain ⟨h1, h2⟩ := runFrom_bounds m f n hf hfm B I [] hI (by simp) (by simp [hn.le])
  obtain ⟨r1, r2⟩ := list_sum_rev_bounds m f hf hfm (run n B I) h1
  unfold revenue
  exact ⟨r1, le_trans r2 (mul_le_mul_of_nonneg_left h2 hf1.le)⟩

noncomputable def uClass (m : ℕ) (n : ℝ) (B : DetPolicy) (i : ℕ) : ℝ :=
  ((run n B (instClass m n i)).map Prod.snd).sum

noncomputable def RClass (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (B : DetPolicy) (i : ℕ) : ℝ :=
  revenue f n B (instClass m n i)

lemma uClass_top (m : ℕ) (n : ℝ) (B : DetPolicy) : uClass m n B (m + 1) = 0 := by
  simp [uClass, instClass_top, run, runFrom]

lemma RClass_top (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (B : DetPolicy) : RClass m f n B (m + 1) = 0 := by
  simp [RClass, revenue, instClass_top, run, runFrom]

lemma uClass_one_le_n (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n) (B : DetPolicy) :
    uClass m n B 1 ≤ n := by
  have hI : IsInstance m (instClass m n 1) := instClass_isInstance m n hn le_rfl (by omega)
  exact (runFrom_bounds m f n hf hfm B (instClass m n 1) [] hI (by simp) (by simp [hn.le])).2

lemma RClass_step (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (B : DetPolicy) {i : ℕ} (him : i ≤ m) :
    RClass m f n B i = RClass m f n B (i + 1) + f i * (uClass m n B i - uClass m n B (i + 1)) := by
  unfold RClass revenue uClass run
  rw [instClass_step m n i him, runFrom_append]
  set past := runFrom n B [] (instClass m n (i + 1))
  simp only [runFrom, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

lemma telescope_det (m : ℕ) (f : ℕ → ℝ) (n : ℝ)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (B : DetPolicy) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m →
      RClass m f n B 1 / f 1 +
        ∑ i ∈ Finset.Icc 2 k, (1 - f i / f (i - 1)) * (RClass m f n B i / f i) =
      uClass m n B 1 - uClass m n B (k + 1) + RClass m f n B (k + 1) / f k
  | 0, hk1, _ => by omega
  | 1, _, h1m => by
    have hf1 : f 1 ≠ 0 := (f_pos m f hf hfm le_rfl h1m).ne'
    have hstep := RClass_step m f n B h1m
    have hIcc : (Finset.Icc 2 1 : Finset ℕ) = ∅ := rfl
    rw [hIcc, Finset.sum_empty, add_zero]
    rw [hstep]
    field_simp
    ring
  | k + 1, _, hkm => by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hf1 : f 1 ≠ 0 := (f_pos m f hf hfm le_rfl hkm).ne'
      have hstep := RClass_step m f n B hkm
      have hIcc : (Finset.Icc 2 1 : Finset ℕ) = ∅ := rfl
      rw [hIcc, Finset.sum_empty, add_zero, hstep]
      field_simp
      ring
    · have ih := telescope_det m f n hf hfm B k hkpos (by omega)
      rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel, ← add_assoc, ih]
      have hfk : f k ≠ 0 := (f_pos m f hf hfm hkpos (by omega)).ne'
      have hfk1 : f (k + 1) ≠ 0 := (f_pos m f hf hfm (by omega) hkm).ne'
      have hstep := RClass_step m f n B hkm
      have hcancel :
          (1 - f (k + 1) / f k) * (RClass m f n B (k + 1) / f (k + 1)) =
            RClass m f n B (k + 1) / f (k + 1) - RClass m f n B (k + 1) / f k := by
        field_simp
      have hdiv :
          RClass m f n B (k + 1) / f (k + 1) =
            RClass m f n B (k + 1 + 1) / f (k + 1) +
              (uClass m n B (k + 1) - uClass m n B (k + 1 + 1)) := by
        rw [hstep]
        field_simp
      linarith

lemma telescope_det_full (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n) (B : DetPolicy) :
    RClass m f n B 1 / f 1 +
      ∑ i ∈ Finset.Icc 2 m, (1 - f i / f (i - 1)) * (RClass m f n B i / f i) ≤ n := by
  have h := telescope_det m f n hf hfm B m (by omega) le_rfl
  rw [uClass_top, RClass_top, sub_zero, zero_div, add_zero] at h
  rw [h]
  exact uClass_one_le_n m f n hm hf hfm hn B

lemma sum_Icc_int_eq (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy) (hA : ∀ I : List Request, IsInstance m I →
      Measurable fun ω => revenue f n (A ω) I) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m →
      Integrable (fun ω => RClass m f n (A ω) 1 / f 1 +
        ∑ i ∈ Finset.Icc 2 k, (1 - f i / f (i - 1)) * (RClass m f n (A ω) i / f i)) μ ∧
      (∫ ω, (RClass m f n (A ω) 1 / f 1 +
        ∑ i ∈ Finset.Icc 2 k, (1 - f i / f (i - 1)) * (RClass m f n (A ω) i / f i)) ∂μ) =
        (∫ ω, RClass m f n (A ω) 1 ∂μ) / f 1 +
        ∑ i ∈ Finset.Icc 2 k, (1 - f i / f (i - 1)) * ((∫ ω, RClass m f n (A ω) i ∂μ) / f i)
  | 0, hk1, _ => by omega
  | k + 1, _, hkm => by
    have hint_class : ∀ i, 1 ≤ i → i ≤ m → Integrable (fun ω => RClass m f n (A ω) i) μ := by
      intro i hi1 him
      have hI := instClass_isInstance m n hn hi1 him
      exact Integrable.of_mem_Icc 0 (f 1 * n) (hA _ hI).aemeasurable
        (Filter.Eventually.of_forall fun ω => revenue_bounds m f n hm hf hfm hn (A ω) hI)
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hIcc : (Finset.Icc 2 1 : Finset ℕ) = ∅ := rfl
      simp only [hIcc, Finset.sum_empty, add_zero]
      refine ⟨(hint_class 1 le_rfl hkm).div_const (f 1), integral_div (f 1) _⟩
    · obtain ⟨ih_int, ih_eq⟩ := sum_Icc_int_eq m f n hm hf hfm hn μ A hA k hkpos (by omega)
      have hterm_int : Integrable (fun ω =>
          (1 - f (k + 1) / f k) * (RClass m f n (A ω) (k + 1) / f (k + 1))) μ :=
        ((hint_class (k + 1) (by omega) hkm).div_const (f (k + 1))).const_mul _
      have hfun_eq :
          (fun ω => RClass m f n (A ω) 1 / f 1 +
            ∑ i ∈ Finset.Icc 2 (k + 1), (1 - f i / f (i - 1)) * (RClass m f n (A ω) i / f i)) =
          (fun ω => (RClass m f n (A ω) 1 / f 1 +
            ∑ i ∈ Finset.Icc 2 k, (1 - f i / f (i - 1)) * (RClass m f n (A ω) i / f i)) +
            (1 - f (k + 1) / f k) * (RClass m f n (A ω) (k + 1) / f (k + 1))) := by
        funext ω
        rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel, add_assoc]
      rw [hfun_eq]
      refine ⟨ih_int.add hterm_int, ?_⟩
      rw [integral_add ih_int hterm_int, ih_eq, integral_const_mul, integral_div,
        Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel, add_assoc]

lemma rand_upper_bound (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy) (hA : ∀ I : List Request, IsInstance m I →
      Measurable fun ω => revenue f n (A ω) I) :
    randCompetitiveRatio m f n μ A ≤ 1 / Delta m f := by
  have hbdd : BddBelow {c : ℝ | ∃ I : List Request, IsInstance m I ∧ 0 < offlineOpt f n I ∧
      c = (∫ ω, revenue f n (A ω) I ∂μ) / offlineOpt f n I} := by
    refine ⟨0, ?_⟩
    rintro c ⟨I, hI, hopt, rfl⟩
    apply div_nonneg _ hopt.le
    exact integral_nonneg fun ω => (revenue_bounds m f n hm hf hfm hn (A ω) hI).1
  set c := randCompetitiveRatio m f n μ A
  have hc_le : ∀ i, 1 ≤ i → i ≤ m →
      c * n ≤ (∫ ω, RClass m f n (A ω) i ∂μ) / f i := by
    intro i hi1 him
    have hfi : 0 < f i := f_pos m f hf hfm hi1 him
    have hfin : 0 < f i * n := mul_pos hfi hn
    have hI := instClass_isInstance m n hn hi1 him
    have hopt := offlineOpt_instClass m f n hf hfm hn hi1 him
    have hmem : (∫ ω, RClass m f n (A ω) i ∂μ) / (f i * n) ∈
        {v : ℝ | ∃ I : List Request, IsInstance m I ∧ 0 < offlineOpt f n I ∧
          v = (∫ ω, revenue f n (A ω) I ∂μ) / offlineOpt f n I} := by
      refine ⟨instClass m n i, hI, by rw [hopt]; exact hfin, ?_⟩
      rw [hopt]; rfl
    have hle : c ≤ (∫ ω, RClass m f n (A ω) i ∂μ) / (f i * n) := csInf_le hbdd hmem
    rw [le_div_iff₀ hfin] at hle
    rw [le_div_iff₀ hfi]
    linarith
  obtain ⟨hint_tot, heq_tot⟩ := sum_Icc_int_eq m f n hm hf hfm hn μ A hA m (by omega) le_rfl
  have hint_le_n :
      (∫ ω, RClass m f n (A ω) 1 ∂μ) / f 1 +
        ∑ i ∈ Finset.Icc 2 m, (1 - f i / f (i - 1)) * ((∫ ω, RClass m f n (A ω) i ∂μ) / f i) ≤ n := by
    rw [← heq_tot]
    have hmono := integral_mono hint_tot (integrable_const n)
      (fun ω => telescope_det_full m f n hm hf hfm hn (A ω))
    simpa using hmono
  have hsum_ge :
      c * n * Delta m f ≤
        (∫ ω, RClass m f n (A ω) 1 ∂μ) / f 1 +
          ∑ i ∈ Finset.Icc 2 m, (1 - f i / f (i - 1)) * ((∫ ω, RClass m f n (A ω) i ∂μ) / f i) := by
    rw [delta_eq_one_add_sum m f hm, mul_add, mul_one, Finset.mul_sum]
    refine add_le_add (hc_le 1 le_rfl (by omega)) ?_
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Icc] at hi
    have hw : 0 ≤ 1 - f i / f (i - 1) := (weight_pos m f hf hfm hi.1 hi.2).le
    have hci := hc_le i (by omega) hi.2
    calc c * n * (1 - f i / f (i - 1))
        = (1 - f i / f (i - 1)) * (c * n) := mul_comm _ _
      _ ≤ (1 - f i / f (i - 1)) * ((∫ ω, RClass m f n (A ω) i ∂μ) / f i) :=
        mul_le_mul_of_nonneg_left hci hw
  have hcn : c * n * Delta m f ≤ n := le_trans hsum_ge hint_le_n
  have hΔpos : 0 < Delta m f := delta_pos m f hm hf hfm
  rw [le_div_iff₀ hΔpos]
  nlinarith

end Aux_RB_thm4

namespace RobustBooking.MultiFare

open Aux_RB_thm4

theorem theorem4_no_policy_exceeds (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy) (hA : ∀ I : List Request, IsInstance m I →
      Measurable fun ω => revenue f n (A ω) I) :
    (∀ B : DetPolicy, competitiveRatio m f n B ≤ 1 / Delta m f) ∧
    randCompetitiveRatio m f n μ A ≤ 1 / Delta m f := by
  refine ⟨?_, rand_upper_bound m f n hm hf hfm hn μ A hA⟩
  intro B
  let μ0 : Measure Unit := Measure.dirac ()
  have hprob : IsProbabilityMeasure μ0 := Measure.dirac.isProbabilityMeasure
  have h1 := rand_upper_bound m f n hm hf hfm hn μ0 (fun _ => B) (fun _ _ => measurable_const)
  have heq : competitiveRatio m f n B = randCompetitiveRatio m f n μ0 (fun _ => B) := by
    unfold competitiveRatio randCompetitiveRatio
    congr 1
    ext c
    simp [μ0]
  rw [heq]
  exact h1

end RobustBooking.MultiFare

open RobustBooking.MultiFare MeasureTheory in
theorem solution (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy) (hA : ∀ I : List Request, IsInstance m I →
      Measurable fun ω => revenue f n (A ω) I) :
    (∀ B : DetPolicy, competitiveRatio m f n B ≤ 1 / Delta m f) ∧
    randCompetitiveRatio m f n μ A ≤ 1 / Delta m f :=
  theorem4_no_policy_exceeds m f n hm hf hfm hn μ A hA
