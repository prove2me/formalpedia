-- Prove2me | solution 1 for ProcureAssort.Hotelling.corollary_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T03:20:26.44145+00:00
-- url     : https://prove2.me/submissions/0ace97d2-643b-4b16-886d-81b28a93eff5

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

open ProcureAssort.Hotelling

namespace PAx

variable {n : ℕ}

lemma interim_sub_mul (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (g h : Profile Θ → ℝ)
    (i : Fin n) (c r : ℝ) :
    interim f (fun θ => g θ - c * h θ) i r = interim f g i r - c * interim f h i r := by
  unfold interim
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun θ _ => ?_
  split_ifs <;> ring

lemma interim_fn_mul (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (φ : ℝ → ℝ)
    (g : Profile Θ → ℝ) (i : Fin n) (c : ℝ) :
    interim f (fun θ => φ (θ i) * g θ) i c = φ c * interim f g i c := by
  unfold interim
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun θ _ => ?_
  split_ifs with h
  · simp only; rw [h]; ring
  · ring

lemma interim_nonneg (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ}
    (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (g : Profile Θ → ℝ) (hg : ∀ θ, 0 ≤ g θ)
    (i : Fin n) (c : ℝ) : 0 ≤ interim f g i c := by
  unfold interim probOthers
  refine Finset.sum_nonneg fun θ _ => ?_
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg fun j _ => (hf0 j _ (θ j).2).le) (hg θ)
  · exact le_rfl

lemma utility_eq (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (x t : Profile Θ → Fin n → ℝ)
    (i : Fin n) (r c : ℝ) :
    utility f x t i r c = interim f (fun θ => t θ i) i r - c * interim f (fun θ => x θ i) i r :=
  interim_sub_mul f _ _ i c r

lemma prob_eq (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (θ : Profile Θ) (i : Fin n) :
    prob f θ = f i (θ i) * probOthers f i θ := by
  unfold prob probOthers
  rw [Finset.mul_prod_erase _ (fun k => f k (θ k)) (Finset.mem_univ i)]

lemma expect_eq_sum_interim (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (g : Profile Θ → ℝ)
    (i : Fin n) : expect f g = ∑ c ∈ Θ i, f i c * interim f g i c := by
  unfold expect interim
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun θ _ => ?_
  have : ∀ c ∈ Θ i, f i c * (if (θ i : ℝ) = c then probOthers f i θ * g θ else 0) =
      if (θ i : ℝ) = c then f i (θ i) * probOthers f i θ * g θ else 0 := by
    intro c _
    split_ifs with h
    · rw [h]; ring
    · ring
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos (θ i).2, prob_eq f θ i]

lemma expect_sub (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (g h : Profile Θ → ℝ) :
    expect f (fun θ => g θ - h θ) = expect f g - expect f h := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun θ _ => by ring

lemma expect_sum (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (g : Fin n → Profile Θ → ℝ) :
    expect f (fun θ => ∑ i, g i θ) = ∑ i, expect f (g i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma expect_mono (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ}
    (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (g h : Profile Θ → ℝ) (hgh : ∀ θ, g θ ≤ h θ) :
    expect f g ≤ expect f h := by
  unfold expect prob
  refine Finset.sum_le_sum fun θ _ => ?_
  exact mul_le_mul_of_nonneg_left (hgh θ) (Finset.prod_nonneg fun j _ => (hf0 j _ (θ j).2).le)

/-! ### predecessor -/

lemma pred_spec (Θ : Fin n → Finset ℝ) (i : Fin n) (r : ℝ)
    (h : ((Θ i).filter (· < r)).Nonempty) :
    pred Θ i r ∈ Θ i ∧ pred Θ i r < r ∧ ∀ b ∈ Θ i, b < r → b ≤ pred Θ i r := by
  unfold pred
  rw [dif_pos h]
  have hm := Finset.max'_mem _ h
  rw [Finset.mem_filter] at hm
  refine ⟨hm.1, hm.2, fun b hb hbr => ?_⟩
  exact Finset.le_max' _ b (Finset.mem_filter.mpr ⟨hb, hbr⟩)

lemma pred_of_empty (Θ : Fin n → Finset ℝ) (i : Fin n) (r : ℝ)
    (h : ¬ ((Θ i).filter (· < r)).Nonempty) : pred Θ i r = r := by
  unfold pred; rw [dif_neg h]

lemma pred_le (Θ : Fin n → Finset ℝ) (i : Fin n) (r : ℝ) : pred Θ i r ≤ r := by
  by_cases h : ((Θ i).filter (· < r)).Nonempty
  · exact (pred_spec Θ i r h).2.1.le
  · rw [pred_of_empty Θ i r h]

lemma pred_of_succ (Θ : Fin n → Finset ℝ) (i : Fin n) (c s : ℝ) (hc : c ∈ Θ i)
    (hcs : c < s) (hnone : ∀ b ∈ Θ i, c < b → s ≤ b) : pred Θ i s = c := by
  have hne : ((Θ i).filter (· < s)).Nonempty := ⟨c, Finset.mem_filter.mpr ⟨hc, hcs⟩⟩
  obtain ⟨h1, h2, h3⟩ := pred_spec Θ i s hne
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    exact absurd (hnone _ h1 hlt) (not_le.mpr h2)
  · exact h3 c hc hcs

/-- Telescoping. -/
lemma telescope (Θ : Fin n → Finset ℝ) (i : Fin n) (c : ℝ) (hc : c ∈ Θ i) :
    ∀ (k : ℕ) (r : ℝ), r ∈ Θ i → c ≤ r →
      ((Θ i).filter (fun b => c < b ∧ b ≤ r)).card = k →
      ∑ b ∈ (Θ i).filter (fun b => c < b ∧ b ≤ r), (b - pred Θ i b) = r - c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro r hr hcr hk
  rcases eq_or_lt_of_le hcr with h | h
  · subst h
    have : (Θ i).filter (fun b => c < b ∧ b ≤ c) = ∅ := by
      ext b; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨_, h1, h2⟩; linarith
    rw [this]; simp
  · have hne : ((Θ i).filter (· < r)).Nonempty := ⟨c, Finset.mem_filter.mpr ⟨hc, h⟩⟩
    obtain ⟨hp, hpr, hmax⟩ := pred_spec Θ i r hne
    have hcp : c ≤ pred Θ i r := hmax c hc h
    have hset : (Θ i).filter (fun b => c < b ∧ b ≤ r) =
        insert r ((Θ i).filter (fun b => c < b ∧ b ≤ pred Θ i r)) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hb, h1, h2⟩
        rcases eq_or_lt_of_le h2 with e | e
        · exact Or.inl e
        · exact Or.inr ⟨hb, h1, hmax b hb e⟩
      · rintro (e | ⟨hb, h1, h2⟩)
        · subst e; exact ⟨hr, h, le_rfl⟩
        · exact ⟨hb, h1, h2.trans hpr.le⟩
    have hnot : r ∉ (Θ i).filter (fun b => c < b ∧ b ≤ pred Θ i r) := by
      simp only [Finset.mem_filter, not_and, not_le]
      intro _ _; exact hpr
    rw [hset, Finset.sum_insert hnot]
    have hcard : ((Θ i).filter (fun b => c < b ∧ b ≤ pred Θ i r)).card < k := by
      rw [← hk, hset, Finset.card_insert_of_notMem hnot]; omega
    rw [ih _ hcard (pred Θ i r) hp hcp rfl]
    ring

lemma telescope' (Θ : Fin n → Finset ℝ) (i : Fin n) (c r : ℝ) (hc : c ∈ Θ i) (hr : r ∈ Θ i)
    (hcr : c ≤ r) :
    ∑ b ∈ (Θ i).filter (fun b => c < b ∧ b ≤ r), (b - pred Θ i b) = r - c :=
  telescope Θ i c hc _ r hr hcr rfl

/-- splitting the tail sum -/
lemma tail_split (Θ : Fin n → Finset ℝ) (i : Fin n) (w : ℝ → ℝ) (c r : ℝ) (hcr : c ≤ r) :
    ∑ b ∈ (Θ i).filter (c < ·), w b =
      ∑ b ∈ (Θ i).filter (fun b => c < b ∧ b ≤ r), w b + ∑ b ∈ (Θ i).filter (r < ·), w b := by
  rw [← Finset.sum_filter_add_sum_filter_not ((Θ i).filter (c < ·)) (· ≤ r)]
  congr 1
  · rw [Finset.filter_filter]
  · rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun b _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨_, h⟩; exact lt_of_not_ge h
    · intro h; exact ⟨lt_of_le_of_lt hcr h, not_le.mpr h⟩

/-- Downward induction (local downward IC + IR ⟹ the information-rent lower bound). -/
lemma rent_lower (Θ : Fin n → Finset ℝ) (i : Fin n) (U w : ℝ → ℝ)
    (hIR : ∀ c ∈ Θ i, 0 ≤ U c)
    (hstep : ∀ c ∈ Θ i, ∀ s ∈ Θ i, c < s → U s + (s - c) * w s ≤ U c) :
    ∀ (k : ℕ) (c : ℝ), c ∈ Θ i → ((Θ i).filter (c < ·)).card = k →
      ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * w b ≤ U c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hc hk
  by_cases hne : ((Θ i).filter (c < ·)).Nonempty
  · set s := ((Θ i).filter (c < ·)).min' hne with hs
    have hsm := Finset.min'_mem _ hne
    rw [← hs, Finset.mem_filter] at hsm
    have hmin : ∀ b ∈ Θ i, c < b → s ≤ b := fun b hb hcb =>
      Finset.min'_le _ b (Finset.mem_filter.mpr ⟨hb, hcb⟩)
    have hps : pred Θ i s = c := pred_of_succ Θ i c s hc hsm.2 hmin
    have hset : (Θ i).filter (c < ·) = insert s ((Θ i).filter (s < ·)) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hb, h1⟩
        rcases eq_or_lt_of_le (hmin b hb h1) with e | e
        · exact Or.inl e.symm
        · exact Or.inr ⟨hb, e⟩
      · rintro (e | ⟨hb, h1⟩)
        · subst e; exact hsm
        · exact ⟨hb, hsm.2.trans h1⟩
    have hnot : s ∉ (Θ i).filter (s < ·) := by simp
    have hcard : ((Θ i).filter (s < ·)).card < k := by
      rw [← hk, hset, Finset.card_insert_of_notMem hnot]; omega
    rw [hset, Finset.sum_insert hnot, hps]
    have := ih _ hcard s hsm.1 rfl
    have := hstep c hc s hsm.1 hsm.2
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact hIR c hc

lemma rent_lower' (Θ : Fin n → Finset ℝ) (i : Fin n) (U w : ℝ → ℝ)
    (hIR : ∀ c ∈ Θ i, 0 ≤ U c)
    (hstep : ∀ c ∈ Θ i, ∀ s ∈ Θ i, c < s → U s + (s - c) * w s ≤ U c) (c : ℝ) (hc : c ∈ Θ i) :
    ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * w b ≤ U c :=
  rent_lower Θ i U w hIR hstep _ c hc rfl

/-- The virtual-cost identity: `Σ_c f(c) (c w(c) + Σ_{b>c} (b - ρ b) w(b)) = Σ_c f(c) v(c) w(c)`. -/
lemma virtual_identity (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (i : Fin n) (w : ℝ → ℝ) :
    ∑ c ∈ Θ i, f i c * (c * w c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * w b) =
      ∑ c ∈ Θ i, f i c * (virtualCost Θ f i c * w c) := by
  have hswap : ∑ c ∈ Θ i, f i c * ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * w b =
      ∑ b ∈ Θ i, (b - pred Θ i b) * w b * ∑ c ∈ (Θ i).filter (· < b), f i c := by
    simp_rw [Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> ring
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hfb := (hf0 i b hb).ne'
  unfold virtualCost
  by_cases hne : ((Θ i).filter (· < b)).Nonempty
  · obtain ⟨hp, hpb, hmax⟩ := pred_spec Θ i b hne
    have hF : ∑ c ∈ (Θ i).filter (· < b), f i c = cdfF Θ f i (pred Θ i b) := by
      unfold cdfF
      refine Finset.sum_congr (Finset.filter_congr fun c hc => ?_) fun _ _ => rfl
      constructor
      · intro h; exact hmax c hc h
      · intro h; exact lt_of_le_of_lt h hpb
    rw [hF]
    field_simp
  · rw [pred_of_empty Θ i b hne]
    simp

end PAx


open ProcureAssort.Hotelling

open PAx

theorem solution
    {n : ℕ} (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (GCS : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ))
    (x t : Profile Θ → Fin n → ℝ) (hfeas : IsCentFeasible f X x t)
    (hopt : ∀ x' t' : Profile Θ → Fin n → ℝ, IsCentFeasible f X x' t' →
      centObj f GCS x' t' ≤ centObj f GCS x t)
    (p : Profile Θ → Fin n → ℝ)
    (h10 : ∀ θ, IsDemand GCS X (Finset.univ.filter (fun i => 0 < x θ i)) (p θ) (x θ))
    (h11 : ∀ i, ∀ c ∈ Θ i,
      interim f (fun θ => p θ i * x θ i) i c = interim f (fun θ => t θ i) i c) :
    IsDecLinFeasible f GCS X (fun θ => Finset.univ.filter (fun i => 0 < x θ i)) p x ∧
      decLinObj f GCS p x = centObj f GCS x t ∧
      optDecLin Θ f GCS X = optCent Θ f GCS X := by
  classical
  have hpart1 : IsDecLinFeasible f GCS X (fun θ => Finset.univ.filter (fun i => 0 < x θ i)) p x := by
    refine ⟨⟨?_, ?_, hfeas.2.2⟩, h10⟩
    · intro i a ha b hb
      have := hfeas.1 i a ha b hb
      simp only [utility_eq] at this ⊢
      rw [h11 i a ha, h11 i b hb]
      exact this
    · intro i a ha
      have := hfeas.2.1 i a ha
      simp only [utility_eq] at this ⊢
      rw [h11 i a ha]
      exact this
  have hpart2 : decLinObj f GCS p x = centObj f GCS x t := by
    unfold decLinObj centObj CS
    rw [expect_sub, expect_sub, expect_sum, expect_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [expect_eq_sum_interim f _ i, expect_eq_sum_interim f _ i]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [h11 i c hc]
  refine ⟨hpart1, hpart2, ?_⟩
  have hC : IsGreatest {r | ∃ x t : Profile Θ → Fin n → ℝ, IsCentFeasible f X x t ∧
      r = centObj f GCS x t} (centObj f GCS x t) := by
    refine ⟨⟨x, t, hfeas, rfl⟩, ?_⟩
    rintro r ⟨x', t', h', rfl⟩
    exact hopt x' t' h'
  have hD : IsGreatest {r | ∃ (q : Profile Θ → Finset (Fin n)) (p x : Profile Θ → Fin n → ℝ),
      IsDecLinFeasible f GCS X q p x ∧ r = decLinObj f GCS p x} (centObj f GCS x t) := by
    refine ⟨⟨_, p, x, hpart1, hpart2.symm⟩, ?_⟩
    rintro r ⟨q', p', x', h', rfl⟩
    exact hopt x' (fun θ i => p' θ i * x' θ i) h'.1
  unfold optDecLin optCent
  rw [hC.csSup_eq, hD.csSup_eq]
