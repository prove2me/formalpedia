-- Prove2me | solution 1 for ProcureAssort.Hotelling.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T03:42:33.342119+00:00
-- url     : https://prove2.me/submissions/7fcafac7-a4d9-4c10-9ee6-d1899d473122

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

namespace PAx

lemma expect_CS {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ) (GCS : (Fin n → ℝ) → ℝ)
    (y : Profile Θ → Fin n → ℝ) :
    expect f (fun θ => CS GCS (y θ) (vvec Θ f θ)) =
      expect f (fun θ => GCS (y θ)) - ∑ i, expect f (fun θ => virtualCost Θ f i (θ i) * y θ i) := by
  unfold CS vvec
  rw [expect_sub, expect_sum]

lemma centObj_eq {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ) (GCS : (Fin n → ℝ) → ℝ)
    (x t : Profile Θ → Fin n → ℝ) :
    centObj f GCS x t = expect f (fun θ => GCS (x θ)) - ∑ i, expect f (fun θ => t θ i) := by
  unfold centObj
  rw [expect_sub, expect_sum]

/-- Myerson lower bound on expected transfers of any IC/IR mechanism. -/
lemma myerson_lower {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (X : Set (Fin n → ℝ))
    (x t : Profile Θ → Fin n → ℝ) (hfeas : IsCentFeasible f X x t) (i : Fin n) :
    expect f (fun θ => virtualCost Θ f i (θ i) * x θ i) ≤ expect f (fun θ => t θ i) := by
  obtain ⟨hIC, hIR, -⟩ := hfeas
  rw [expect_eq_sum_interim f _ i, expect_eq_sum_interim f _ i]
  simp_rw [interim_fn_mul f (virtualCost Θ f i)]
  rw [← virtual_identity Θ f hf0 i (fun c => interim f (fun θ => x θ i) i c)]
  refine Finset.sum_le_sum fun c hc => mul_le_mul_of_nonneg_left ?_ (hf0 i c hc).le
  have key := rent_lower' Θ i (fun c => utility f x t i c c)
    (fun c => interim f (fun θ => x θ i) i c) (fun c hc => hIR i c hc)
    (fun c hc s hs _ => by
      have := hIC i c hc s hs
      simp only [utility_eq] at this ⊢
      linarith) c hc
  rw [utility_eq] at key
  linarith

end PAx

open PAx

theorem PAx.prop31
    {n : ℕ} (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (GCS : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ))
    (hX : ∀ y ∈ X, ∀ i, 0 ≤ y i)
    (x t : Profile Θ → Fin n → ℝ)
    (hcond1 : ∀ θ, x θ ∈ X ∧ ∀ y ∈ X, CS GCS y (vvec Θ f θ) ≤ CS GCS (x θ) (vvec Θ f θ))
    (hcond2 : ∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≤ b →
      interim f (fun θ => x θ i) i b ≤ interim f (fun θ => x θ i) i a)
    (hcond3 : ∀ i, ∀ c ∈ Θ i, interim f (fun θ => t θ i) i c =
      c * interim f (fun θ => x θ i) i c +
        ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * interim f (fun θ => x θ i) i b) :
    IsCentFeasible f X x t ∧
      ∀ x' t' : Profile Θ → Fin n → ℝ, IsCentFeasible f X x' t' →
        centObj f GCS x' t' ≤ centObj f GCS x t := by
  classical
  have hxnn : ∀ θ i, 0 ≤ x θ i := fun θ i => hX _ (hcond1 θ).1 i
  have hXnn : ∀ i c, 0 ≤ interim f (fun θ => x θ i) i c :=
    fun i c => interim_nonneg f hf0 _ (fun θ => hxnn θ i) i c
  have hfeas : IsCentFeasible f X x t := by
    refine ⟨?_, ?_, fun θ => (hcond1 θ).1⟩
    · intro i a ha b hb
      rw [utility_eq, utility_eq, hcond3 i a ha, hcond3 i b hb]
      rcases le_total a b with hab | hab
      · rw [tail_split Θ i _ a b hab]
        have htel := telescope' Θ i a b ha hb hab
        have : (b - a) * interim f (fun θ => x θ i) i b ≤
            ∑ c ∈ (Θ i).filter (fun c => a < c ∧ c ≤ b),
              (c - pred Θ i c) * interim f (fun θ => x θ i) i c := by
          rw [← htel, Finset.sum_mul]
          refine Finset.sum_le_sum fun c hc => ?_
          rw [Finset.mem_filter] at hc
          exact mul_le_mul_of_nonneg_left (hcond2 i c hc.1 b hb hc.2.2)
            (sub_nonneg.mpr (pred_le Θ i c))
        linarith
      · rw [tail_split Θ i _ b a hab]
        have htel := telescope' Θ i b a hb ha hab
        have : ∑ c ∈ (Θ i).filter (fun c => b < c ∧ c ≤ a),
              (c - pred Θ i c) * interim f (fun θ => x θ i) i c ≤
            (a - b) * interim f (fun θ => x θ i) i b := by
          rw [← htel, Finset.sum_mul]
          refine Finset.sum_le_sum fun c hc => ?_
          rw [Finset.mem_filter] at hc
          exact mul_le_mul_of_nonneg_left (hcond2 i b hb c hc.1 hc.2.1.le)
            (sub_nonneg.mpr (pred_le Θ i c))
        linarith
    · intro i a ha
      rw [utility_eq, hcond3 i a ha]
      have : 0 ≤ ∑ b ∈ (Θ i).filter (a < ·), (b - pred Θ i b) * interim f (fun θ => x θ i) i b :=
        Finset.sum_nonneg fun b _ => mul_nonneg (sub_nonneg.mpr (pred_le Θ i b)) (hXnn i b)
      linarith
  refine ⟨hfeas, fun x' t' hfeas' => ?_⟩
  have hEq : ∀ i, expect f (fun θ => t θ i) =
      expect f (fun θ => virtualCost Θ f i (θ i) * x θ i) := by
    intro i
    rw [expect_eq_sum_interim f _ i, expect_eq_sum_interim f _ i]
    simp_rw [interim_fn_mul f (virtualCost Θ f i)]
    rw [← virtual_identity Θ f hf0 i (fun c => interim f (fun θ => x θ i) i c)]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [hcond3 i c hc]
  have h1 : centObj f GCS x' t' ≤ expect f (fun θ => CS GCS (x' θ) (vvec Θ f θ)) := by
    rw [centObj_eq, expect_CS]
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
      myerson_lower Θ f hf0 X x' t' hfeas' i
    linarith
  have h2 : expect f (fun θ => CS GCS (x' θ) (vvec Θ f θ)) ≤
      expect f (fun θ => CS GCS (x θ) (vvec Θ f θ)) :=
    expect_mono f hf0 _ _ fun θ => (hcond1 θ).2 _ (hfeas'.2.2 θ)
  have h3 : expect f (fun θ => CS GCS (x θ) (vvec Θ f θ)) = centObj f GCS x t := by
    rw [centObj_eq, expect_CS]
    simp_rw [hEq]
  linarith


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

namespace PAQ

variable {n : ℕ}

lemma probOthers_update (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (θ : Profile Θ) (i : Fin n)
    (b : ↥(Θ i)) : probOthers f i (Function.update θ i b) = probOthers f i θ := by
  unfold probOthers
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma interim_shift (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (g : Profile Θ → ℝ) (i : Fin n)
    (a b : ↥(Θ i)) :
    interim f (fun θ => g (Function.update θ i b)) i a = interim f g i b := by
  classical
  unfold interim
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun θ => Function.update θ i b) (fun θ => Function.update θ i a)
    ?_ ?_ ?_ ?_ ?_
  · intro θ _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [Function.update_self]⟩
  · intro θ _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [Function.update_self]⟩
  · intro θ hθ
    rw [Finset.mem_filter] at hθ
    show Function.update (Function.update θ i b) i a = θ
    rw [Function.update_idem, Function.update_eq_self_iff]
    exact (Subtype.ext hθ.2).symm
  · intro θ hθ
    rw [Finset.mem_filter] at hθ
    show Function.update (Function.update θ i a) i b = θ
    rw [Function.update_idem, Function.update_eq_self_iff]
    exact (Subtype.ext hθ.2).symm
  · intro θ _
    show probOthers f i θ * g (Function.update θ i b) =
      probOthers f i (Function.update θ i b) * g (Function.update θ i b)
    rw [probOthers_update]

lemma interim_add (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} (g h : Profile Θ → ℝ) (i : Fin n)
    (c : ℝ) : interim f (fun θ => g θ + h θ) i c = interim f g i c + interim f h i c := by
  unfold interim
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun θ _ => ?_
  split_ifs <;> ring

lemma interim_sum (f : Fin n → ℝ → ℝ) {Θ : Fin n → Finset ℝ} {ι : Type*} (s : Finset ι)
    (g : ι → Profile Θ → ℝ) (i : Fin n) (c : ℝ) :
    interim f (fun θ => ∑ k ∈ s, g k θ) i c = ∑ k ∈ s, interim f (g k) i c := by
  unfold interim
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun θ _ => ?_
  split_ifs
  · rw [Finset.mul_sum]
  · simp

section
variable (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ)
    (f : Fin n → ℝ → ℝ)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
include hn hreg hℓ hℓ0 hℓ1 hδ

lemma xstar_opt (θ : Profile Θ) :
    xstar Θ f ℓ δ θ ∈ simplex n ∧ ∀ y ∈ simplex n,
      CS (hotGCS ℓ δ) y (vvec Θ f θ) ≤ CS (hotGCS ℓ δ) (xstar Θ f ℓ δ θ) (vvec Θ f θ) := by
  have := PAH.hotDemand_isDemand' n hn ℓ hℓ hℓ0 hℓ1 δ hδ (vvec Θ f θ)
  exact ⟨this.1, fun y hy => this.2.2 y hy (fun i h => absurd (Finset.mem_univ i) h)⟩

lemma xstar_update_le (θ : Profile Θ) (i : Fin n) (b : ↥(Θ i)) (hb : (θ i : ℝ) ≤ b) :
    xstar Θ f ℓ δ (Function.update θ i b) i ≤ xstar Θ f ℓ δ θ i := by
  classical
  rcases eq_or_lt_of_le hb with h | h
  · have : Function.update θ i b = θ := by
      rw [Function.update_eq_self_iff]; exact Subtype.ext h.symm
    rw [this]
  · set θ' := Function.update θ i b
    set v := vvec Θ f θ
    set v' := vvec Θ f θ'
    set y := xstar Θ f ℓ δ θ
    set y' := xstar Θ f ℓ δ θ'
    have hvi : v i < v' i := by
      simp only [v, v', vvec, θ', Function.update_self]
      exact hreg i (θ i).2 b.2 h
    have hsum : ∀ z : Fin n → ℝ, ∑ j, v' j * z j - ∑ j, v j * z j = (v' i - v i) * z i := by
      intro z
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · ring
      · intro j _ hj
        simp only [v, v', vvec, θ', Function.update_of_ne hj]; ring
      · simp
    obtain ⟨hy, hyo⟩ := xstar_opt n hn Θ f hreg ℓ hℓ hℓ0 hℓ1 δ hδ θ
    obtain ⟨hy', hyo'⟩ := xstar_opt n hn Θ f hreg ℓ hℓ hℓ0 hℓ1 δ hδ θ'
    have h1 := hyo y' hy'
    have h2 := hyo' y hy
    unfold CS at h1 h2
    have e1 := hsum y
    have e2 := hsum y'
    have : (v' i - v i) * y' i ≤ (v' i - v i) * y i := by linarith
    exact le_of_mul_le_mul_left this (by linarith)

lemma xstar_nonneg (θ : Profile Θ) (i : Fin n) : 0 ≤ xstar Θ f ℓ δ θ i :=
  (xstar_opt n hn Θ f hreg ℓ hℓ hℓ0 hℓ1 δ hδ θ).1.1 i

end

end PAQ

open PAQ PAx

theorem PAQ.prop32
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    IsCentFeasible f (simplex n) (xstar Θ f ℓ δ) (tstar Θ (xstar Θ f ℓ δ)) ∧
    (∀ θ, xstar Θ f ℓ δ θ ∈ simplex n ∧ ∀ y ∈ simplex n,
      CS (hotGCS ℓ δ) y (vvec Θ f θ) ≤ CS (hotGCS ℓ δ) (xstar Θ f ℓ δ θ) (vvec Θ f θ)) ∧
    (∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≤ b → interim f (fun θ => xstar Θ f ℓ δ θ i) i b ≤ interim f (fun θ => xstar Θ f ℓ δ θ i) i a) ∧
    (∀ i, ∀ c ∈ Θ i, interim f (fun θ => tstar Θ (xstar Θ f ℓ δ) θ i) i c =
      c * interim f (fun θ => xstar Θ f ℓ δ θ i) i c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * interim f (fun θ => xstar Θ f ℓ δ θ i) i b) ∧
    (∀ (θ : Profile Θ) (i : Fin n),
      (θ i : ℝ) * xstar Θ f ℓ δ θ i ≤ tstar Θ (xstar Θ f ℓ δ) θ i ∧
      (xstar Θ f ℓ δ θ i = 0 → tstar Θ (xstar Θ f ℓ δ) θ i = 0)) := by
  classical
  set x := xstar Θ f ℓ δ with hx
  set t := tstar Θ x with ht
  have hc1 := xstar_opt n hn Θ f hreg ℓ hℓ hℓ0 hℓ1 δ hδ
  have hupd := xstar_update_le n hn Θ f hreg ℓ hℓ hℓ0 hℓ1 δ hδ
  have hxnn := xstar_nonneg n hn Θ f hreg ℓ hℓ hℓ0 hℓ1 δ hδ
  have hc2 : ∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≤ b →
      interim f (fun θ => x θ i) i b ≤ interim f (fun θ => x θ i) i a := by
    intro i a ha b hb hab
    have hs := interim_shift f (fun θ => x θ i) i ⟨a, ha⟩ ⟨b, hb⟩
    simp only at hs
    rw [← hs]
    unfold interim
    refine Finset.sum_le_sum fun θ _ => ?_
    split_ifs with h
    · refine mul_le_mul_of_nonneg_left ?_ ?_
      · exact hupd θ i ⟨b, hb⟩ (by rw [h]; exact hab)
      · unfold probOthers
        exact Finset.prod_nonneg fun j _ => (hf0 j _ (θ j).2).le
    · exact le_rfl
  have hc3 : ∀ i, ∀ c ∈ Θ i, interim f (fun θ => t θ i) i c =
      c * interim f (fun θ => x θ i) i c +
        ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * interim f (fun θ => x θ i) i b := by
    intro i c hc
    have hfun : (fun θ => t θ i) = fun θ => (fun s : ℝ => s) (θ i) * x θ i +
        ∑ b : ↥(Θ i), (fun s : ℝ => if s < (b : ℝ) then ((b : ℝ) - pred Θ i b) else 0) (θ i) *
          x (Function.update θ i b) i := by
      funext θ
      simp only [t, tstar]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> ring
    rw [hfun, interim_add, interim_sum, interim_fn_mul f (fun s => s) (fun θ => x θ i) i c]
    congr 1
    rw [Finset.sum_filter, ← Finset.sum_coe_sort (Θ i)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [interim_fn_mul f (fun s : ℝ => if s < (b : ℝ) then ((b : ℝ) - pred Θ i b) else 0)
      (fun θ => x (Function.update θ i b) i) i c]
    have hs := interim_shift f (fun θ => x θ i) i ⟨c, hc⟩ b
    simp only at hs
    rw [hs]
    split_ifs <;> ring
  have hX : ∀ y ∈ simplex n, ∀ i, 0 ≤ y i := fun y hy i => hy.1 i
  refine ⟨(prop31 Θ hΘ f hf0 hf1 hreg (hotGCS ℓ δ) (simplex n) hX x t hc1 hc2 hc3).1,
    hc1, hc2, hc3, fun θ i => ⟨?_, fun h0 => ?_⟩⟩
  · simp only [t, tstar]
    have : 0 ≤ ∑ b : ↥(Θ i), (if (θ i : ℝ) < b then ((b : ℝ) - pred Θ i b) *
        x (Function.update θ i b) i else 0) := by
      refine Finset.sum_nonneg fun b _ => ?_
      split_ifs
      · exact mul_nonneg (sub_nonneg.mpr (pred_le Θ i b)) (hxnn _ i)
      · exact le_rfl
    linarith
  · simp only [t, tstar]
    rw [h0, mul_zero, zero_add]
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hlt
    · have : x (Function.update θ i b) i = 0 :=
        le_antisymm (h0 ▸ hupd θ i b hlt.le) (hxnn _ i)
      rw [this, mul_zero]
    · rfl


open ProcureAssort.Hotelling

theorem solution
    (n : ℕ) (hn : 2 ≤ n)
    (Θ : Fin n → Finset ℝ) (hΘ : ∀ i, ∀ c ∈ Θ i, 0 < c)
    (f : Fin n → ℝ → ℝ) (hf0 : ∀ i, ∀ c ∈ Θ i, 0 < f i c) (hf1 : ∀ i, ∑ c ∈ Θ i, f i c = 1)
    (hreg : ∀ i, StrictMonoOn (virtualCost Θ f i) ((Θ i : Finset ℝ) : Set ℝ))
    (ℓ : Fin n → ℝ) (hℓ : StrictMono ℓ) (hℓ0 : ∀ i, 0 ≤ ℓ i) (hℓ1 : ∀ i, ℓ i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    IsCentFeasible f (simplex n) (xstar Θ f ℓ δ) (tstar Θ (xstar Θ f ℓ δ)) ∧
    (∀ θ, xstar Θ f ℓ δ θ ∈ simplex n ∧ ∀ y ∈ simplex n,
      CS (hotGCS ℓ δ) y (vvec Θ f θ) ≤ CS (hotGCS ℓ δ) (xstar Θ f ℓ δ θ) (vvec Θ f θ)) ∧
    (∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, a ≤ b → interim f (fun θ => xstar Θ f ℓ δ θ i) i b ≤ interim f (fun θ => xstar Θ f ℓ δ θ i) i a) ∧
    (∀ i, ∀ c ∈ Θ i, interim f (fun θ => tstar Θ (xstar Θ f ℓ δ) θ i) i c =
      c * interim f (fun θ => xstar Θ f ℓ δ θ i) i c + ∑ b ∈ (Θ i).filter (c < ·), (b - pred Θ i b) * interim f (fun θ => xstar Θ f ℓ δ θ i) i b) ∧
    (∀ (θ : Profile Θ) (i : Fin n),
      (θ i : ℝ) * xstar Θ f ℓ δ θ i ≤ tstar Θ (xstar Θ f ℓ δ) θ i ∧
      (xstar Θ f ℓ δ θ i = 0 → tstar Θ (xstar Θ f ℓ δ) θ i = 0)) :=
  PAQ.prop32 n hn Θ hΘ f hf0 hf1 hreg ℓ hℓ hℓ0 hℓ1 δ hδ
