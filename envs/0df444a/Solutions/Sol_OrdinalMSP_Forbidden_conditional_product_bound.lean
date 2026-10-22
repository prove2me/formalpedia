-- Prove2me | solution 1 for OrdinalMSP.Forbidden.conditional_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:08:43.801387+00:00
-- url     : https://prove2.me/submissions/ce861bcc-d96f-43d4-ad40-35a6ed75e846

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

open OrdinalMSP.Forbidden

namespace OMSPcpb

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- Arrival orders agreeing with `τ` at every (0-based) position `≥ m`. -/
def cls (m : ℕ) (τ : ArrivalOrder R) : Finset (ArrivalOrder R) :=
  Finset.univ.filter (fun σ => ∀ i : Fin (Fintype.card R), m ≤ (i : ℕ) → σ i = τ i)

lemma mem_cls {m : ℕ} {τ σ : ArrivalOrder R} :
    σ ∈ cls m τ ↔ ∀ i : Fin (Fintype.card R), m ≤ (i : ℕ) → σ i = τ i := by
  simp [cls]

lemma self_mem_cls (m : ℕ) (τ : ArrivalOrder R) : τ ∈ cls m τ := mem_cls.2 (fun _ _ => rfl)

lemma cls_symm {m : ℕ} {τ σ : ArrivalOrder R} : σ ∈ cls m τ → τ ∈ cls m σ := by
  intro h; rw [mem_cls] at *; intro i hi; exact (h i hi).symm

lemma cls_trans {m : ℕ} {τ σ ρ : ArrivalOrder R} : σ ∈ cls m τ → ρ ∈ cls m σ → ρ ∈ cls m τ := by
  intro h1 h2; rw [mem_cls] at *; intro i hi; rw [h2 i hi, h1 i hi]

lemma cls_mono {a b : ℕ} (hab : a ≤ b) {τ σ : ArrivalOrder R} : σ ∈ cls a τ → σ ∈ cls b τ := by
  intro h; rw [mem_cls] at *; intro i hi; exact h i (le_trans hab hi)

lemma card_cls_eq (m : ℕ) (τ τ' : ArrivalOrder R) : (cls m τ).card = (cls m τ').card := by
  refine Finset.card_nbij' (fun σ => σ.trans (τ.symm.trans τ'))
    (fun σ => σ.trans (τ'.symm.trans τ)) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_coe, mem_cls] at hσ ⊢
    intro i hi; simp [hσ i hi]
  · intro σ hσ
    simp only [Finset.mem_coe, mem_cls] at hσ ⊢
    intro i hi; simp [hσ i hi]
  · intro σ _; ext i; simp
  · intro σ _; ext i; simp

lemma mem_arrived (σ : ArrivalOrder R) (t : ℕ) (x : R) :
    x ∈ arrived σ t ↔ ((σ.symm x : ℕ) < t) := by
  unfold arrived
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simpa using hi
  · intro h
    exact ⟨σ.symm x, by simpa using h, by simp⟩

lemma card_arrived (σ : ArrivalOrder R) (t : ℕ) (ht : t ≤ Fintype.card R) :
    (arrived σ t).card = t := by
  unfold arrived
  rw [Finset.card_image_of_injective _ σ.injective, Fin.card_filter_val_lt]
  omega

lemma arrived_eq_of_mem_cls {a b : ℕ} (hab : a ≤ b) {τ σ : ArrivalOrder R} (h : σ ∈ cls a τ) :
    arrived σ b = arrived τ b := by
  rw [mem_cls] at h
  ext x
  rw [mem_arrived, mem_arrived]
  constructor
  · intro hx
    by_contra hc
    rw [not_lt] at hc
    have h1 : σ (τ.symm x) = x := by rw [h _ (le_trans hab hc)]; simp
    have : σ.symm x = τ.symm x := by rw [Equiv.symm_apply_eq]; exact h1.symm
    omega
  · intro hx
    by_contra hc
    rw [not_lt] at hc
    have h1 : τ (σ.symm x) = x := by rw [← h _ (le_trans hab hc)]; simp
    have : τ.symm x = σ.symm x := by rw [Equiv.symm_apply_eq]; exact h1.symm
    omega


section main

variable (F : Finset R → Finset R → R → Finset R) (Y : Finset R) (r : R) (s k t : ℕ)

/-- The event `r_j ∉ F(R_j, Y, r)` for all (0-based) `j` with `s ≤ j < m`. -/
def Ev (m : ℕ) (σ : ArrivalOrder R) : Prop :=
  ∀ j : Fin (Fintype.card R), s ≤ (j : ℕ) → (j : ℕ) < m →
    σ j ∉ F (arrived σ ((j : ℕ) + 1)) Y r

instance (m : ℕ) : DecidablePred (Ev F Y r s m) := fun σ => by unfold Ev; infer_instance

/-- The conditioning set `r_t = r`, `R_t = Y`. -/
def Sset : Finset (ArrivalOrder R) :=
  Finset.univ.filter (fun σ : ArrivalOrder R => ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y))

variable {F Y r s k t}

lemma mem_Sset {σ : ArrivalOrder R} :
    σ ∈ Sset Y r t ↔ ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y) := by
  simp [Sset]

lemma mem_Sset_of_cls {m : ℕ} (hm : m ≤ t - 1) {τ σ : ArrivalOrder R} (hτ : τ ∈ Sset Y r t)
    (hσ : σ ∈ cls m τ) : σ ∈ Sset Y r t := by
  rw [mem_Sset] at hτ ⊢
  refine ⟨?_, ?_⟩
  · have h1 : σ (τ.symm r) = r := by
      rw [mem_cls] at hσ; rw [hσ _ (by omega)]; simp
    have : σ.symm r = τ.symm r := by rw [Equiv.symm_apply_eq]; exact h1.symm
    rw [this]; exact hτ.1
  · rw [arrived_eq_of_mem_cls (by omega) hσ]; exact hτ.2

lemma ev_zero (σ : ArrivalOrder R) : Ev F Y r s 0 σ := by
  intro j _ hj; omega

lemma prod_nonneg' (a b : ℕ) :
    0 ≤ ∏ j ∈ Finset.Ico a b, max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ)) :=
  Finset.prod_nonneg (fun _ _ => le_max_left _ _)

theorem main_ind (hF : ∀ X, X ⊆ Y.erase r → F X Y r ⊆ X ∧ (F X Y r).card ≤ k)
    (hst : s + 1 ≤ t) (htn : t ≤ Fintype.card R) :
    ∀ m, m ≤ t - 1 → ∀ τ ∈ Sset Y r t,
      (∏ j ∈ Finset.Ico (s + 1) (m + 1), max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ))) *
          ((cls m τ).card : ℝ) ≤ (((cls m τ).filter (Ev F Y r s m)).card : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro _ τ _
    rw [Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty, one_mul]
    rw [Finset.filter_true_of_mem (fun σ _ => ev_zero σ)]
  | succ m ih =>
    intro hm τ hτ
    have hmn : m < Fintype.card R := by omega
    set mi : Fin (Fintype.card R) := ⟨m, hmn⟩ with hmi
    set X := arrived τ (m + 1) with hX
    have hτS := (mem_Sset.1 hτ)
    -- X ⊆ Y.erase r
    have hXsub : X ⊆ Y.erase r := by
      intro x hx
      rw [hX, mem_arrived] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · rintro rfl; omega
      · rw [← hτS.2, mem_arrived]; omega
    have hXcard : X.card = m + 1 := card_arrived τ (m + 1) (by omega)
    -- the shifted base points
    let τx : R → ArrivalOrder R := fun x => τ.trans (Equiv.swap (τ mi) x)
    have hτx_cls : ∀ x ∈ X, ∀ σ : ArrivalOrder R,
        (σ ∈ cls (m + 1) τ ∧ σ mi = x) ↔ σ ∈ cls m (τx x) := by
      intro x hx σ
      have hx' : (τ.symm x : ℕ) < m + 1 := (mem_arrived τ _ x).1 hx
      have key : ∀ i : Fin (Fintype.card R), m + 1 ≤ (i : ℕ) → τx x i = τ i := by
        intro i hi
        simp only [τx, Equiv.trans_apply]
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; have := τ.injective h; rw [this] at hi; simp [hmi] at hi
        · intro h; rw [← h] at hx'; simp at hx'; omega
      have hm' : τx x mi = x := by simp [τx]
      rw [mem_cls, mem_cls]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.eq_or_lt_of_le hi with h | h
        · have : i = mi := Fin.ext (by simp [hmi]; omega)
          rw [this, h2, hm']
        · rw [key i h, h1 i h]
      · intro h
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [h i (by omega), key i hi]
        · rw [h mi (by simp [hmi]), hm']
    have hτxS : ∀ x ∈ X, τx x ∈ Sset Y r t := by
      intro x hx
      have := (hτx_cls x hx (τx x)).2 (self_mem_cls _ _)
      exact mem_Sset_of_cls hm hτ this.1
    have hEv : ∀ x ∈ X, ∀ σ ∈ cls m (τx x),
        Ev F Y r s (m + 1) σ ↔ (Ev F Y r s m σ ∧ (s ≤ m → x ∉ F X Y r)) := by
      intro x hx σ hσ
      obtain ⟨h1, h2⟩ := (hτx_cls x hx σ).2 hσ
      have harr : arrived σ (m + 1) = X := arrived_eq_of_mem_cls le_rfl h1
      constructor
      · intro h
        refine ⟨fun j hj1 hj2 => h j hj1 (by omega), fun hsm => ?_⟩
        have := h mi (by simp [hmi]; exact hsm) (by simp [hmi])
        simp only [hmi] at this
        rw [harr, h2] at this; exact this
      · rintro ⟨h, hg⟩ j hj1 hj2
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hj | hj
        · exact h j hj1 hj
        · have hjm : j = mi := Fin.ext (by simp [hmi]; omega)
          rw [hjm, harr, h2]
          exact hg (by rw [hjm] at hj1; simpa [hmi] using hj1)
    -- maps-to for the fiberwise decomposition
    have hmaps : ∀ A : Finset (ArrivalOrder R), A ⊆ cls (m + 1) τ →
        ((A : Set (ArrivalOrder R))).MapsTo (fun σ => σ mi) X := by
      intro A hA σ hσ
      have h1 := hA hσ
      show σ mi ∈ X
      rw [hX, ← arrived_eq_of_mem_cls le_rfl h1, mem_arrived]
      simp [hmi]
    have hfib : ∀ x ∈ X, (cls (m + 1) τ).filter (fun σ => σ mi = x) = cls m (τx x) := by
      intro x hx; ext σ
      rw [Finset.mem_filter, hτx_cls x hx σ]
    set N := (cls m τ).card with hN
    have hcard : (cls (m + 1) τ).card = (m + 1) * N := by
      rw [Finset.card_eq_sum_card_fiberwise (hmaps _ subset_rfl)]
      rw [Finset.sum_congr rfl (fun x hx => by rw [hfib x hx, card_cls_eq m (τx x) τ])]
      rw [Finset.sum_const, hXcard, smul_eq_mul]
    set good := X.filter (fun x => s ≤ m → x ∉ F X Y r) with hgood
    set cm := ∏ j ∈ Finset.Ico (s + 1) (m + 1), max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ)) with hcm
    have hcm0 : 0 ≤ cm := prod_nonneg' _ _
    have hcount : cm * (N : ℝ) * (good.card : ℝ) ≤
        (((cls (m + 1) τ).filter (Ev F Y r s (m + 1))).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise
        (hmaps _ (Finset.filter_subset _ _))]
      push_cast
      have hfib2 : ∀ x ∈ X, ((cls (m + 1) τ).filter (Ev F Y r s (m + 1))).filter
          (fun σ => σ mi = x) = (cls m (τx x)).filter (Ev F Y r s (m + 1)) := by
        intro x hx
        rw [Finset.filter_comm, hfib x hx]
      rw [Finset.sum_congr rfl (fun x hx => by rw [hfib2 x hx])]
      have : cm * (N : ℝ) * (good.card : ℝ) =
          ∑ x ∈ X, (if (s ≤ m → x ∉ F X Y r) then cm * (N : ℝ) else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          hgood]
        ring
      rw [this]
      apply Finset.sum_le_sum
      intro x hx
      split_ifs with hg
      · have h1 := ih (by omega) (τx x) (hτxS x hx)
        rw [card_cls_eq m (τx x) τ] at h1
        have h2 : (cls m (τx x)).filter (Ev F Y r s (m + 1)) =
            (cls m (τx x)).filter (Ev F Y r s m) := by
          apply Finset.filter_congr
          intro σ hσ
          rw [hEv x hx σ hσ]
          exact ⟨fun h => h.1, fun h => ⟨h, hg⟩⟩
        rw [h2]; exact h1
      · exact Nat.cast_nonneg _
    refine le_trans ?_ hcount
    rw [hcard]; push_cast
    by_cases hsm : s ≤ m
    · rw [Finset.prod_Ico_succ_top (by omega)]
      rw [← hcm]
      have hgc : (m + 1 : ℝ) - k ≤ good.card := by
        have h1 : good = X \ F X Y r := by
          rw [hgood]; ext x; simp [Finset.mem_sdiff, hsm]
        have h2 := Finset.le_card_sdiff (F X Y r) X
        have h3 := (hF X hXsub).2
        rw [← h1, hXcard] at h2
        have : ((m + 1 : ℕ) : ℝ) - ((F X Y r).card : ℝ) ≤ (good.card : ℝ) := by
          have : m + 1 ≤ good.card + (F X Y r).card := by omega
          have : ((m + 1 : ℕ) : ℝ) ≤ (good.card : ℝ) + ((F X Y r).card : ℝ) := by
            exact_mod_cast this
          linarith
        have h4 : ((F X Y r).card : ℝ) ≤ k := by exact_mod_cast h3
        push_cast at this
        linarith
      have hmax : max 0 ((((m + 1 : ℕ) : ℝ) - (k : ℝ)) / ((m + 1 : ℕ) : ℝ)) * ((m : ℝ) + 1)
          ≤ good.card := by
        rcases le_total ((((m + 1 : ℕ) : ℝ) - (k : ℝ)) / ((m + 1 : ℕ) : ℝ)) 0 with h | h
        · rw [max_eq_left h, zero_mul]; exact Nat.cast_nonneg _
        · rw [max_eq_right h]
          push_cast
          rw [div_mul_cancel₀ _ (by positivity)]
          exact hgc
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      calc cm * max 0 ((((m + 1 : ℕ) : ℝ) - (k : ℝ)) / ((m + 1 : ℕ) : ℝ)) * (((m : ℝ) + 1) * N)
          = cm * N * (max 0 ((((m + 1 : ℕ) : ℝ) - (k : ℝ)) / ((m + 1 : ℕ) : ℝ)) * ((m : ℝ) + 1)) := by
            ring
        _ ≤ cm * N * good.card := by
            apply mul_le_mul_of_nonneg_left hmax (mul_nonneg hcm0 hN0)
    · have h1 : Finset.Ico (s + 1) (m + 1 + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
      have h2 : Finset.Ico (s + 1) (m + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
      have h3 : good = X := by
        rw [hgood]; apply Finset.filter_true_of_mem; intro x _ h; exact absurd h hsm
      rw [h1, Finset.prod_empty, h3, hXcard]
      rw [h2, Finset.prod_empty] at hcm
      rw [hcm]; push_cast; ring_nf; exact le_refl _

end main

end OMSPcpb

open OMSPcpb in
theorem solution {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]
    (M : Matroid R) (hE : M.E = Set.univ) (k : ℕ) (ALG : ArrivalOrder R → ℕ → Finset R)
    (hALG : HasForbiddenSets M k ALG) (r : R) (hr : r ∈ opt M Finset.univ)
    (s t : ℕ) (hst : s + 1 ≤ t) (htn : t ≤ Fintype.card R)
    (Y : Finset R) (hY : Y.card = t) (hrY : r ∈ Y) :
    (∏ j ∈ Finset.Ico (s + 1) t, max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ))) *
        ((Finset.univ.filter (fun σ : ArrivalOrder R =>
            ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y))).card : ℝ) ≤
      ((Finset.univ.filter (fun σ : ArrivalOrder R =>
            ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y) ∧ r ∈ ALG σ s)).card : ℝ) := by
  obtain ⟨F, hFb, hFsel⟩ := hALG.forbidden
  -- Lemma 4: r ∈ OPT(Y)
  have hropt : r ∈ opt M Y := by
    classical
    unfold opt at hr ⊢
    rw [Finset.mem_filter] at hr ⊢
    refine ⟨hrY, fun hc => hr.2 ?_⟩
    refine M.closure_subset_closure ?_ hc
    intro q hq
    exact ⟨Finset.mem_univ _, hq.2⟩
  have hF : ∀ X, X ⊆ Y.erase r → F X Y r ⊆ X ∧ (F X Y r).card ≤ k :=
    fun X hX => hFb X Y r hropt hX
  set c := ∏ j ∈ Finset.Ico (s + 1) t, max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ)) with hc
  have hc' : c = ∏ j ∈ Finset.Ico (s + 1) (t - 1 + 1), max 0 (((j : ℝ) - (k : ℝ)) / (j : ℝ)) := by
    rw [hc]; congr 2; omega
  have hS : Finset.univ.filter (fun σ : ArrivalOrder R =>
            ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y)) = Sset Y r t := rfl
  rw [hS]
  -- step 1: the event implies selection
  have hsub : (Sset Y r t).filter (Ev F Y r s (t - 1)) ⊆ Finset.univ.filter
      (fun σ : ArrivalOrder R => ((σ.symm r : ℕ) = t - 1 ∧ arrived σ t = Y) ∧ r ∈ ALG σ s) := by
    intro σ hσ
    rw [Finset.mem_filter, mem_Sset] at hσ
    obtain ⟨⟨h1, h2⟩, hev⟩ := hσ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨h1, h2⟩, ?_⟩
    have hi : σ (σ.symm r) = r := by simp
    have ht1 : (σ.symm r : ℕ) + 1 = t := by omega
    have := hFsel σ s (σ.symm r) (by omega) (by rw [hi, ht1, h2]; exact hropt) (by
      intro j hj1 hj2
      rw [hi, ht1, h2]
      exact hev j hj1 (by omega))
    rwa [hi] at this
  refine le_trans ?_ (Nat.cast_le.2 (Finset.card_le_card hsub))
  -- step 2: double counting over classes
  rcases (Sset Y r t).eq_empty_or_nonempty with hemp | ⟨τ0, hτ0⟩
  · rw [hemp]; simp
  set N := (cls (t - 1) τ0).card with hN
  have hNpos : 0 < N := Finset.card_pos.2 ⟨τ0, self_mem_cls _ _⟩
  have hind := main_ind (F := F) (Y := Y) (r := r) (s := s) (k := k) (t := t) hF hst htn
    (t - 1) le_rfl
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := Sset Y r t) (t := (Sset Y r t).filter (Ev F Y r s (t - 1)))
    (fun τ σ => σ ∈ cls (t - 1) τ)
  have hA : ∀ τ ∈ Sset Y r t, ((Sset Y r t).filter (Ev F Y r s (t - 1))).bipartiteAbove
      (fun τ σ => σ ∈ cls (t - 1) τ) τ = (cls (t - 1) τ).filter (Ev F Y r s (t - 1)) := by
    intro τ hτ; ext σ
    simp only [Finset.mem_bipartiteAbove, Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨⟨mem_Sset_of_cls le_rfl hτ h2, h1⟩, h2⟩
  have hB : ∀ σ ∈ (Sset Y r t).filter (Ev F Y r s (t - 1)),
      ((Sset Y r t).bipartiteBelow (fun τ σ => σ ∈ cls (t - 1) τ) σ).card = N := by
    intro σ hσ
    have hσS := (Finset.mem_filter.1 hσ).1
    have : (Sset Y r t).bipartiteBelow (fun τ σ => σ ∈ cls (t - 1) τ) σ = cls (t - 1) σ := by
      ext τ
      simp only [Finset.mem_bipartiteBelow]
      constructor
      · rintro ⟨_, h⟩; exact cls_symm h
      · intro h; exact ⟨mem_Sset_of_cls le_rfl hσS h, cls_symm h⟩
    rw [this, hN, card_cls_eq]
  rw [Finset.sum_congr rfl (fun τ hτ => by rw [hA τ hτ]), Finset.sum_congr rfl hB,
    Finset.sum_const, smul_eq_mul] at hdc
  have hsum : ∑ τ ∈ Sset Y r t, c * (N : ℝ) ≤
      ∑ τ ∈ Sset Y r t, (((cls (t - 1) τ).filter (Ev F Y r s (t - 1))).card : ℝ) := by
    apply Finset.sum_le_sum
    intro τ hτ
    have := hind τ hτ
    rw [← hc', card_cls_eq (t - 1) τ τ0, ← hN] at this
    exact this
  rw [Finset.sum_const, nsmul_eq_mul, ← Nat.cast_sum, hdc] at hsum
  push_cast at hsum
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  nlinarith
