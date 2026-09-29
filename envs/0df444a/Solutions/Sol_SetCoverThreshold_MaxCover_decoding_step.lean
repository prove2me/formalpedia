-- Prove2me | solution 1 for SetCoverThreshold.MaxCover.decoding_step
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:29:00.042781+00:00
-- url     : https://prove2.me/submissions/0d70fa8d-1029-45ac-bca4-7654adf5395d

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

/-- A default canonical answer on one coordinate. -/
def aux_dc_defCoord (φ : Formula5) : (x : Fin φ.M ⊕ ℕ) → CoordAnswer φ x
  | Sum.inl c => (⟨fun p => (φ.clause c p).1, ⟨0, rfl⟩⟩ : {b : Fin 3 → Bool // φ.LocalSat c b})
  | Sum.inr _ => (false : Bool)

/-- A default canonical answer to a question. -/
def aux_dc_defAns (φ : Formula5) {ℓ : ℕ} (q : Question φ ℓ) : Answer φ q :=
  fun j => aux_dc_defCoord φ (q j)

/-- The (prover, possible question) pairs. -/
abbrev aux_dc_X (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool) : Type :=
  Σ i : Fin k, possibleQuestions φ code i

open Classical in
/-- The answers `a` with `S_(q,a,i) ∈ C`. -/
noncomputable def aux_dc_A (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (C : Finset (SetIdx φ code)) (x : aux_dc_X φ code) : Finset (Answer φ x.2.1) :=
  Finset.univ.filter (fun a => (⟨x.1, x.2, a⟩ : SetIdx φ code) ∈ C)

open Classical in
/-- The support of the random answer of prover `x.1` on question `x.2`. -/
noncomputable def aux_dc_S (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (C : Finset (SetIdx φ code)) (x : aux_dc_X φ code) : Finset (Answer φ x.2.1) :=
  if (aux_dc_A φ code C x).Nonempty then aux_dc_A φ code C x else {aux_dc_defAns φ x.2.1}

open Classical in
/-- The strategies determined by a choice function. -/
noncomputable def aux_dc_strat (φ : Formula5) {k ℓ : ℕ} (code : Fin k → Fin ℓ → Bool)
    (t : (x : aux_dc_X φ code) → Answer φ x.2.1) : Fin k → Strategy φ ℓ :=
  fun i q => if h : q ∈ possibleQuestions φ code i then t ⟨i, ⟨q, h⟩⟩ else aux_dc_defAns φ q

theorem aux_dc_count {X : Type*} [Fintype X] [DecidableEq X] {β : X → Type*}
    [∀ x, DecidableEq (β x)] (S : ∀ x, Finset (β x)) (x y : X) (hxy : x ≠ y)
    (a : β x) (b : β y) (ha : a ∈ S x) (hb : b ∈ S y) :
    ((Fintype.piFinset S).filter (fun t => t x = a ∧ t y = b)).card * ((S x).card * (S y).card)
      = (Fintype.piFinset S).card := by
  have h1 : (Fintype.piFinset S).filter (fun t => t x = a ∧ t y = b) =
      Fintype.piFinset (Function.update (Function.update S x {a}) y {b}) := by
    ext t
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h, h1, h2⟩ z
      by_cases hzy : z = y
      · subst hzy; simp [h2]
      · rw [Function.update_of_ne hzy]
        by_cases hzx : z = x
        · subst hzx; simp [h1]
        · rw [Function.update_of_ne hzx]; exact h z
    · intro h
      have hy := h y
      rw [Function.update_self, Finset.mem_singleton] at hy
      have hx := h x
      rw [Function.update_of_ne hxy, Function.update_self, Finset.mem_singleton] at hx
      refine ⟨fun z => ?_, hx, hy⟩
      by_cases hzy : z = y
      · subst hzy; rw [hy]; exact hb
      · by_cases hzx : z = x
        · subst hzx; rw [hx]; exact ha
        · have := h z
          rwa [Function.update_of_ne hzy, Function.update_of_ne hzx] at this
  rw [h1, Fintype.card_piFinset, Fintype.card_piFinset]
  have h2 : ∀ z, (S z).card = (Function.update (Function.update S x {a}) y {b} z).card *
      ((if z = x then (S x).card else 1) * (if z = y then (S y).card else 1)) := by
    intro z
    by_cases hzy : z = y
    · subst hzy
      simp [Function.update_self, Ne.symm hxy]
    · by_cases hzx : z = x
      · subst hzx; simp [hzy]
      · simp [hzx, hzy]
  rw [Finset.prod_congr rfl (fun z _ => h2 z), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq']

end SetCoverThreshold.MaxCover

open SetCoverThreshold.MaxCover

theorem solution (ε : ℝ) (hε : 0 < ε) (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool)
    (φ : Formula5) (C : Finset (SetIdx φ code))
    (hgood : ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) ≤ (goodCount φ code ε C : ℝ)) :
    ∃ strat : Fin k → Strategy φ ℓ,
      ε / 3 * (ε / (3 * k)) ^ 2 * (Fintype.card (RandString φ ℓ) : ℝ) ≤
        (weakAcceptCount φ code strat : ℝ) := by
  classical
  set S := aux_dc_S φ code C with hSdef
  set T := Fintype.piFinset S with hTdef
  set δ : ℝ := ε / (3 * k) with hδ
  have hTne : T.Nonempty := by
    rw [hTdef, Fintype.piFinset_nonempty]
    intro x
    rw [hSdef]; unfold aux_dc_S
    split_ifs with h
    · exact h
    · exact Finset.singleton_nonempty _
  have key : ∀ r, IsGood φ code ε C r →
      (T.card : ℝ) * δ ^ 2 ≤
        ((T.filter (fun t => WeakAccept φ code (aux_dc_strat φ code t) r)).card : ℝ) := by
    intro r hr
    obtain ⟨hw, s, hs, s', hs', hne, hq, hq', hbits⟩ := hr
    obtain ⟨i, ⟨q, hqmem⟩, a⟩ := s
    obtain ⟨i', ⟨q', hqmem'⟩, a'⟩ := s'
    simp only at hne hq hq' hbits
    subst hq hq'
    have hk : (0 : ℝ) < k := by exact_mod_cast Fin.pos i
    let x : aux_dc_X φ code := ⟨i, ⟨question φ code r i, hqmem⟩⟩
    let x' : aux_dc_X φ code := ⟨i', ⟨question φ code r i', hqmem'⟩⟩
    have hxx : x ≠ x' := by
      intro h; exact hne (congrArg Sigma.fst h)
    have haA : a ∈ aux_dc_A φ code C x := by
      unfold aux_dc_A; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hs
    have haA' : a' ∈ aux_dc_A φ code C x' := by
      unfold aux_dc_A; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hs'
    have hSx : S x = aux_dc_A φ code C x := by
      rw [hSdef]; unfold aux_dc_S; rw [if_pos ⟨a, haA⟩]
    have hSx' : S x' = aux_dc_A φ code C x' := by
      rw [hSdef]; unfold aux_dc_S; rw [if_pos ⟨a', haA'⟩]
    -- the size bound
    have hbound : ∀ (y : aux_dc_X φ code), y.2.1 = question φ code r y.1 →
        ((aux_dc_A φ code C y).card : ℝ) ≤ 3 * k / ε := by
      intro y hy
      refine le_trans ?_ hw
      have : (aux_dc_A φ code C y).card ≤ setWeight φ code C r := by
        unfold setWeight
        refine Finset.card_le_card_of_injOn (fun b => (⟨y.1, y.2, b⟩ : SetIdx φ code)) ?_ ?_
        · intro b hb
          simp only [aux_dc_A, Finset.coe_filter, Finset.mem_univ, true_and,
            Set.mem_ofPred_eq] at hb
          simp only [Finset.coe_filter, Set.mem_ofPred_eq]
          exact ⟨hb, hy⟩
        · intro b₁ _ b₂ _ h
          simpa using h
      exact_mod_cast this
    have hb1 : ((S x).card : ℝ) * δ ≤ 1 := by
      rw [hSx]
      have := hbound x rfl
      calc ((aux_dc_A φ code C x).card : ℝ) * δ ≤ 3 * k / ε * δ :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 1 := by rw [hδ]; field_simp
    have hb2 : ((S x').card : ℝ) * δ ≤ 1 := by
      rw [hSx']
      have := hbound x' rfl
      calc ((aux_dc_A φ code C x').card : ℝ) * δ ≤ 3 * k / ε * δ :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 1 := by rw [hδ]; field_simp
    have hcount := aux_dc_count S x x' hxx a a' (hSx ▸ haA) (hSx' ▸ haA')
    have hsub : (T.filter (fun t => t x = a ∧ t x' = a')).card ≤
        (T.filter (fun t => WeakAccept φ code (aux_dc_strat φ code t) r)).card := by
      apply Finset.card_le_card
      intro t ht
      simp only [Finset.mem_filter] at ht ⊢
      obtain ⟨htT, hta, hta'⟩ := ht
      refine ⟨htT, i, i', hne, ?_⟩
      have e1 : aux_dc_strat φ code t i (question φ code r i) = a := by
        simp only [aux_dc_strat, dif_pos hqmem]; exact hta
      have e2 : aux_dc_strat φ code t i' (question φ code r i') = a' := by
        simp only [aux_dc_strat, dif_pos hqmem']; exact hta'
      unfold induced
      rw [e1, e2]
      exact hbits
    have hcountR : ((T.filter (fun t => t x = a ∧ t x' = a')).card : ℝ) *
        (((S x).card : ℝ) * ((S x').card : ℝ)) = (T.card : ℝ) := by
      exact_mod_cast hcount
    have hsubR : ((T.filter (fun t => t x = a ∧ t x' = a')).card : ℝ) ≤
        ((T.filter (fun t => WeakAccept φ code (aux_dc_strat φ code t) r)).card : ℝ) := by
      exact_mod_cast hsub
    have hn1 : (0 : ℝ) ≤ ((S x).card : ℝ) * δ := by positivity
    have hn2 : (0 : ℝ) ≤ ((S x').card : ℝ) * δ := by positivity
    have hprod : ((S x).card : ℝ) * δ * (((S x').card : ℝ) * δ) ≤ 1 :=
      mul_le_one₀ hb1 hn2 hb2
    set c := ((T.filter (fun t => t x = a ∧ t x' = a')).card : ℝ)
    have hc0 : 0 ≤ c := by positivity
    calc (T.card : ℝ) * δ ^ 2 = c * (((S x).card : ℝ) * δ * (((S x').card : ℝ) * δ)) := by
          rw [← hcountR]; ring
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hprod hc0
      _ = c := mul_one c
      _ ≤ _ := hsubR
  -- double counting
  have hswap : ∑ t ∈ T, (weakAcceptCount φ code (aux_dc_strat φ code t) : ℝ) =
      ∑ r, ((T.filter (fun t => WeakAccept φ code (aux_dc_strat φ code t) r)).card : ℝ) := by
    simp only [weakAcceptCount, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_comm
  have hlow : (T.card : ℝ) * ((goodCount φ code ε C : ℝ) * δ ^ 2) ≤
      ∑ t ∈ T, (weakAcceptCount φ code (aux_dc_strat φ code t) : ℝ) := by
    rw [hswap]
    calc (T.card : ℝ) * ((goodCount φ code ε C : ℝ) * δ ^ 2)
        = ∑ r ∈ Finset.univ.filter (IsGood φ code ε C), (T.card : ℝ) * δ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          unfold goodCount
          ring
      _ ≤ ∑ r ∈ Finset.univ.filter (IsGood φ code ε C),
            ((T.filter (fun t => WeakAccept φ code (aux_dc_strat φ code t) r)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          exact key r hr
      _ ≤ ∑ r, ((T.filter (fun t => WeakAccept φ code (aux_dc_strat φ code t) r)).card : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro r _ _
          positivity
  obtain ⟨t, _, ht⟩ := Finset.exists_le_of_sum_le hTne
    (f := fun _ => (goodCount φ code ε C : ℝ) * δ ^ 2)
    (g := fun t => (weakAcceptCount φ code (aux_dc_strat φ code t) : ℝ))
    (by rw [Finset.sum_const, nsmul_eq_mul]; exact hlow)
  refine ⟨aux_dc_strat φ code t, ?_⟩
  calc ε / 3 * δ ^ 2 * (Fintype.card (RandString φ ℓ) : ℝ)
      = ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) * δ ^ 2 := by ring
    _ ≤ (goodCount φ code ε C : ℝ) * δ ^ 2 := mul_le_mul_of_nonneg_right hgood (sq_nonneg _)
    _ ≤ _ := ht
