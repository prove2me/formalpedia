-- Prove2me | solution 1 for ReentrantScheduling.FBFS.Supplement.theorem4_ls_population
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:37.764035+00:00
-- url     : https://prove2.me/submissions/db723825-6c0e-48bc-91f2-808ac0379cd7

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Supplement_LeastSlack

open ReentrantScheduling
open ReentrantScheduling.FBFS
open ReentrantScheduling.FBFS.Supplement

/-- Theorem 4, p. 1413: both LS population bounds, uniformly over runs and due dates. -/
theorem solution (L : Line) (lam γ γ₁ γ₂ : ℝ)
    (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hγ₁ : 0 ≤ γ₁) (hγ₂ : 0 ≤ γ₂)
    (hload : L.load lam < 1) (ζ : Fin L.l → ℝ) (hζ : ∀ i, 0 ≤ ζ i) :
    ∃ (f : ℕ → ℝ) (Γ : ℝ), 0 ≤ Γ ∧
      ∀ (R : Run L) (δ : R.Part → ℝ), R.Arrivals lam γ →
        DueWindow R δ γ₁ γ₂ → LSAdmissible R δ ζ →
        ∀ n : ℕ, R.x 0 = (n : ℕ∞) →
          populationSup R < ENNReal.ofReal (f n) ∧
          populationLimsup R ≤ ENNReal.ofReal Γ := by
            classical
            have svcSet : ∀ (R : Run L) (q : R.Part) (i : Fin L.l), ∃ a : ℝ,
                {u : ℝ | R.InService q i u} = ∅ ∨ {u : ℝ | R.InService q i u} = Set.Ico a (a + L.τ i) := by
              intro R q i
              by_cases he : R.entry q ≤ i
              · cases hs : R.start q i with
                | top => exact ⟨0, Or.inl (by ext u; simp [Run.InService, hs])⟩
                | coe a =>
                  refine ⟨a, Or.inr ?_⟩
                  ext u
                  simp only [Run.InService, hs, Set.mem_setOf_eq, Set.mem_Ico, he, true_and]
                  constructor
                  · rintro ⟨h1, h2⟩
                    exact ⟨by exact_mod_cast h1, by rw [← WithTop.coe_add] at h2; exact_mod_cast h2⟩
                  · rintro ⟨h1, h2⟩
                    exact ⟨by exact_mod_cast h1, by rw [← WithTop.coe_add]; exact_mod_cast h2⟩
              · exact ⟨0, Or.inl (by ext u; simp [Run.InService, he])⟩
            open MeasureTheory in
            have workCons : ∀ (R : Run L) (σ : Fin L.S) (F : Finset (R.Part × Fin L.l)) (s t : ℝ), s ≤ t →
                (∀ u, s ≤ u → u < t → R.busySlots σ u ⊆ ↑F) →
                (∀ u, s ≤ u → u < t → ((L.m σ : ℕ) : ℕ∞) ≤ (R.busySlots σ u).encard) →
                (L.m σ : ℝ) * (t - s) ≤ ∑ x ∈ F.filter (fun x => L.center x.2 = σ), L.τ x.2 := by
              intro R σ F s t hst hF hm
              set G := F.filter (fun x => L.center x.2 = σ) with hG
              let g : ℝ → ℝ := fun u => ∑ x ∈ G, Set.indicator {u : ℝ | R.InService x.1 x.2 u} (fun _ => (1:ℝ)) u
              have hmeas : ∀ x : R.Part × Fin L.l, MeasurableSet {u : ℝ | R.InService x.1 x.2 u} := by
                intro x
                obtain ⟨a, h | h⟩ := svcSet R x.1 x.2 <;> rw [h]
                · exact MeasurableSet.empty
                · exact measurableSet_Ico
              have hvol : ∀ x : R.Part × Fin L.l,
                  volume.real ({u : ℝ | R.InService x.1 x.2 u} ∩ Set.Ico s t) ≤ L.τ x.2 := by
                intro x
                obtain ⟨a, h | h⟩ := svcSet R x.1 x.2 <;> rw [h]
                · simp [(L.τ_pos _).le]
                · calc volume.real (Set.Ico a (a + L.τ x.2) ∩ Set.Ico s t)
                      ≤ volume.real (Set.Ico a (a + L.τ x.2)) :=
                        measureReal_mono Set.inter_subset_left (by simp)
                    _ = L.τ x.2 := by rw [Real.volume_real_Ico]; simp [(L.τ_pos _).le]
              have hpt : ∀ u ∈ Set.Ico s t, (L.m σ : ℝ) ≤ g u := by
                rintro u ⟨h1, h2⟩
                have hsub : R.busySlots σ u ⊆ ↑(G.filter (fun x => R.InService x.1 x.2 u)) := by
                  intro x hx
                  have := hF u h1 h2 hx
                  simp only [Finset.coe_filter, hG, Finset.mem_filter, Set.mem_setOf_eq]
                  exact ⟨⟨this, hx.1⟩, hx.2⟩
                have h3 := (hm u h1 h2).trans (Set.encard_le_encard hsub)
                rw [Set.encard_coe_eq_coe_finsetCard] at h3
                have h4 : L.m σ ≤ (G.filter (fun x => R.InService x.1 x.2 u)).card := by exact_mod_cast h3
                have h5 : g u = ((G.filter (fun x => R.InService x.1 x.2 u)).card : ℝ) := by
                  simp only [g, Set.indicator_apply, Set.mem_setOf_eq]
                  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
                rw [h5]; exact_mod_cast h4
              have hint : ∀ x ∈ G, Integrable (Set.indicator {u : ℝ | R.InService x.1 x.2 u} (fun _ => (1:ℝ)))
                  (volume.restrict (Set.Ico s t)) := by
                intro x _
                exact (integrable_const (1:ℝ)).indicator (hmeas x) |>.mono_measure le_rfl
              calc (L.m σ : ℝ) * (t - s) = ∫ _ in Set.Ico s t, (L.m σ : ℝ) := by
                    rw [setIntegral_const, Real.volume_real_Ico_of_le hst, smul_eq_mul, mul_comm]
                _ ≤ ∫ u in Set.Ico s t, g u := by
                    apply setIntegral_mono_on (integrable_const _) (integrable_finset_sum _ hint)
                      measurableSet_Ico hpt
                _ = ∑ x ∈ G, ∫ u in Set.Ico s t,
                      Set.indicator {u : ℝ | R.InService x.1 x.2 u} (fun _ => (1:ℝ)) u := by
                    exact integral_finset_sum _ hint
                _ = ∑ x ∈ G, volume.real ({u : ℝ | R.InService x.1 x.2 u} ∩ Set.Ico s t) := by
                    refine Finset.sum_congr rfl fun x _ => ?_
                    rw [integral_indicator_const _ (hmeas x), smul_eq_mul, mul_one, measureReal_restrict_apply (hmeas x)]
                _ ≤ ∑ x ∈ G, L.τ x.2 := Finset.sum_le_sum fun x _ => hvol x
            obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, ∀ i, ζ i ≤ Z := ⟨∑ i, |ζ i|, fun i =>
              (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |ζ i|)
                (fun j _ => abs_nonneg _) (Finset.mem_univ i))⟩
            have overtake : ∀ (R : Run L) (δ : R.Part → ℝ), DueWindow R δ γ₁ γ₂ →
                LSAdmissible R δ ζ → ∀ p i (t : ℝ), 0 ≤ t → R.entry p ≤ i →
                R.start p i = (t : WithTop ℝ) → ∀ q j, L.center j = L.center i →
                R.Waiting q j t → R.α p ≤ R.α q + (γ₁ + γ₂ + Z) := by
              intro R δ hW hLS p i t ht hpi hs q j hc hq
              have h1 := hLS.leastSlack p i t ht hpi hs q j hc hq
              have h2 := (hW p).1
              have h3 := (hW q).2
              have h4 := hZ i
              have h5 := hζ j
              linarith
            have chainStep : ∀ (R : Run L) (δ : R.Part → ℝ), LSAdmissible R δ ζ →
                ∀ p (i j : Fin L.l), R.entry p ≤ i → j.val = i.val + 1 →
                R.start p i + ((L.τ i : ℝ) : WithTop ℝ) ≤ R.start p j := by
              intro R δ hLS p i j hpi hj
              have hlt : R.entry p < j := lt_of_le_of_lt hpi (by
                rw [Fin.lt_def]; omega)
              rcases hLS.precedence p j hlt.le with h | ⟨_, hje, _⟩
              · have harr : R.arrive p j = R.start p i + ((L.τ i : ℝ) : WithTop ℝ) := by
                  unfold Run.arrive
                  rw [if_neg (ne_of_gt hlt), if_pos hlt]
                  have : (⟨j.val - 1, by omega⟩ : Fin L.l) = i := by
                    ext; simp; omega
                  rw [this]
                rw [← harr]; exact h
              · exact absurd hje (ne_of_gt hlt)
            have chain : ∀ (R : Run L) (δ : R.Part → ℝ), LSAdmissible R δ ζ →
                ∀ p (k : ℕ) (i j : Fin L.l), R.entry p ≤ i → j.val = i.val + k + 1 →
                R.start p i + ((L.τ i : ℝ) : WithTop ℝ) ≤ R.start p j := by
              intro R δ hLS p k
              induction k with
              | zero => intro i j hpi hj; exact chainStep R δ hLS p i j hpi (by omega)
              | succ k ih =>
                intro i j hpi hj
                have hk : i.val + k + 1 < L.l := by omega
                have h1 := ih i ⟨i.val + k + 1, hk⟩ hpi rfl
                have h2 := chainStep R δ hLS p ⟨i.val + k + 1, hk⟩ j
                  (le_trans hpi (by rw [Fin.le_def]; simp; omega)) (by simp; omega)
                refine le_trans h1 (le_trans ?_ h2)
                exact le_add_of_nonneg_right (by exact_mod_cast (L.τ_pos _).le)
            have αnn : ∀ (R : Run L) p, 0 ≤ R.α p := by
              intro R p
              by_cases h : R.initial p
              · rw [R.α_initial p h]
              · exact R.α_released p h
            have relPrec : ∀ (R : Run L) (δ : R.Part → ℝ), LSAdmissible R δ ζ → ∀ p, ¬ R.initial p →
                ∀ j, R.arrive p j ≤ R.start p j := by
              intro R δ hLS p hp j
              have he : R.entry p ≤ j := by rw [R.entry_released p hp, Fin.le_def]; simp
              rcases hLS.precedence p j he with h | ⟨h, _⟩
              · exact h
              · exact absurd h hp
            have αle : ∀ (R : Run L) (δ : R.Part → ℝ), LSAdmissible R δ ζ → ∀ p, ¬ R.initial p →
                ∀ j : Fin L.l, ((R.α p : ℝ) : WithTop ℝ) ≤ R.start p j := by
              intro R δ hLS p hp j
              obtain ⟨j, hj⟩ := j
              induction j with
              | zero =>
                have := relPrec R δ hLS p hp ⟨0, hj⟩
                unfold Run.arrive at this
                rw [if_pos (by rw [R.entry_released p hp])] at this
                exact this
              | succ j ih =>
                have h1 := ih (by omega)
                have h2 := relPrec R δ hLS p hp ⟨j+1, hj⟩
                unfold Run.arrive at h2
                have hne : (⟨j+1, hj⟩ : Fin L.l) ≠ R.entry p := by
                  rw [R.entry_released p hp]; simp
                have hlt : R.entry p < ⟨j+1, hj⟩ := by
                  rw [R.entry_released p hp, Fin.lt_def]; simp
                rw [if_neg hne, if_pos hlt] at h2
                simp only [Nat.add_sub_cancel] at h2
                refine h1.trans (le_trans ?_ h2)
                exact le_add_of_nonneg_right (by exact_mod_cast (L.τ_pos _).le)
            have toExit : ∀ (R : Run L) (δ : R.Part → ℝ), LSAdmissible R δ ζ → ∀ p (j : Fin L.l),
                R.entry p ≤ j → R.start p j + ((L.τ j : ℝ) : WithTop ℝ) ≤ R.exit p := by
              intro R δ hLS p j hj
              unfold Run.exit
              by_cases h : j.val = L.l - 1
              · have : j = ⟨L.l - 1, by have := L.l_pos; omega⟩ := by ext; exact h
                rw [this]
              · have hlt : j.val < L.l - 1 := by have := j.isLt; omega
                refine le_trans ?_ (le_add_of_nonneg_right (by exact_mod_cast (L.τ_pos _).le))
                exact chain R δ hLS p (L.l - 1 - j.val - 1) j _ hj (by simp; omega)
            have exitGt : ∀ (R : Run L) (δ : R.Part → ℝ), LSAdmissible R δ ζ → ∀ p,
                ((R.α p : ℝ) : WithTop ℝ) < R.exit p := by
              intro R δ hLS p
              refine lt_of_lt_of_le ?_ (toExit R δ hLS p (R.entry p) le_rfl)
              rcases hLS.precedence p (R.entry p) le_rfl with h | ⟨hi, _, h, _⟩
              · unfold Run.arrive at h
                rw [if_pos rfl] at h
                cases hs : R.start p (R.entry p) with
                | top => simp
                | coe a =>
                  rw [hs] at h
                  have : R.α p ≤ a := by exact_mod_cast h
                  rw [← WithTop.coe_add]; exact_mod_cast (by linarith [L.τ_pos (R.entry p)])
              · cases hs : R.start p (R.entry p) with
                | top => simp
                | coe a =>
                  rw [hs] at h
                  have : -L.τ (R.entry p) < a := by exact_mod_cast h
                  rw [← WithTop.coe_add, R.α_initial p hi]; exact_mod_cast (by linarith)
            have order : ∀ (R : Run L) (δ : R.Part → ℝ), DueWindow R δ γ₁ γ₂ → LSAdmissible R δ ζ →
                ∀ q p, R.α q < R.α p - (γ₁ + γ₂ + Z) → ∀ j : Fin L.l, R.entry q ≤ j →
                R.start q j ≤ R.start p j := by
              intro R δ hW hLS q p hqp
              have hCnn : 0 ≤ γ₁ + γ₂ + Z := by have := hζ ⟨0, L.l_pos⟩; have := hZ ⟨0, L.l_pos⟩; linarith
              have hp : ¬ R.initial p := by
                intro hi; have := R.α_initial p hi; have := αnn R q; linarith
              intro j
              obtain ⟨j, hj⟩ := j
              induction j with
              | zero =>
                intro hqj
                cases hs : R.start p ⟨0, hj⟩ with
                | top => exact le_top
                | coe t =>
                  by_contra hlt
                  rw [not_le] at hlt
                  have hαt : R.α p ≤ t := by have := αle R δ hLS p hp ⟨0, hj⟩; rw [hs] at this; exact_mod_cast this
                  have hqe : R.entry q = ⟨0, hj⟩ := le_antisymm hqj (by rw [Fin.le_def]; simp)
                  have hwait : R.Waiting q ⟨0, hj⟩ t := by
                    refine ⟨hqj, ?_, hlt⟩
                    unfold Run.arrive; rw [if_pos hqe.symm]
                    exact_mod_cast (by linarith : R.α q ≤ t)
                  have := overtake R δ hW hLS p ⟨0, hj⟩ t (by linarith [αnn R p])
                    (by rw [R.entry_released p hp]) hs q ⟨0, hj⟩ rfl hwait
                  linarith
              | succ j ih =>
                intro hqj
                cases hs : R.start p ⟨j+1, hj⟩ with
                | top => exact le_top
                | coe t =>
                  by_contra hlt
                  rw [not_le] at hlt
                  have hαt : R.α p ≤ t := by
                    have := αle R δ hLS p hp ⟨j+1, hj⟩; rw [hs] at this; exact_mod_cast this
                  have harr : R.arrive q ⟨j+1, hj⟩ ≤ (t : WithTop ℝ) := by
                    unfold Run.arrive
                    by_cases he : (⟨j+1, hj⟩ : Fin L.l) = R.entry q
                    · rw [if_pos he]; exact_mod_cast (by linarith [αnn R q] : R.α q ≤ t)
                    · have hlt' : R.entry q < ⟨j+1, hj⟩ := lt_of_le_of_ne hqj (Ne.symm he)
                      rw [if_neg he, if_pos hlt']
                      simp only [Nat.add_sub_cancel]
                      have h1 := ih (by omega) (by rw [Fin.le_def]; rw [Fin.lt_def] at hlt'; simp at hlt' ⊢; omega)
                      have h2 := relPrec R δ hLS p hp ⟨j+1, hj⟩
                      unfold Run.arrive at h2
                      have hne : (⟨j+1, hj⟩ : Fin L.l) ≠ R.entry p := by rw [R.entry_released p hp]; simp
                      have hlt2 : R.entry p < ⟨j+1, hj⟩ := by
                        rw [R.entry_released p hp, Fin.lt_def]; simp
                      rw [if_neg hne, if_pos hlt2, hs] at h2
                      simp only [Nat.add_sub_cancel] at h2
                      exact (add_le_add h1 le_rfl).trans h2
                  have hwait : R.Waiting q ⟨j+1, hj⟩ t := ⟨hqj, harr, hlt⟩
                  have := overtake R δ hW hLS p ⟨j+1, hj⟩ t (by linarith [αnn R p])
                    (by rw [R.entry_released p hp, Fin.le_def]; simp) hs q ⟨j+1, hj⟩ rfl hwait
                  linarith
            have hCnn : 0 ≤ γ₁ + γ₂ + Z := by have := hζ ⟨0, L.l_pos⟩; have := hZ ⟨0, L.l_pos⟩; linarith
            have hτs : ∀ i, L.τ i ≤ ∑ j, L.τ j := fun i =>
              Finset.single_le_sum (f := L.τ) (fun j _ => (L.τ_pos j).le) (Finset.mem_univ i)
            have wnn : ∀ σ, 0 ≤ L.w σ := fun σ => Finset.sum_nonneg fun i _ =>
              div_nonneg (L.τ_pos i).le (Nat.cast_nonneg _)
            have wle : ∀ σ, L.w σ ≤ L.wbar := fun σ => Finset.le_sup' L.w (Finset.mem_univ σ)
            have mw : ∀ σ, (L.m σ : ℝ) * L.w σ = ∑ i ∈ Finset.univ.filter (fun i => L.center i = σ), L.τ i := by
              intro σ
              unfold Line.w
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              have : (L.m σ : ℝ) ≠ 0 := by exact_mod_cast (L.m_pos σ).ne'
              field_simp
            have waitB : ∀ (R : Run L) (δ : R.Part → ℝ), DueWindow R δ γ₁ γ₂ → LSAdmissible R δ ζ →
                ∀ π (k : Fin L.l) (t0 K : ℝ), 0 ≤ t0 → R.entry π ≤ k → R.arrive π k ≤ (t0 : WithTop ℝ) →
                ({q | R.α π - (γ₁ + γ₂ + Z) ≤ R.α q ∧ R.α q ≤ R.α π + (γ₁ + γ₂ + Z)}.ncard : ℝ) ≤ K →
                R.start π k ≤ (((t0 + (∑ i, L.τ i)) + L.wbar *
                  (({q | R.α q < R.α π - (γ₁ + γ₂ + Z) ∧ (t0 : WithTop ℝ) < R.exit q}.ncard : ℝ) + K) : ℝ)
                    : WithTop ℝ) := by
              clear svcSet chainStep chain relPrec αle exitGt order
              intro R δ hW hLS π k t0 K ht0 hπk harr hK
              set C := γ₁ + γ₂ + Z with hC
              set τs := ∑ i, L.τ i with hτsdef
              set σ := L.center k with hσ
              set O := {q | R.α q < R.α π - C ∧ (t0 : WithTop ℝ) < R.exit q} with hO
              set W := {q | R.α π - C ≤ R.α q ∧ R.α q ≤ R.α π + C} with hWdef
              have hfin : {q | R.α q ≤ R.α π + C}.Finite := R.α_finite _
              set F := (hfin.toFinset ×ˢ (Finset.univ : Finset (Fin L.l))).filter
                (fun x : R.Part × Fin L.l => R.entry x.1 ≤ x.2 ∧ (t0 : WithTop ℝ) ≤ R.start x.1 x.2) with hF
              set G := F.filter (fun x => L.center x.2 = σ) with hG
              have hOWfin : (O ∪ W).Finite := hfin.subset (by
                rintro q (⟨h1, _⟩ | ⟨_, h2⟩)
                · show R.α q ≤ R.α π + C; linarith
                · exact h2)
              have hsumG : ∑ x ∈ G, L.τ x.2 ≤ ((O.ncard : ℝ) + K) * ((L.m σ : ℝ) * L.w σ) := by
                have hsub : G ⊆ (G.image Prod.fst) ×ˢ (Finset.univ.filter (fun j => L.center j = σ)) := by
                  intro x hx
                  rw [Finset.mem_product]
                  refine ⟨Finset.mem_image_of_mem _ hx, ?_⟩
                  rw [hG, Finset.mem_filter] at hx
                  simp [hx.2]
                have h1 : ∑ x ∈ G, L.τ x.2 ≤ ∑ x ∈ (G.image Prod.fst) ×ˢ
                    (Finset.univ.filter (fun j => L.center j = σ)), L.τ x.2 :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => (L.τ_pos _).le)
                rw [Finset.sum_product] at h1
                simp only at h1
                rw [Finset.sum_const, nsmul_eq_mul, ← mw σ] at h1
                have hcard : ((G.image Prod.fst).card : ℝ) ≤ (O.ncard : ℝ) + K := by
                  have hsub2 : (↑(G.image Prod.fst) : Set R.Part) ⊆ O ∪ W := by
                    intro y hy
                    rw [Finset.coe_image] at hy
                    obtain ⟨x, hx, rfl⟩ := hy
                    rw [Finset.mem_coe, hG, Finset.mem_filter, hF, Finset.mem_filter, Finset.mem_product,
                      hfin.mem_toFinset] at hx
                    obtain ⟨⟨⟨hα, -⟩, he, hst⟩, -⟩ := hx
                    by_cases hlt : R.α x.1 < R.α π - C
                    · left
                      refine ⟨hlt, ?_⟩
                      calc (t0 : WithTop ℝ) < ((t0 + L.τ x.2 : ℝ) : WithTop ℝ) := by
                            exact_mod_cast (by linarith [L.τ_pos x.2])
                        _ = (t0 : WithTop ℝ) + ((L.τ x.2 : ℝ) : WithTop ℝ) := WithTop.coe_add _ _
                        _ ≤ R.start x.1 x.2 + ((L.τ x.2 : ℝ) : WithTop ℝ) := add_le_add hst le_rfl
                        _ ≤ R.exit x.1 := toExit R δ hLS x.1 x.2 he
                    · right; exact ⟨by linarith, hα⟩
                  have := Set.ncard_le_ncard hsub2 hOWfin
                  rw [Set.ncard_coe_finset] at this
                  have h3 := (this.trans (Set.ncard_union_le O W))
                  have h4 : ((G.image Prod.fst).card : ℝ) ≤ (O.ncard : ℝ) + (W.ncard : ℝ) := by exact_mod_cast h3
                  linarith
                have hmw : 0 ≤ (L.m σ : ℝ) * L.w σ := mul_nonneg (Nat.cast_nonneg _) (wnn σ)
                exact h1.trans (mul_le_mul_of_nonneg_right hcard hmw)
              set B := (t0 + τs) + L.wbar * ((O.ncard : ℝ) + K) with hB
              have hKnn : 0 ≤ K := le_trans (Nat.cast_nonneg _) hK
              have hBge : t0 + τs ≤ B := by
                have : 0 ≤ L.wbar * ((O.ncard : ℝ) + K) :=
                  mul_nonneg ((wnn σ).trans (wle σ)) (by positivity)
                linarith
              by_contra hgt
              rw [not_le] at hgt
              obtain ⟨u, hBu, hu⟩ : ∃ u : ℝ, B < u ∧ (u : WithTop ℝ) < R.start π k := by
                cases hs : R.start π k with
                | top => exact ⟨B + 1, by linarith, WithTop.coe_lt_top _⟩
                | coe a =>
                  rw [hs] at hgt
                  have : B < a := by exact_mod_cast hgt
                  exact ⟨(B + a) / 2, by linarith, by exact_mod_cast (by linarith : (B + a) / 2 < a)⟩
              have hwaitv : ∀ v : ℝ, t0 ≤ v → v < u → R.Waiting π k v := fun v h1 h2 =>
                ⟨hπk, harr.trans (by exact_mod_cast h1), lt_trans (by exact_mod_cast h2) hu⟩
              have hsubF : ∀ v, t0 + τs ≤ v → v < u → R.busySlots σ v ⊆ ↑F := by
                intro v hv1 hv2 x hx
                obtain ⟨hc, he, hs1, hs2⟩ := hx
                cases hsx : R.start x.1 x.2 with
                | top => rw [hsx] at hs1; exact absurd hs1 (by simp)
                | coe a =>
                  rw [hsx] at hs1 hs2
                  have ha : a ≤ v := by exact_mod_cast hs1
                  have hav : v < a + L.τ x.2 := by rw [← WithTop.coe_add] at hs2; exact_mod_cast hs2
                  have hta : t0 ≤ a := by
                    by_contra h; rw [not_le] at h; linarith [hτs x.2]
                  have hα := overtake R δ hW hLS x.1 x.2 a (by linarith) he hsx π k hc.symm
                    (hwaitv a hta (by linarith))
                  rw [Finset.mem_coe, hF, Finset.mem_filter, Finset.mem_product, hfin.mem_toFinset]
                  exact ⟨⟨hα, Finset.mem_univ _⟩, he, by rw [hsx]; exact_mod_cast hta⟩
              have hm : ∀ v, t0 + τs ≤ v → v < u → ((L.m σ : ℕ) : ℕ∞) ≤ (R.busySlots σ v).encard := by
                intro v hv1 hv2
                rw [hLS.nonidling σ v (by linarith [hτs k, L.τ_pos k]) ⟨π, k, rfl, hwaitv v (by linarith [hτs k, L.τ_pos k]) hv2⟩]
              have hwc := workCons R σ F (t0 + τs) u (by linarith) hsubF hm
              rw [← hG] at hwc
              have hmpos : (0 : ℝ) < L.m σ := by exact_mod_cast L.m_pos σ
              have h5 : (L.m σ : ℝ) * (u - (t0 + τs)) ≤ (L.m σ : ℝ) * (((O.ncard : ℝ) + K) * L.wbar) := by
                have := hwc.trans hsumG
                have h6 : ((O.ncard : ℝ) + K) * ((L.m σ : ℝ) * L.w σ) ≤ (L.m σ : ℝ) * (((O.ncard : ℝ) + K) * L.wbar) := by
                  rw [mul_left_comm]
                  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (wle σ) (by positivity)) hmpos.le
                linarith
              have h7 := le_of_mul_le_mul_left h5 hmpos
              rw [hB] at hBu
              have : ((O.ncard : ℝ) + K) * L.wbar = L.wbar * ((O.ncard : ℝ) + K) := mul_comm _ _
              linarith
            have arrOrder : ∀ (R : Run L) (δ : R.Part → ℝ), DueWindow R δ γ₁ γ₂ → LSAdmissible R δ ζ →
                ∀ q p, R.α q < R.α p - (γ₁ + γ₂ + Z) → ∀ j : Fin L.l, R.entry q < j →
                R.arrive q j ≤ R.arrive p j := by
              intro R δ hW hLS q p hqp j hj
              have hp : ¬ R.initial p := by
                intro hi; have := R.α_initial p hi; have := αnn R q; linarith
              have hjp : R.entry p < j := by
                rw [R.entry_released p hp, Fin.lt_def]; rw [Fin.lt_def] at hj; simp; omega
              unfold Run.arrive
              rw [if_neg (ne_of_gt hj), if_pos hj, if_neg (ne_of_gt hjp), if_pos hjp]
              refine add_le_add (order R δ hW hLS q p hqp _ ?_) le_rfl
              rw [Fin.le_def]; rw [Fin.lt_def] at hj; simp; omega
            obtain ⟨ε, hε, hρ⟩ : ∃ ε : ℝ, 0 < ε ∧ lam * (L.wbar + ε) < 1 := by
              have h1 : lam * L.wbar < 1 := hload
              refine ⟨(1 - lam * L.wbar) / (2 * (lam + 1)), by apply div_pos <;> linarith, ?_⟩
              have h2 : lam * ((1 - lam * L.wbar) / (2 * (lam + 1))) ≤ (1 - lam * L.wbar) / 2 := by
                rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
                have : (1 - lam * L.wbar) * (2 * (lam + 1)) = lam * (1 - lam * L.wbar) * 2 + 2 * (1 - lam * L.wbar) := by ring
                linarith
              have h3 : lam * (L.wbar + (1 - lam * L.wbar) / (2 * (lam + 1))) =
                  lam * L.wbar + lam * ((1 - lam * L.wbar) / (2 * (lam + 1))) := by ring
              linarith
            have hwbar : 0 ≤ L.wbar := (wnn (L.center ⟨0, L.l_pos⟩)).trans (wle _)
            have hlpos : (0 : ℝ) < L.l := by exact_mod_cast L.l_pos
            have Hlev : ∀ K : ℝ, 0 ≤ K → ∀ d : ℕ, d ≤ L.l → ∃ c : ℝ, 0 ≤ c ∧
                ∀ (R : Run L) (δ : R.Part → ℝ), DueWindow R δ γ₁ γ₂ → LSAdmissible R δ ζ →
                ∀ tst : ℝ, 0 ≤ tst →
                (∀ q, (tst : WithTop ℝ) < R.exit q →
                  ({q' | R.α q - (γ₁ + γ₂ + Z) ≤ R.α q' ∧ R.α q' ≤ R.α q + (γ₁ + γ₂ + Z)}.ncard : ℝ) ≤ K) →
                ∀ (x : ℕ) (π : R.Part) (t0 : ℝ), tst ≤ t0 → R.α π ≤ t0 →
                ((∀ h : L.l - d < L.l, R.entry π < ⟨L.l - d, h⟩ → R.arrive π ⟨L.l - d, h⟩ ≤ (t0 : WithTop ℝ)) ∧
                  (L.l ≤ L.l - d → R.exit π ≤ (t0 : WithTop ℝ))) →
                {q | R.α q < R.α π - (γ₁ + γ₂ + Z) ∧ (t0 : WithTop ℝ) < R.exit q}.ncard = x →
                R.exit π ≤ ((t0 + c + (L.wbar + ε * d / L.l) * x : ℝ) : WithTop ℝ) := by
              clear svcSet workCons overtake chainStep chain relPrec αle toExit exitGt order wnn wle mw hρ
              intro K hK d
              induction d with
              | zero =>
                intro _
                refine ⟨0, le_rfl, ?_⟩
                intro R δ hW hLS tst htst hwin x π t0 h1 h2 hIn hx
                refine (hIn.2 (by simp)).trans ?_
                have : 0 ≤ (L.wbar + ε * ((0:ℕ):ℝ) / L.l) * x :=
                  mul_nonneg (by rw [Nat.cast_zero, mul_zero, zero_div, add_zero]; exact hwbar) (Nat.cast_nonneg _)
                exact_mod_cast (by linarith)
              | succ d ih =>
                intro hd
                obtain ⟨c, hc0, hc⟩ := ih (by omega)
                set τs := ∑ i, L.τ i with hτsdef
                have hτs0 : 0 ≤ τs := Finset.sum_nonneg fun i _ => (L.τ_pos i).le
                set Y := c * L.l / ε with hY
                have hY0 : 0 ≤ Y := div_nonneg (mul_nonneg hc0 hlpos.le) hε.le
                set sd := L.wbar + ε * (d : ℝ) / L.l with hsd
                set sd1 := L.wbar + ε * ((d + 1 : ℕ) : ℝ) / L.l with hsd1
                have hsd0 : L.wbar ≤ sd := by
                  have : 0 ≤ ε * (d:ℝ) / L.l := div_nonneg (mul_nonneg hε.le (Nat.cast_nonneg _)) hlpos.le
                  linarith
                have hsdle : sd ≤ L.wbar + ε := by
                  have : ε * (d:ℝ) / L.l ≤ ε := by
                    rw [div_le_iff₀ hlpos]
                    have : (d:ℝ) ≤ L.l := by exact_mod_cast (show d ≤ L.l by omega)
                    exact mul_le_mul_of_nonneg_left this hε.le
                  linarith
                have hgap : sd1 = sd + ε / L.l := by
                  rw [hsd1, hsd]; push_cast; ring
                have hsd1ge : sd ≤ sd1 := by
                  rw [hgap]
                  have : 0 ≤ ε / L.l := div_nonneg hε.le hlpos.le
                  linarith
                have hc'0 : 0 ≤ 2 * τs + L.wbar * K + c + (L.wbar + ε) * Y := by
                  have := mul_nonneg hwbar hK
                  have := mul_nonneg (add_nonneg hwbar hε.le) hY0
                  linarith
                refine ⟨2 * τs + L.wbar * K + c + (L.wbar + ε) * Y, hc'0, ?_⟩
                set c' := 2 * τs + L.wbar * K + c + (L.wbar + ε) * Y with hc'
                intro R δ hW hLS tst htst hwin x
                induction x using Nat.strong_induction_on with
                | _ x ihx =>
                intro π t0 h1 h2 hIn hx
                have hk : L.l - (d + 1) < L.l := by have := L.l_pos; omega
                set kk : Fin L.l := ⟨L.l - (d + 1), hk⟩ with hkk
                have hkd : L.l - d = L.l - (d + 1) + 1 := by omega
                -- the direct case: π already in the truncated system of level d at time t0
                have direct : ((∀ h : L.l - d < L.l, R.entry π < ⟨L.l - d, h⟩ →
                      R.arrive π ⟨L.l - d, h⟩ ≤ (t0 : WithTop ℝ)) ∧
                    (L.l ≤ L.l - d → R.exit π ≤ (t0 : WithTop ℝ))) →
                    R.exit π ≤ ((t0 + c' + sd1 * x : ℝ) : WithTop ℝ) := by
                  intro hIn'
                  refine (hc R δ hW hLS tst htst hwin x π t0 h1 h2 hIn' hx).trans ?_
                  have : sd * x ≤ sd1 * x := mul_le_mul_of_nonneg_right hsd1ge (Nat.cast_nonneg _)
                  have : c ≤ c' := by
                    have := mul_nonneg hwbar hK
                    have := mul_nonneg (add_nonneg hwbar hε.le) hY0
                    linarith
                  exact_mod_cast (by linarith)
                -- reaching level d once service at kk ends
                have nextIn : ∀ T : ℝ, R.entry π ≤ kk → R.start π kk + ((L.τ kk : ℝ) : WithTop ℝ) ≤ (T : WithTop ℝ) →
                    ((∀ h : L.l - d < L.l, R.entry π < ⟨L.l - d, h⟩ →
                      R.arrive π ⟨L.l - d, h⟩ ≤ (T : WithTop ℝ)) ∧
                    (L.l ≤ L.l - d → R.exit π ≤ (T : WithTop ℝ))) := by
                  intro T hek hT
                  constructor
                  · intro h hlt
                    unfold Run.arrive
                    rw [if_neg (ne_of_gt hlt), if_pos hlt]
                    have : (⟨L.l - d - 1, by omega⟩ : Fin L.l) = kk := by ext; simp [hkk]; omega
                    rw [this]; exact hT
                  · intro h
                    unfold Run.exit
                    have : (⟨L.l - 1, by have := L.l_pos; omega⟩ : Fin L.l) = kk := by ext; simp [hkk]; omega
                    rw [this]; exact hT
                by_cases hek : kk < R.entry π
                · apply direct
                  constructor
                  · intro h hlt
                    exfalso
                    rw [Fin.lt_def] at hlt hek; simp [hkk] at hek hlt; omega
                  · intro h; exfalso; have := (R.entry π).isLt; rw [Fin.lt_def] at hek; simp [hkk] at hek; omega
                rw [not_lt] at hek
                have harr : R.arrive π kk ≤ (t0 : WithTop ℝ) := by
                  rcases lt_or_eq_of_le hek with hlt | heq
                  · exact hIn.1 hk hlt
                  · unfold Run.arrive; rw [if_pos heq.symm]; exact_mod_cast h2
                by_cases hb1 : R.start π kk + ((L.τ kk : ℝ) : WithTop ℝ) ≤ (t0 : WithTop ℝ)
                · exact direct (nextIn t0 hek hb1)
                rw [not_le] at hb1
                by_cases hex : R.exit π ≤ (t0 : WithTop ℝ)
                · refine hex.trans ?_
                  have : 0 ≤ sd1 * x := mul_nonneg (by linarith) (Nat.cast_nonneg _)
                  have : 0 ≤ c' := hc'0
                  exact_mod_cast (by linarith)
                rw [not_le] at hex
                have hwinπ := hwin π (lt_of_le_of_lt (by exact_mod_cast h1) hex)
                have hwb := waitB R δ hW hLS π kk t0 K (htst.trans h1) hek harr hwinπ
                rw [hx] at hwb
                obtain ⟨a, ha⟩ : ∃ a : ℝ, R.start π kk = (a : WithTop ℝ) := by
                  cases hs : R.start π kk with
                  | top => rw [hs] at hwb; exact absurd hwb (not_le.mpr (WithTop.coe_lt_top _))
                  | coe a => exact ⟨a, rfl⟩
                rw [ha] at hwb hb1
                have hale : a ≤ t0 + τs + L.wbar * ((x : ℝ) + K) := by exact_mod_cast hwb
                rw [← WithTop.coe_add] at hb1
                have hT0 : t0 < a + L.τ kk := by exact_mod_cast hb1
                set T' := a + L.τ kk with hT'
                have hInT := nextIn T' hek (by rw [ha, ← WithTop.coe_add])
                set Oy := {q | R.α q < R.α π - (γ₁ + γ₂ + Z) ∧ (T' : WithTop ℝ) < R.exit q} with hOy
                have hcT := hc R δ hW hLS tst htst hwin Oy.ncard π T' (by linarith) (by linarith) hInT rfl
                have hτk := hτs kk
                by_cases hy : (Oy.ncard : ℝ) ≤ Y
                · refine hcT.trans ?_
                  have h3 : sd * (Oy.ncard : ℝ) ≤ (L.wbar + ε) * Y :=
                    mul_le_mul hsdle hy (Nat.cast_nonneg _) (add_nonneg hwbar hε.le)
                  have h4 : L.wbar * (x : ℝ) ≤ sd1 * x :=
                    mul_le_mul_of_nonneg_right (hsd0.trans hsd1ge) (Nat.cast_nonneg _)
                  have h5 : L.wbar * ((x : ℝ) + K) = L.wbar * x + L.wbar * K := by ring
                  exact_mod_cast (by linarith)
                rw [not_le] at hy
                -- case 2: the oldest part still ahead at T'
                set O0 := {q | R.α q < R.α π - (γ₁ + γ₂ + Z) ∧ (t0 : WithTop ℝ) < R.exit q} with hO0
                have hO0fin : O0.Finite := (R.α_finite (R.α π)).subset (fun q hq => by
                  show R.α q ≤ R.α π; linarith [hq.1])
                have hOyfin : Oy.Finite := (R.α_finite (R.α π)).subset (fun q hq => by
                  show R.α q ≤ R.α π; linarith [hq.1])
                have hOysub : Oy ⊆ O0 := fun q hq => ⟨hq.1, lt_trans (by exact_mod_cast hT0) hq.2⟩
                have hOyne : Oy.Nonempty := by
                  rw [Set.nonempty_iff_ne_empty]; intro he
                  rw [he, Set.ncard_empty] at hy; simp at hy; linarith
                obtain ⟨π2, hπ2, hmin⟩ := Set.exists_min_image Oy R.α hOyfin hOyne
                set O2 := {q | R.α q < R.α π2 - (γ₁ + γ₂ + Z) ∧ (t0 : WithTop ℝ) < R.exit q} with hO2
                have hO2sub : O2 ⊆ O0 \ Oy := by
                  intro q hq
                  refine ⟨⟨by linarith [hq.1, hπ2.1], hq.2⟩, fun hqy => ?_⟩
                  have := hmin q hqy; linarith [hq.1]
                have hx2 : O2.ncard + Oy.ncard ≤ x := by
                  have h6 := Set.ncard_le_ncard hO2sub (hO0fin.diff)
                  rw [Set.ncard_diff hOysub hOyfin] at h6
                  have h7 := Set.ncard_le_ncard hOysub hO0fin
                  rw [hx] at h6 h7; omega
                have hy1 : 1 ≤ Oy.ncard := by
                  rw [Nat.one_le_iff_ne_zero]; intro h0; rw [h0] at hy; simp at hy; linarith
                have hπ2init : R.α π2 < R.α π - (γ₁ + γ₂ + Z) := hπ2.1
                have hIn2 : ((∀ h : L.l - (d+1) < L.l, R.entry π2 < ⟨L.l - (d+1), h⟩ →
                      R.arrive π2 ⟨L.l - (d+1), h⟩ ≤ (t0 : WithTop ℝ)) ∧
                    (L.l ≤ L.l - (d+1) → R.exit π2 ≤ (t0 : WithTop ℝ))) := by
                  constructor
                  · intro h hlt
                    exact (arrOrder R δ hW hLS π2 π hπ2init kk hlt).trans harr
                  · intro h; omega
                have hc2 := ihx O2.ncard (by omega) π2 t0 h1 (by linarith [αnn R π2]) hIn2 rfl
                have hT2 : (T' : WithTop ℝ) < ((t0 + c' + sd1 * O2.ncard : ℝ) : WithTop ℝ) :=
                  lt_of_lt_of_le hπ2.2 hc2
                have hT2' : T' < t0 + c' + sd1 * O2.ncard := by exact_mod_cast hT2
                refine hcT.trans ?_
                have hcY : c ≤ ε / L.l * Oy.ncard := by
                  rw [hY, div_lt_iff₀ hε] at hy
                  rw [div_mul_eq_mul_div, le_div_iff₀ hlpos]; linarith
                have hx2r : (O2.ncard : ℝ) + Oy.ncard ≤ x := by exact_mod_cast hx2
                have hsd1nn : 0 ≤ sd1 := by linarith
                have h8 : sd1 * (O2.ncard : ℝ) + sd1 * Oy.ncard ≤ sd1 * x := by
                  rw [← mul_add]; exact mul_le_mul_of_nonneg_left hx2r hsd1nn
                have h10 : sd1 * (Oy.ncard : ℝ) = sd * Oy.ncard + ε / L.l * Oy.ncard := by rw [hgap]; ring
                have h11 : T' + c + sd * Oy.ncard ≤ t0 + c' + sd1 * x := by linarith
                exact_mod_cast h11
            have arrR : ∀ (R : Run L), R.Arrivals lam γ → ∀ s0 t : ℝ, 0 ≤ s0 → s0 ≤ t →
                ({p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ t}.ncard : ℝ) ≤ lam * (t - s0) + γ := by
              intro R hArr s0 t hs0 hst
              have h := hArr s0 t hs0 hst
              have hfin : {p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ t}.Finite :=
                (R.α_finite t).subset (fun p hp => hp.2.2)
              rw [← hfin.cast_ncard_eq] at h
              have hnn : 0 ≤ lam * (t - s0) + γ := by nlinarith
              by_cases h0 : {p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ t}.ncard = 0
              · rw [h0]; simpa using hnn
              · have : ((({p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ t}.ncard : ℕ) : ℕ∞) : ENNReal) =
                    (({p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ t}.ncard : ℕ) : ENNReal) := rfl
                rw [this, ENNReal.natCast_le_ofReal h0] at h
                exact h
            have Thm3 : ∀ c s : ℝ, 0 ≤ c → 0 ≤ s → lam * s < 1 → ∀ (R : Run L) (δ : R.Part → ℝ),
                R.Arrivals lam γ → LSAdmissible R δ ζ → ∀ tst : ℝ, 0 ≤ tst →
                (∀ π (t0 : ℝ), tst ≤ t0 → R.α π ≤ t0 → R.exit π ≤
                  ((t0 + c + s * ({q | R.α q ≤ t0 ∧ (t0 : WithTop ℝ) < R.exit q}.ncard : ℝ) : ℝ) : WithTop ℝ)) →
                (∀ t, tst ≤ t → ({q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℝ) ≤
                    max ({q | R.α q ≤ tst ∧ (tst : WithTop ℝ) < R.exit q}.ncard : ℝ)
                      ((lam * (1 + c) + γ) / (1 - lam * s)) * (1 + lam * s) + (lam * (1 + c) + γ)) ∧
                (∃ T : ℝ, ∀ t, T ≤ t → ({q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℝ) ≤
                    ((lam * (1 + c) + γ) / (1 - lam * s) + 1) * (1 + lam * s) + (lam * (1 + c) + γ)) := by
              clear svcSet workCons overtake chainStep chain relPrec αle toExit exitGt order waitB arrOrder Hlev wnn wle mw
              intro c s hc hs hρ R δ hArr hLS tst htst hP
              set X : ℝ → ℝ := fun t => (({q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) with hXdef
              show (∀ t, tst ≤ t → X t ≤ max (X tst) _ * _ + _) ∧ ∃ T : ℝ, ∀ t, T ≤ t → X t ≤ _
              set ρ := lam * s with hρdef
              set a := lam * (1 + c) + γ with ha
              set B := a / (1 - ρ) with hB
              have hρ0 : 0 ≤ ρ := mul_nonneg hlam hs
              have ha0 : 0 ≤ a := by positivity
              have hB0 : 0 ≤ B := div_nonneg ha0 (by linarith)
              have hne : 1 - ρ ≠ 0 := ne_of_gt (by linarith)
              have haB : a = (1 - ρ) * B := by rw [hB]; field_simp
              have hBeq : a + ρ * B = B := by rw [haB]; ring
              have hX0 : ∀ t, 0 ≤ X t := fun t => Nat.cast_nonneg _
              obtain ⟨ts, h0, hsucc⟩ : ∃ ts : ℕ → ℝ, ts 0 = tst ∧ ∀ j, ts (j+1) = ts j + 1 + c + s * X (ts j) :=
                ⟨fun j => Nat.rec (motive := fun _ => ℝ) tst (fun _ t => t + 1 + c + s * X t) j, rfl, fun j => rfl⟩
              have hstep : ∀ j, ts j + 1 ≤ ts (j+1) := by
                intro j; rw [hsucc]; have := mul_nonneg hs (hX0 (ts j)); linarith
              have hmono : Monotone ts := monotone_nat_of_le_succ fun j => by linarith [hstep j]
              have hge : ∀ j : ℕ, tst + j ≤ ts j := by
                intro j; induction j with
                | zero => simp [h0]
                | succ j ih => have := hstep j; push_cast; linarith
              have hts0 : ∀ j, 0 ≤ ts j := fun j => by linarith [hge j, (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
              -- counting
              have hcount : ∀ (u t : ℝ), 0 ≤ u → u ≤ t →
                  X t ≤ (({q | R.α q ≤ u ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) + (lam * (t - u) + γ) := by
                intro u t hu hut
                have hsub : {q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q} ⊆
                    {q | R.α q ≤ u ∧ (t : WithTop ℝ) < R.exit q} ∪ {p | ¬ R.initial p ∧ u < R.α p ∧ R.α p ≤ t} := by
                  intro q ⟨hq1, hq2⟩
                  by_cases h : R.α q ≤ u
                  · left; exact ⟨h, hq2⟩
                  · right
                    rw [not_le] at h
                    refine ⟨fun hi => ?_, h, hq1⟩
                    rw [R.α_initial q hi] at h; linarith
                have hfin : ({q | R.α q ≤ u ∧ (t : WithTop ℝ) < R.exit q} ∪
                    {p | ¬ R.initial p ∧ u < R.α p ∧ R.α p ≤ t}).Finite :=
                  (R.α_finite t).subset (by
                    rintro q (⟨h1, _⟩ | ⟨_, _, h2⟩)
                    · show R.α q ≤ t; linarith
                    · exact h2)
                have h1 := (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
                have h2 := arrR R hArr u t hu hut
                have h3 : (({q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) ≤
                    (({q | R.α q ≤ u ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) +
                    (({p | ¬ R.initial p ∧ u < R.α p ∧ R.α p ≤ t}.ncard : ℕ) : ℝ) := by exact_mod_cast h1
                simp only [hXdef]; linarith
              have hold : ∀ (u t : ℝ), u ≤ t →
                  (({q | R.α q ≤ u ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) ≤ X u := by
                intro u t hut
                have hsub : {q | R.α q ≤ u ∧ (t : WithTop ℝ) < R.exit q} ⊆ {q | R.α q ≤ u ∧ (u : WithTop ℝ) < R.exit q} :=
                  fun q ⟨h1, h2⟩ => ⟨h1, lt_of_le_of_lt (by exact_mod_cast hut) h2⟩
                have := Set.ncard_le_ncard hsub ((R.α_finite u).subset fun q hq => hq.1)
                simp only [hXdef]; exact_mod_cast this
              have hin : ∀ j t, ts j ≤ t → t ≤ ts (j+1) → X t ≤ X (ts j) + a + ρ * X (ts j) := by
                intro j t h1 h2
                have := hcount (ts j) t (hts0 j) h1
                have := hold (ts j) t h1
                have : lam * (t - ts j) ≤ lam * (1 + c + s * X (ts j)) := by
                  apply mul_le_mul_of_nonneg_left _ hlam; rw [hsucc] at h2; linarith
                have : lam * (1 + c + s * X (ts j)) = lam * (1 + c) + ρ * X (ts j) := by rw [hρdef]; ring
                linarith
              have hnext : ∀ j, X (ts (j+1)) ≤ a + ρ * X (ts j) := by
                intro j
                have h1 := hcount (ts j) (ts (j+1)) (hts0 j) (hmono (Nat.le_succ j))
                have hempty : {q | R.α q ≤ ts j ∧ ((ts (j+1) : ℝ) : WithTop ℝ) < R.exit q} = ∅ := by
                  ext q
                  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
                  intro hq
                  refine (hP q (ts j) (by rw [← h0]; exact hmono (Nat.zero_le j)) hq).trans ?_
                  rw [hsucc]; exact_mod_cast (by linarith)
                rw [hempty, Set.ncard_empty] at h1
                have : lam * (ts (j+1) - ts j) = lam * (1 + c) + ρ * X (ts j) := by rw [hsucc, hρdef]; ring
                simp at h1; linarith
              have hbd : ∀ j, X (ts j) ≤ max (X tst) B := by
                intro j; induction j with
                | zero => rw [h0]; exact le_max_left _ _
                | succ j ih =>
                  refine (hnext j).trans ?_
                  have : ρ * X (ts j) ≤ ρ * max (X tst) B := mul_le_mul_of_nonneg_left ih hρ0
                  have : (1 - ρ) * B ≤ (1 - ρ) * max (X tst) B :=
                    mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
                  have : (1 - ρ) * max (X tst) B + ρ * max (X tst) B = max (X tst) B := by ring
                  linarith
              have hgeo : ∀ j, X (ts j) ≤ B + ρ ^ j * X tst := by
                intro j; induction j with
                | zero => rw [h0]; simp; exact hB0
                | succ j ih =>
                  refine (hnext j).trans ?_
                  have := mul_le_mul_of_nonneg_left ih hρ0
                  have : ρ * (B + ρ ^ j * X tst) = ρ * B + ρ ^ (j+1) * X tst := by ring
                  linarith
              have hfind : ∀ t, tst ≤ t → ∃ j, ts j ≤ t ∧ t < ts (j+1) ∧ ∀ J, ts J ≤ t → J ≤ j := by
                intro t ht
                have hex : ∃ j, t < ts (j+1) := by
                  obtain ⟨j, hj⟩ := exists_nat_gt (t - tst)
                  exact ⟨j, by have := hge (j+1); push_cast at this; linarith⟩
                refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
                · rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h | h
                  · rw [h, h0]; exact ht
                  · have := Nat.find_min hex (Nat.pred_lt (by omega : Nat.find hex ≠ 0))
                    rw [not_lt] at this
                    rw [h]; convert this using 2
                · intro J hJ
                  by_contra hlt; rw [not_le] at hlt
                  have := hmono (show Nat.find hex + 1 ≤ J by omega)
                  have := Nat.find_spec hex
                  linarith
              constructor
              · intro t ht
                obtain ⟨j, h1, h2, -⟩ := hfind t ht
                have := hin j t h1 h2.le
                have := hbd j
                have : ρ * X (ts j) ≤ ρ * max (X tst) B := mul_le_mul_of_nonneg_left (hbd j) hρ0
                have : max (X tst) B * (1 + ρ) = max (X tst) B + ρ * max (X tst) B := by ring
                linarith
              · obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1 / (X tst + 1) by
                  have := hX0 tst; positivity) hρ
                refine ⟨ts J, fun t ht => ?_⟩
                obtain ⟨j, h1, h2, h3⟩ := hfind t (by rw [← h0]; exact (hmono (Nat.zero_le J)).trans ht)
                have hJj := h3 J ht
                have hpow : ρ ^ j ≤ ρ ^ J := pow_le_pow_of_le_one hρ0 hρ.le hJj
                have hX1 : ρ ^ J * X tst ≤ 1 := by
                  have := hX0 tst
                  rw [lt_div_iff₀ (by linarith)] at hJ
                  have : 0 ≤ ρ ^ J := pow_nonneg hρ0 J
                  have : ρ ^ J * (X tst + 1) = ρ ^ J * X tst + ρ ^ J := by ring
                  linarith
                have hXj : X (ts j) ≤ B + 1 := by
                  have := hgeo j
                  have := mul_le_mul_of_nonneg_right hpow (hX0 tst)
                  linarith
                have := hin j t h1 h2.le
                have : ρ * X (ts j) ≤ ρ * (B + 1) := mul_le_mul_of_nonneg_left hXj hρ0
                have : (B + 1) * (1 + ρ) = (B + 1) + ρ * (B + 1) := by ring
                linarith
            have Hd : ∀ K : ℝ, ∃ c : ℝ, 0 ≤ c ∧ (0 ≤ K →
                ∀ (R : Run L) (δ : R.Part → ℝ), DueWindow R δ γ₁ γ₂ → LSAdmissible R δ ζ →
                ∀ tst : ℝ, 0 ≤ tst →
                (∀ q, (tst : WithTop ℝ) < R.exit q →
                  ({q' | R.α q - (γ₁ + γ₂ + Z) ≤ R.α q' ∧ R.α q' ≤ R.α q + (γ₁ + γ₂ + Z)}.ncard : ℝ) ≤ K) →
                ∀ (π : R.Part) (t0 : ℝ), tst ≤ t0 → R.α π ≤ t0 → R.exit π ≤
                  ((t0 + c + (L.wbar + ε) * ({q | R.α q ≤ t0 ∧ (t0 : WithTop ℝ) < R.exit q}.ncard : ℝ) : ℝ)
                    : WithTop ℝ)) := by
              intro K
              by_cases hK : 0 ≤ K
              · obtain ⟨c, hc0, hc⟩ := Hlev K hK L.l le_rfl
                refine ⟨c, hc0, fun _ R δ hW hLS tst htst hwin π t0 h1 h2 => ?_⟩
                have hIn : ((∀ h : L.l - L.l < L.l, R.entry π < ⟨L.l - L.l, h⟩ →
                      R.arrive π ⟨L.l - L.l, h⟩ ≤ (t0 : WithTop ℝ)) ∧
                    (L.l ≤ L.l - L.l → R.exit π ≤ (t0 : WithTop ℝ))) := by
                  constructor
                  · intro h hlt; exfalso; rw [Fin.lt_def] at hlt; simp at hlt
                  · intro h; exfalso; have := L.l_pos; omega
                have h3 := hc R δ hW hLS tst htst hwin _ π t0 h1 h2 hIn rfl
                have hεl : ε * (L.l : ℕ) / (L.l : ℝ) = ε := by field_simp
                rw [hεl] at h3
                refine h3.trans ?_
                have hsub : {q | R.α q < R.α π - (γ₁ + γ₂ + Z) ∧ (t0 : WithTop ℝ) < R.exit q} ⊆
                    {q | R.α q ≤ t0 ∧ (t0 : WithTop ℝ) < R.exit q} :=
                  fun q hq => ⟨by linarith [hq.1], hq.2⟩
                have h4 := Set.ncard_le_ncard hsub ((R.α_finite t0).subset fun q hq => hq.1)
                have h5 : (({q | R.α q < R.α π - (γ₁ + γ₂ + Z) ∧ (t0 : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) ≤
                    (({q | R.α q ≤ t0 ∧ (t0 : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) := by exact_mod_cast h4
                have h6 := mul_le_mul_of_nonneg_left h5 (by linarith : 0 ≤ L.wbar + ε)
                exact_mod_cast (by linarith)
              · exact ⟨0, le_rfl, fun h => absurd h hK⟩
            clear svcSet workCons overtake chainStep chain relPrec αle toExit order waitB arrOrder Hlev wnn wle mw
            choose cf hcf0 hcf using Hd
            set C := γ₁ + γ₂ + Z with hCdef
            set K0 := lam * (2 * C + 1) + γ with hK0
            have hK0nn : 0 ≤ K0 := by positivity
            set s := L.wbar + ε with hsdef
            have hs0 : 0 ≤ s := by positivity
            have xconv : ∀ (R : Run L) (t M : ℝ),
                (({q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) ≤ M →
                ((R.x t : ℕ∞) : ENNReal) ≤ ENNReal.ofReal M := by
              intro R t M h
              unfold Run.x
              have hfin : {p | R.α p ≤ t ∧ (t : WithTop ℝ) < R.exit p}.Finite :=
                (R.α_finite t).subset (fun p hp => hp.1)
              rw [← hfin.cast_ncard_eq]
              by_cases h0 : {q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard = 0
              · rw [h0]; simp
              · have : ((({q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℕ∞) : ENNReal) =
                    (({q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ENNReal) := rfl
                rw [this, ENNReal.natCast_le_ofReal h0]; exact h
            -- window bounds
            have winA : ∀ (R : Run L), R.Arrivals lam γ → ∀ q s0, 0 ≤ s0 → R.α q - C - 1 ≤ s0 → s0 ≤ R.α q + C →
                ({p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ R.α q + C}.ncard : ℝ) ≤ K0 := by
              intro R hArr q s0 h1 h2 h3
              have := arrR R hArr s0 (R.α q + C) h1 h3
              have : lam * (R.α q + C - s0) ≤ lam * (2 * C + 1) := mul_le_mul_of_nonneg_left (by linarith) hlam
              linarith
            have winLate : ∀ (R : Run L), R.Arrivals lam γ → ∀ q, C + 1 ≤ R.α q →
                ({q' | R.α q - C ≤ R.α q' ∧ R.α q' ≤ R.α q + C}.ncard : ℝ) ≤ K0 := by
              intro R hArr q hq
              have hsub : {q' | R.α q - C ≤ R.α q' ∧ R.α q' ≤ R.α q + C} ⊆
                  {p | ¬ R.initial p ∧ R.α q - C - 1 < R.α p ∧ R.α p ≤ R.α q + C} := by
                intro p hp
                refine ⟨fun hi => ?_, by linarith [hp.1], hp.2⟩
                have := R.α_initial p hi; linarith [hp.1]
              have h1 := Set.ncard_le_ncard hsub ((R.α_finite (R.α q + C)).subset fun p hp => hp.2.2)
              have h2 := winA R hArr q (R.α q - C - 1) (by linarith) le_rfl (by linarith)
              have h3 : (({q' | R.α q - C ≤ R.α q' ∧ R.α q' ≤ R.α q + C}.ncard : ℕ) : ℝ) ≤
                  (({p | ¬ R.initial p ∧ R.α q - C - 1 < R.α p ∧ R.α p ≤ R.α q + C}.ncard : ℕ) : ℝ) := by
                exact_mod_cast h1
              linarith
            have winAll : ∀ (R : Run L) (δ : R.Part → ℝ), R.Arrivals lam γ → LSAdmissible R δ ζ →
                ∀ q, ({q' | R.α q - C ≤ R.α q' ∧ R.α q' ≤ R.α q + C}.ncard : ℝ) ≤
                  ({q | R.α q ≤ 0 ∧ ((0:ℝ) : WithTop ℝ) < R.exit q}.ncard : ℝ) + K0 := by
              intro R δ hArr hLS q
              have hαq := αnn R q
              obtain ⟨s0, hs0a, hs0b, hs0c, hs0d⟩ : ∃ s0 : ℝ, 0 ≤ s0 ∧ R.α q - C - 1 ≤ s0 ∧ s0 ≤ R.α q + C ∧
                  ∀ p, 0 < R.α p → R.α q - C ≤ R.α p → s0 < R.α p := by
                by_cases hc : R.α q - C - 1 ≤ 0
                · exact ⟨0, le_rfl, hc, by linarith, fun p h _ => h⟩
                · rw [not_le] at hc
                  exact ⟨R.α q - C - 1, hc.le, le_rfl, by linarith, fun p _ h => by linarith⟩
              have hsub : {q' | R.α q - C ≤ R.α q' ∧ R.α q' ≤ R.α q + C} ⊆
                  {q | R.α q ≤ 0 ∧ ((0:ℝ) : WithTop ℝ) < R.exit q} ∪
                    {p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ R.α q + C} := by
                intro p hp
                by_cases h : R.α p ≤ 0
                · left
                  refine ⟨h, ?_⟩
                  have := exitGt R δ hLS p
                  have hp0 : R.α p = 0 := le_antisymm h (αnn R p)
                  rw [hp0] at this; exact this
                · right
                  rw [not_le] at h
                  refine ⟨fun hi => ?_, hs0d p h hp.1, hp.2⟩
                  have := R.α_initial p hi; linarith
              have hfin : ({q | R.α q ≤ 0 ∧ ((0:ℝ) : WithTop ℝ) < R.exit q} ∪
                    {p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ R.α q + C}).Finite :=
                (R.α_finite (R.α q + C)).subset (by
                  rintro p (⟨h1, _⟩ | ⟨_, _, h2⟩)
                  · show R.α p ≤ R.α q + C; linarith
                  · exact h2)
              have h1 := (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
              have h2 := winA R hArr q s0 hs0a hs0b hs0c
              have h3 : (({q' | R.α q - C ≤ R.α q' ∧ R.α q' ≤ R.α q + C}.ncard : ℕ) : ℝ) ≤
                  (({q | R.α q ≤ 0 ∧ ((0:ℝ) : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) +
                  (({p | ¬ R.initial p ∧ s0 < R.α p ∧ R.α p ≤ R.α q + C}.ncard : ℕ) : ℝ) := by
                rw [← Nat.cast_add]; exact Nat.cast_le.mpr h1
              exact h3.trans (add_le_add le_rfl h2)
            have hρs : lam * s < 1 := hρ
            set an : ℕ → ℝ := fun n => lam * (1 + cf ((n : ℝ) + K0)) + γ with han
            set Mn : ℕ → ℝ := fun n => max (n : ℝ) (an n / (1 - lam * s)) * (1 + lam * s) + an n with hMn
            set a0 := lam * (1 + cf K0) + γ with ha0
            refine ⟨fun n => Mn n + 1, (a0 / (1 - lam * s) + 1) * (1 + lam * s) + a0, ?_, ?_⟩
            · have : 0 ≤ cf K0 := hcf0 K0
              have : 0 ≤ a0 := by positivity
              have : 0 ≤ a0 / (1 - lam * s) := div_nonneg this (by linarith)
              have : 0 ≤ lam * s := mul_nonneg hlam hs0
              positivity
            intro R δ hArr hW hLS n hn
            have hX0 : (({q | R.α q ≤ 0 ∧ ((0:ℝ) : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) = n := by
              have h := hn
              unfold Run.x at h
              rw [Set.ncard_def, h]; simp
            have hKn : 0 ≤ (n : ℝ) + K0 := by positivity
            have hPn := hcf ((n : ℝ) + K0) hKn R δ hW hLS 0 le_rfl (fun q _ => by
              have := winAll R δ hArr hLS q; rw [hX0] at this; exact this)
            obtain ⟨hsup, -⟩ := Thm3 (cf ((n : ℝ) + K0)) s (hcf0 _) hs0 hρs R δ hArr hLS 0 le_rfl
              (fun π t0 h1 h2 => hPn π t0 h1 h2)
            rw [hX0] at hsup
            have hsupM : ∀ t, 0 ≤ t → (({q | R.α q ≤ t ∧ (t : WithTop ℝ) < R.exit q}.ncard : ℕ) : ℝ) ≤ Mn n :=
              fun t ht => hsup t ht
            have hMn0 : 0 ≤ Mn n := by
              have := hsupM 0 le_rfl
              exact le_trans (Nat.cast_nonneg _) this
            constructor
            · refine lt_of_le_of_lt (iSup_le fun t => xconv R t.1 (Mn n) (hsupM t.1 t.2)) ?_
              rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
              linarith
            · set tst := C + 1 + cf ((n : ℝ) + K0) + s * Mn n with htst
              have htst0 : 0 ≤ tst := by
                have := hcf0 ((n : ℝ) + K0)
                have := mul_nonneg hs0 hMn0
                linarith
              have hwin : ∀ q, (tst : WithTop ℝ) < R.exit q →
                  ({q' | R.α q - C ≤ R.α q' ∧ R.α q' ≤ R.α q + C}.ncard : ℝ) ≤ K0 := by
                intro q hq
                by_cases hα : C + 1 ≤ R.α q
                · exact winLate R hArr q hα
                · exfalso
                  rw [not_le] at hα
                  have h1 := hPn q (R.α q) (αnn R q) le_rfl
                  have h2 := hsupM (R.α q) (αnn R q)
                  have h3 : s * (({q' | R.α q' ≤ R.α q ∧ ((R.α q : ℝ) : WithTop ℝ) < R.exit q'}.ncard : ℕ) : ℝ) ≤
                      s * Mn n := mul_le_mul_of_nonneg_left h2 hs0
                  have h4 : R.exit q ≤ (tst : WithTop ℝ) := h1.trans (by exact_mod_cast (by linarith))
                  exact absurd (lt_of_lt_of_le hq h4) (lt_irrefl _)
              have hP0 := hcf K0 hK0nn R δ hW hLS tst htst0 hwin
              obtain ⟨-, T, hT⟩ := Thm3 (cf K0) s (hcf0 _) hs0 hρs R δ hArr hLS tst htst0
                (fun π t0 h1 h2 => hP0 π t0 h1 h2)
              unfold populationLimsup
              apply Filter.limsup_le_of_le
              · isBoundedDefault
              · rw [Filter.eventually_atTop]
                exact ⟨T, fun t ht => xconv R t _ (hT t ht)⟩
