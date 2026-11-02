-- Prove2me | solution 1 for QuantumMaxCutEnergy.matching_rounding_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T17:43:25.879872+00:00
-- url     : https://prove2.me/submissions/8657e7d3-cbd2-488f-a59c-494e9cacd78f

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

open scoped BigOperators

namespace QuantumMaxCutEnergy

variable {n : ℕ}

/-! ### Bridging the vertex-indexed star sum to an edge-indexed sum -/

/-- The total `x`-mass of the edges incident to vertex `i`, indexed by edges. -/
private def edgeStarSum (x : Edge n → ℝ) (i : Fin n) : ℝ :=
  ∑ e : Edge n, (if e.val.1 = i ∨ e.val.2 = i then x e else 0)

private theorem edgeStarSum_eq (x : Edge n → ℝ) (i : Fin n) :
    edgeStarSum x i = ∑ j : Fin n, (if h : i < j then x ⟨(i, j), h⟩
      else if h : j < i then x ⟨(j, i), h⟩ else 0) := by
  set s : Finset (Edge n) :=
    Finset.univ.filter (fun e => e.val.1 = i ∨ e.val.2 = i) with hsdef
  have h1 : edgeStarSum x i = ∑ e ∈ s, x e := by
    rw [hsdef, edgeStarSum, ← Finset.sum_filter]
  have hmem_other : ∀ e ∈ s, (if e.val.1 = i then e.val.2 else e.val.1) ≠ i := by
    intro e he
    have hep := e.property
    split <;> omega
  have h2 : ∑ e ∈ s, x e = ∑ j ∈ Finset.univ.erase i,
      (if h : i < j then x ⟨(i, j), h⟩ else if h : j < i then x ⟨(j, i), h⟩ else 0) := by
    refine Finset.sum_bij (fun e _ => if e.val.1 = i then e.val.2 else e.val.1)
      (fun e he => Finset.mem_erase.mpr ⟨hmem_other e he, Finset.mem_univ _⟩) ?_ ?_ ?_
    · -- injectivity
      intro a ha b hb hab
      have hap := a.property
      have hbp := b.property
      by_cases ha₁ : a.val.1 = i
      · by_cases hb₁ : b.val.1 = i
        · simp only [if_pos ha₁, if_pos hb₁] at hab
          refine Subtype.ext ?_
          show (a.val.1, a.val.2) = (b.val.1, b.val.2)
          rw [ha₁, hb₁, hab]
        · simp only [if_pos ha₁, if_neg hb₁] at hab
          have hb₂ : b.val.2 = i := by
            rcases (Finset.mem_filter.mp hb).2 with h | h
            · exact absurd h hb₁
            · exact h
          omega
      · by_cases hb₁ : b.val.1 = i
        · simp only [if_neg ha₁, if_pos hb₁] at hab
          have ha₂ : a.val.2 = i := by
            rcases (Finset.mem_filter.mp ha).2 with h | h
            · exact absurd h ha₁
            · exact h
          omega
        · simp only [if_neg ha₁, if_neg hb₁] at hab
          have ha₂ : a.val.2 = i := by
            rcases (Finset.mem_filter.mp ha).2 with h | h
            · exact absurd h ha₁
            · exact h
          have hb₂ : b.val.2 = i := by
            rcases (Finset.mem_filter.mp hb).2 with h | h
            · exact absurd h hb₁
            · exact h
          refine Subtype.ext ?_
          show (a.val.1, a.val.2) = (b.val.1, b.val.2)
          rw [ha₂, hb₂, hab]
    · -- surjectivity
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rcases Fin.lt_or_ge i j with hlt | hge
      · refine ⟨⟨(i, j), hlt⟩, ?_, ?_⟩
        · rw [hsdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, Or.inl rfl⟩
        · show (if (⟨(i, j), hlt⟩ : Edge n).val.1 = i then (⟨(i, j), hlt⟩ : Edge n).val.2
              else (⟨(i, j), hlt⟩ : Edge n).val.1) = j
          rw [if_pos rfl]
      · rcases eq_or_lt_of_le hge with heq | hjlt
        · exact absurd heq hji
        · refine ⟨⟨(j, i), hjlt⟩, ?_, ?_⟩
          · rw [hsdef, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, Or.inr rfl⟩
          · show (if (⟨(j, i), hjlt⟩ : Edge n).val.1 = i then (⟨(j, i), hjlt⟩ : Edge n).val.2
                else (⟨(j, i), hjlt⟩ : Edge n).val.1) = j
            rw [if_neg (Fin.ne_of_lt hjlt)]
    · -- agreement
      intro e he
      by_cases hc : e.val.1 = i
      · have hlt : i < e.val.2 := hc ▸ e.property
        rw [if_pos hc, dif_pos hlt]
        congr 1
        refine Subtype.ext ?_
        show (e.val.1, e.val.2) = (i, e.val.2)
        rw [hc]
      · have heq : e.val.2 = i := by
          rcases (Finset.mem_filter.mp he).2 with h | h
          · exact absurd h hc
          · exact h
        have hlt : e.val.1 < i := heq ▸ e.property
        rw [if_neg hc, dif_neg (by omega), dif_pos (by omega)]
        congr 1
        refine Subtype.ext ?_
        show (e.val.1, e.val.2) = (e.val.1, i)
        rw [heq]
  -- fold the erased vertex back in
  have hzero : (if h : i < i then x ⟨(i, i), h⟩
      else if h : i < i then x ⟨(i, i), h⟩ else 0) = 0 := by
    rw [dif_neg (by omega), dif_neg (by omega)]
  have h3 := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
    (h := Finset.mem_univ i)
    (f := fun j : Fin n => (if h : i < j then x ⟨(i, j), h⟩ else if h : j < i then x ⟨(j, i), h⟩ else 0))
  rw [h1, h2, ← h3, hzero]
  ring

private theorem edgeStarSum_le_one (x : Edge n → ℝ)
    (hstar : ∀ i : Fin n, ∑ j : Fin n, (if h : i < j then x ⟨(i, j), h⟩
      else if h : j < i then x ⟨(j, i), h⟩ else 0) ≤ 1) (i : Fin n) :
    edgeStarSum x i ≤ 1 := by
  rw [edgeStarSum_eq]; exact hstar i

/-! ### The greedy half-rounding -/

private theorem exists_matching_aux {n : ℕ} (w : Weights n) (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hstar : ∀ i : Fin n, edgeStarSum x i ≤ 1) :
    ∀ m : ℕ, ∀ S : Finset (Edge n), S.card ≤ m →
      ∃ M : Finset (Edge n), (∀ e ∈ M, e ∈ S) ∧
        (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧
          e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
        (1 / 2 : ℝ) * ∑ e ∈ S, (w e : ℝ) * x e ≤ ∑ e ∈ M, (w e : ℝ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m IH =>
    intro S hS
    by_cases hz : ∀ e ∈ S, x e = 0
    · refine ⟨∅, ?_, ?_, ?_⟩
      · intro e he; exact absurd he (by simp)
      · intro e he e' he' _; exact absurd he (by simp)
      · have hsum : ∑ e ∈ S, (w e : ℝ) * x e = 0 := by
          refine Finset.sum_eq_zero (fun e he => ?_)
          rw [hz e he, mul_zero]
        rw [Finset.sum_empty, hsum, mul_zero]
    · -- pick the heaviest x-positive edge of S
      push_neg at hz
      obtain ⟨e₁, he₁S, hx₁⟩ := hz
      have hx₁lt : 0 < x e₁ := lt_of_le_of_ne (hx e₁) (Ne.symm hx₁)
      set F : Finset (Edge n) := S.filter (fun e => 0 < x e) with hFdef
      have hFne : F.Nonempty := ⟨e₁, by simp [hFdef, he₁S, hx₁lt]⟩
      have himg : (F.image (fun e => (w e : ℝ))).Nonempty := hFne.image _
      obtain ⟨e₀, hemax, hwe₀⟩ :=
        Finset.mem_image.mp (Finset.max'_mem (F.image (fun e => (w e : ℝ))) himg)
      have hwpos : 0 ≤ (w e₀ : ℝ) := NNRat.cast_nonneg _
      have hmax : ∀ e ∈ F, (w e : ℝ) ≤ (w e₀ : ℝ) := by
        intro e he
        rw [hwe₀]
        exact Finset.le_max' (F.image (fun e => (w e : ℝ))) (w e : ℝ)
          (Finset.mem_image_of_mem (fun e => (w e : ℝ)) he)
      set u := e₀.val.1 with hudef
      set v := e₀.val.2 with hvdef
      set S₁ : Finset (Edge n) :=
        S.filter (fun f => f.val.1 = u ∨ f.val.2 = u ∨ f.val.1 = v ∨ f.val.2 = v) with hS₁def
      set T : Finset (Edge n) := S \ S₁ with hTdef
      have hS₁sub : S₁ ⊆ S := Finset.filter_subset _ _
      have he₀S₁ : e₀ ∈ S₁ := by
        simp only [hS₁def, Finset.mem_filter, Finset.mem_univ, true_and, hudef]
        exact ⟨(Finset.mem_filter.mp hemax).1, Or.inl trivial⟩
      have he₀T : e₀ ∉ T := by
        rw [hTdef]
        intro hc
        exact (Finset.mem_sdiff.mp hc).2 he₀S₁
      have hTcard : T.card < m := by
        have hsub : T ⊆ S.erase e₀ := by
          intro e he
          rw [hTdef] at he
          have heS : e ∈ S := (Finset.mem_sdiff.mp he).1
          have heS₁ : e ∉ S₁ := (Finset.mem_sdiff.mp he).2
          refine Finset.mem_erase.mpr ⟨fun hc => heS₁ (by rw [hc]; exact he₀S₁), heS⟩
        have hcard : T.card ≤ (S.erase e₀).card := Finset.card_le_card hsub
        have herase : (S.erase e₀).card = S.card - 1 :=
          Finset.card_erase_of_mem (Finset.mem_filter.mp hemax).1
        have hpos : 0 < S.card := by
          have hne : S.Nonempty := ⟨e₀, (Finset.mem_filter.mp hemax).1⟩
          exact hne.card_pos
        omega
      obtain ⟨M₁, hM₁S, hM₁match, hM₁w⟩ := IH T.card hTcard T le_rfl
      -- weight bookkeeping
      have hsplit : ∑ e ∈ S, (w e : ℝ) * x e
          = ∑ e ∈ T, (w e : ℝ) * x e + ∑ e ∈ S₁, (w e : ℝ) * x e := by
        rw [hTdef, ← Finset.sum_sdiff hS₁sub]
      have hS₁bound : ∑ e ∈ S₁, (w e : ℝ) * x e ≤ 2 * (w e₀ : ℝ) := by
        have hterm : ∑ e ∈ S₁, (w e : ℝ) * x e ≤ (w e₀ : ℝ) * ∑ e ∈ S₁, x e := by
          have key : ∑ e ∈ S₁, (w e : ℝ) * x e ≤ ∑ e ∈ S₁, (w e₀ : ℝ) * x e := by
            refine Finset.sum_le_sum (fun e he => ?_)
            by_cases hxz : x e = 0
            · rw [hxz, mul_zero, mul_zero]
            · have heF : e ∈ F := by
                simp only [hFdef, Finset.mem_filter]
                exact ⟨hS₁sub he, lt_of_le_of_ne (hx e) (Ne.symm hxz)⟩
              exact mul_le_mul_of_nonneg_right (hmax e heF) (hx e)
          rw [Finset.mul_sum]
          exact key
        have hstar2 : ∑ e ∈ S₁, x e ≤ 2 := by
          set Au : Finset (Edge n) :=
            Finset.univ.filter (fun e => e.val.1 = u ∨ e.val.2 = u) with hAudef
          set Av : Finset (Edge n) :=
            Finset.univ.filter (fun e => e.val.1 = v ∨ e.val.2 = v) with hAvdef
          have hsub : S₁ ⊆ Au ∪ Av := by
            intro e he
            simp only [hS₁def, Finset.mem_filter, Finset.mem_univ, true_and] at he
            simp only [Finset.mem_union, hAudef, hAvdef, Finset.mem_filter,
              Finset.mem_univ, true_and]
            tauto
          have hAuSub : Au ⊆ Au ∪ Av := Finset.subset_union_left
          have hco : (Au ∪ Av) \ Au = Av \ Au := by
            ext e
            simp only [Finset.mem_sdiff, Finset.mem_union]
            tauto
          have hle : ∑ e ∈ Au ∪ Av, x e ≤ ∑ e ∈ Au, x e + ∑ e ∈ Av, x e := by
            have hsp : ∑ e ∈ ((Au ∪ Av) \ Au : Finset (Edge n)), x e + ∑ e ∈ Au, x e
                = ∑ e ∈ Au ∪ Av, x e := Finset.sum_sdiff hAuSub
            rw [hco] at hsp
            have hmon : ∑ e ∈ Av \ Au, x e ≤ ∑ e ∈ Av, x e :=
              Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => (Finset.mem_sdiff.mp ha).1)
                (fun a _ _ => hx a)
            linarith
          have hAu : ∑ e ∈ Au, x e = edgeStarSum x u := by
            rw [hAudef, edgeStarSum, ← Finset.sum_filter]
          have hAv : ∑ e ∈ Av, x e = edgeStarSum x v := by
            rw [hAvdef, edgeStarSum, ← Finset.sum_filter]
          have hmono : ∑ e ∈ S₁, x e ≤ ∑ e ∈ Au ∪ Av, x e :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hx a)
          have key := hle
          rw [hAu, hAv] at key
          linarith [hmono, key, hstar u, hstar v]
        calc ∑ e ∈ S₁, (w e : ℝ) * x e ≤ (w e₀ : ℝ) * ∑ e ∈ S₁, x e := hterm
          _ ≤ (w e₀ : ℝ) * 2 := mul_le_mul_of_nonneg_left hstar2 hwpos
          _ = 2 * (w e₀ : ℝ) := by ring
      refine ⟨insert e₀ M₁, ?_, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact (Finset.mem_filter.mp hemax).1
        · exact (Finset.mem_sdiff.mp (hM₁S e he)).1
      · intro e he e' he' hne
        rcases Finset.mem_insert.mp he with hee₀ | heM
        · rcases Finset.mem_insert.mp he' with he'e₀ | he'M
          · exact absurd (hee₀.trans he'e₀.symm) hne
          · have he'S : e' ∈ S := (Finset.mem_sdiff.mp (hM₁S e' he'M)).1
            have heS₁ : e' ∉ S₁ := (Finset.mem_sdiff.mp (hM₁S e' he'M)).2
            have h4 : ¬(e'.val.1 = u ∨ e'.val.2 = u ∨ e'.val.1 = v ∨ e'.val.2 = v) := fun hc =>
              heS₁ (by
                rw [hS₁def, Finset.mem_filter]
                exact ⟨he'S, hc⟩)
            simp only [hudef, hvdef, not_or] at h4
            rw [hee₀]
            exact ⟨fun hc => h4.1 hc.symm, fun hc => h4.2.1 hc.symm,
              fun hc => h4.2.2.1 hc.symm, fun hc => h4.2.2.2 hc.symm⟩
        · rcases Finset.mem_insert.mp he' with he'e₀ | he'M
          · have heS : e ∈ S := (Finset.mem_sdiff.mp (hM₁S e heM)).1
            have heS₁ : e ∉ S₁ := (Finset.mem_sdiff.mp (hM₁S e heM)).2
            have h4 : ¬(e.val.1 = u ∨ e.val.2 = u ∨ e.val.1 = v ∨ e.val.2 = v) := fun hc =>
              heS₁ (by
                rw [hS₁def, Finset.mem_filter]
                exact ⟨heS, hc⟩)
            simp only [hudef, hvdef, not_or] at h4
            rw [he'e₀]
            exact ⟨h4.1, h4.2.2.1, h4.2.1, h4.2.2.2⟩
          · exact hM₁match e heM e' he'M hne
      · have hhalfS₁ : (1 / 2 : ℝ) * ∑ e ∈ S₁, (w e : ℝ) * x e ≤ (w e₀ : ℝ) := by
          have h1 : (1 / 2 : ℝ) * ∑ e ∈ S₁, (w e : ℝ) * x e
              ≤ (1 / 2 : ℝ) * (2 * (w e₀ : ℝ)) :=
            mul_le_mul_of_nonneg_left hS₁bound (by norm_num)
          have h2 : (1 / 2 : ℝ) * (2 * (w e₀ : ℝ)) = (w e₀ : ℝ) := by ring
          rw [h2] at h1
          exact h1
        have he₀M₁ : e₀ ∉ M₁ := by
          intro hc
          exact he₀T (hM₁S e₀ hc)
        calc (1 / 2 : ℝ) * ∑ e ∈ S, (w e : ℝ) * x e
            = (1 / 2 : ℝ) * (∑ e ∈ T, (w e : ℝ) * x e + ∑ e ∈ S₁, (w e : ℝ) * x e) := by
              rw [hsplit]
          _ = (1 / 2 : ℝ) * ∑ e ∈ T, (w e : ℝ) * x e
              + (1 / 2 : ℝ) * ∑ e ∈ S₁, (w e : ℝ) * x e := by ring
          _ ≤ ∑ e ∈ M₁, (w e : ℝ) + (w e₀ : ℝ) := by linarith [hM₁w, hhalfS₁]
          _ = ∑ e ∈ insert e₀ M₁, (w e : ℝ) := by
              rw [Finset.sum_insert he₀M₁]; ring

end QuantumMaxCutEnergy

/-- **Fractional-matching half-rounding.** If `x` gives every edge of a weighted
graph a nonnegative mass and the incident mass at every vertex is at most `1`,
then some matching carries at least half of the total `weight * x` mass. -/
theorem solution (G : QuantumMaxCutEnergy.Input) (x : QuantumMaxCutEnergy.Edge G.n → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hstar : ∀ i : Fin G.n, ∑ j : Fin G.n, (if h : i < j then x ⟨(i, j), h⟩
      else if h : j < i then x ⟨(j, i), h⟩ else 0) ≤ 1) :
    ∃ M : Finset (QuantumMaxCutEnergy.Edge G.n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧
        e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (1 / 2 : ℝ) * ∑ e, (G.weights e : ℝ) * x e ≤ ∑ e ∈ M, (G.weights e : ℝ) := by
  have h := QuantumMaxCutEnergy.exists_matching_aux G.weights x hx
    (fun i => QuantumMaxCutEnergy.edgeStarSum_le_one x hstar i)
  obtain ⟨M, -, hmatch, hw⟩ :=
    h (Fintype.card (QuantumMaxCutEnergy.Edge G.n)) Finset.univ (by rw [Finset.card_univ])
  exact ⟨M, hmatch, hw⟩

#print axioms solution
