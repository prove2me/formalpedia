-- Prove2me | solution 1 for RobustMultitask.Estimator.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:39:33.076172+00:00
-- url     : https://prove2.me/submissions/522d05a7-14bb-439e-934b-dd9409e9086a

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal
theorem abs_sum_le_card_mul {α : Type*} (A : Finset α) (f : α → ℝ) (r : ℝ)
    (h : ∀ j ∈ A, |f j| ≤ r) : |∑ j ∈ A, f j| ≤ A.card * r := by
  calc |∑ j ∈ A, f j| ≤ ∑ j ∈ A, |f j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ A, r := sum_le_sum h
    _ = A.card * r := by rw [sum_const, nsmul_eq_mul]

theorem card_kept (N m : ℕ) (h2m : 2 * m ≤ N) :
    (univ.filter (fun ι : Fin N => m ≤ ι.val ∧ ι.val + m < N)).card = N - 2 * m := by
  have : (univ.filter (fun ι : Fin N => m ≤ ι.val ∧ ι.val + m < N)).map Fin.valEmbedding
      = Finset.Ico m (N - m) := by
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_Ico]
    constructor
    · rintro ⟨ι, ⟨h1, h2⟩, rfl⟩; omega
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, by omega⟩, ⟨h1, by simp; omega⟩, rfl⟩
  rw [← card_map, this, Nat.card_Ico]; omega

theorem det_trim {N : ℕ} (z : Fin N → ℝ) (mu r : ℝ) (m : ℕ) (𝒥 : Finset (Fin N)) (hr : 0 ≤ r)
    (h2m : 2 * m ≤ N) (hbad : (univ.filter (fun j => r < |z j - mu|)).card ≤ m) :
    |(∑ ι ∈ univ.filter (fun ι : Fin N => m ≤ ι.val ∧ ι.val + m < N), z (Tuple.sort z ι))
        - ((N : ℝ) - 2 * m) * mu|
      ≤ 𝒥.card * r + 2 * m * r + |∑ j ∈ 𝒥ᶜ, (if |z j - mu| ≤ r then z j - mu else 0)| := by
  classical
  set K := univ.filter (fun ι : Fin N => m ≤ ι.val ∧ ι.val + m < N) with hKdef
  set e := Tuple.sort z with he
  set T := K.map e.toEmbedding with hT
  have hmono := Tuple.monotone_sort z
  have hTcard : T.card = N - 2 * m := by rw [hT, card_map, hKdef, card_kept N m h2m]
  have hsum : ∑ ι ∈ K, z (e ι) = ∑ j ∈ T, z j := by rw [hT, sum_map]; rfl
  -- every kept sample lies in `[mu - r, mu + r]`
  have hin : ∀ j ∈ T, |z j - mu| ≤ r := by
    intro j hj
    rw [hT, mem_map] at hj
    obtain ⟨ι, hι, rfl⟩ := hj
    rw [hKdef, mem_filter] at hι
    obtain ⟨-, hι1, hι2⟩ := hι
    by_contra hcon
    push Not at hcon
    simp only [Equiv.toEmbedding_apply] at hcon
    rcases lt_abs.1 hcon with hpos | hneg
    · -- too large: all later order statistics are bad too
      have hsub : (Finset.Ici ι).map e.toEmbedding ⊆ univ.filter (fun j => r < |z j - mu|) := by
        intro x hx
        rw [mem_map] at hx
        obtain ⟨ι', hι', rfl⟩ := hx
        rw [mem_Ici] at hι'
        have := hmono hι'
        simp only [Function.comp, ← he] at this
        simp only [mem_filter, mem_univ, true_and]
        rw [lt_abs]; left
        simp only [Equiv.toEmbedding_apply]
        linarith
      have := card_le_card hsub
      rw [card_map, Fin.card_Ici] at this
      omega
    · have hsub : (Finset.Iic ι).map e.toEmbedding ⊆ univ.filter (fun j => r < |z j - mu|) := by
        intro x hx
        rw [mem_map] at hx
        obtain ⟨ι', hι', rfl⟩ := hx
        rw [mem_Iic] at hι'
        have := hmono hι'
        simp only [Function.comp, ← he] at this
        simp only [mem_filter, mem_univ, true_and]
        rw [lt_abs]; right
        simp only [Equiv.toEmbedding_apply]
        linarith
      have := card_le_card hsub
      rw [card_map, Fin.card_Iic] at this
      omega
  set y : Fin N → ℝ := fun j => if |z j - mu| ≤ r then z j - mu else 0 with hydef
  have hy : ∀ j, |y j| ≤ r := by
    intro j; simp only [hydef]; split_ifs with h
    · exact h
    · simpa using hr
  have hcenter : ∑ j ∈ T, z j - ((N : ℝ) - 2 * m) * mu = ∑ j ∈ T, (z j - mu) := by
    rw [sum_sub_distrib, sum_const, hTcard, nsmul_eq_mul, Nat.cast_sub h2m]
    push_cast; ring
  have hsplit1 : ∑ j ∈ T, (z j - mu)
      = ∑ j ∈ T.filter (· ∈ 𝒥), (z j - mu) + ∑ j ∈ T.filter (· ∉ 𝒥), y j := by
    rw [← sum_filter_add_sum_filter_not T (· ∈ 𝒥)]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [mem_filter] at hj
    simp only [hydef, if_pos (hin j hj.1)]
  have hsplit2 : ∑ j ∈ 𝒥ᶜ, y j = ∑ j ∈ 𝒥ᶜ.filter (· ∈ T), y j + ∑ j ∈ 𝒥ᶜ.filter (· ∉ T), y j :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hsetEq : T.filter (· ∉ 𝒥) = 𝒥ᶜ.filter (· ∈ T) := by
    ext j; simp only [mem_filter, mem_compl]; tauto
  have hb1 : |∑ j ∈ T.filter (· ∈ 𝒥), (z j - mu)| ≤ 𝒥.card * r := by
    refine (abs_sum_le_card_mul _ _ r (fun j hj => hin j (mem_filter.1 hj).1)).trans ?_
    gcongr
    intro j hj; exact (mem_filter.1 hj).2
  have hb2 : |∑ j ∈ 𝒥ᶜ.filter (· ∉ T), y j| ≤ 2 * m * r := by
    refine (abs_sum_le_card_mul _ _ r (fun j _ => hy j)).trans ?_
    have hc : (𝒥ᶜ.filter (· ∉ T)).card ≤ 2 * m := by
      have h1 : 𝒥ᶜ.filter (· ∉ T) ⊆ Tᶜ := by
        intro j hj; rw [mem_compl]; exact (mem_filter.1 hj).2
      have := card_le_card h1
      rw [card_compl, Fintype.card_fin, hTcard] at this
      omega
    have : ((𝒥ᶜ.filter (· ∉ T)).card : ℝ) ≤ 2 * m := by exact_mod_cast hc
    nlinarith
  rw [hsum, hcenter, hsplit1, hsetEq]
  have heq : ∑ j ∈ 𝒥ᶜ.filter (· ∈ T), y j = ∑ j ∈ 𝒥ᶜ, y j - ∑ j ∈ 𝒥ᶜ.filter (· ∉ T), y j := by
    rw [hsplit2]; ring
  rw [heq]
  calc |∑ j ∈ T.filter (· ∈ 𝒥), (z j - mu) + (∑ j ∈ 𝒥ᶜ, y j - ∑ j ∈ 𝒥ᶜ.filter (· ∉ T), y j)|
      ≤ |∑ j ∈ T.filter (· ∈ 𝒥), (z j - mu)| + (|∑ j ∈ 𝒥ᶜ, y j|
          + |∑ j ∈ 𝒥ᶜ.filter (· ∉ T), y j|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ _ := by linarith

/-- A subgaussian random variable has mean zero. -/
theorem sg_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c P) :
    P[X] = 0 := by
  have hint : (0 : ℝ) ∈ interior (integrableExpSet X P) := by
    simp [h.integrableExpSet_eq_univ]
  have hd1 := hasDerivAt_mgf hint
  simp only [zero_mul, exp_zero, mul_one] at hd1
  have hd2 : HasDerivAt (fun t : ℝ => exp ((c : ℝ) * t ^ 2 / 2)) 0 0 := by
    have := ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (c : ℝ)).div_const 2 |>.exp
    simpa using this
  have hmin : IsLocalMin (fun t => exp ((c : ℝ) * t ^ 2 / 2) - mgf X P t) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have := h.mgf_le t
    have h0 : mgf X P 0 = 1 := by rw [mgf_zero']; simp
    simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      exp_zero, sub_self]
    linarith
  have := hmin.hasDerivAt_eq_zero (hd2.sub hd1)
  linarith

/-- Expectation bound via the MGF. -/
theorem sg_expect_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c P)
    (g : ℝ → ℝ) (hg : Measurable g) (A l : ℝ)
    (hgb : ∀ x, |g x| ≤ A * (exp (l * x) + exp (-l * x))) :
    Integrable (fun ω => g (X ω)) P ∧
      |P[fun ω => g (X ω)]| ≤ 2 * A * exp (c * l ^ 2 / 2) := by
  have hi1 := h.integrable_exp_mul l
  have hi2 := h.integrable_exp_mul (-l)
  have hdom : Integrable (fun ω => A * (exp (l * X ω) + exp (-l * X ω))) P :=
    (hi1.add hi2).const_mul A
  have hgi : Integrable (fun ω => g (X ω)) P := by
    refine hdom.mono' (hg.comp_aemeasurable h.aemeasurable).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hgb (X ω)
  refine ⟨hgi, ?_⟩
  calc |∫ ω, g (X ω) ∂P| ≤ ∫ ω, |g (X ω)| ∂P := by
        rw [← Real.norm_eq_abs]
        exact (norm_integral_le_integral_norm _).trans (le_of_eq (by simp [Real.norm_eq_abs]))
    _ ≤ ∫ ω, A * (exp (l * X ω) + exp (-l * X ω)) ∂P :=
        integral_mono hgi.abs hdom (fun ω => hgb (X ω))
    _ = A * (mgf X P l + mgf X P (-l)) := by
        rw [integral_const_mul, integral_add hi1 hi2]; rfl
    _ ≤ A * (exp (c * l ^ 2 / 2) + exp (c * (-l) ^ 2 / 2)) := by
        have hA : 0 ≤ A := by
          have := hgb 0
          have h2 : 0 < exp (l * 0) + exp (-l * 0) := by positivity
          by_contra hneg; push Not at hneg
          have : A * (exp (l * 0) + exp (-l * 0)) < 0 := mul_neg_of_neg_of_pos hneg h2
          linarith [abs_nonneg (g 0)]
        gcongr
        · exact h.mgf_le l
        · exact h.mgf_le (-l)
    _ = 2 * A * exp (c * l ^ 2 / 2) := by rw [neg_sq]; ring

/-- Hoeffding tail for a sum of independent subgaussian variables over a finite type. -/
theorem sg_sum_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Type*} [Fintype H] (W : H → Ω → ℝ) (hind : iIndepFun W P) (c : ℝ≥0)
    (hW : ∀ j, HasSubgaussianMGF (W j) c P) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ ∑ j, W j ω} ≤ ENNReal.ofReal (exp (-t ^ 2 / (2 * (Fintype.card H * c)))) := by
  have h := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (c := fun _ => c)
    (fun j _ => hW j)
  have h2 := h.measure_ge_le ht
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : {ω | t ≤ ∑ j, W j ω} = {ω | t ≤ ∑ i ∈ Finset.univ, W i ω} := rfl
  have e2 : (∑ i ∈ (Finset.univ : Finset H), (fun _ => c) i : ℝ≥0) = Fintype.card H * c := by
    simp [Finset.card_univ]
  rw [e2] at h2
  simpa using h2

theorem exp_abs_le (l x : ℝ) (hl : 0 ≤ l) : exp (l * |x|) ≤ exp (l * x) + exp (-l * x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [exp_pos (-l * x)]
  · rw [abs_of_nonpos hx]; rw [show l * -x = -l * x by ring]; linarith [exp_pos (l * x)]

theorem cover_det {N : ℕ} (hNpos : 0 < N) (z : Fin N → ℝ) (𝒥 : Finset (Fin N))
    (mu ζ η C₀ τ s r : ℝ) (hC₀ : 2 < C₀) (hζ0 : 0 < ζ) (hη0 : 0 < η)
    (hη1 : η ≤ 1 / 2 - 1 / C₀ - ζ) (hcard : (𝒥.card : ℝ) < ζ * N)
    (hτ : 0 < τ) (hs : 0 < s) (hr : r = 2 * τ * s)
    (hcount : ((𝒥ᶜ.filter (fun j => r < |z j - mu|)).card : ℝ) < η * N)
    (hY : |∑ j ∈ 𝒥ᶜ, (if |z j - mu| ≤ r then z j - mu else 0)| < 2 * η * N * τ * s) :
    |RobustMultitask.Estimator.trimmedMean z (ζ + η) - mu| < C₀ * τ * (3 * ζ + 4 * η) * s := by
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hC0 : 0 < C₀ := by linarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hinvC : 0 < 1 / C₀ := by positivity
  have hω : 2 * (ζ + η) ≤ 1 - 2 / C₀ := by
    have : 2 / C₀ = 2 * (1 / C₀) := by ring
    linarith
  obtain ⟨m, hm⟩ : ∃ m, m = RobustMultitask.Estimator.trimCount N (ζ + η) := ⟨_, rfl⟩
  have hmle : (m : ℝ) ≤ N * (ζ + η) := hm ▸ Nat.floor_le (by positivity)
  have hpos2 : 0 < 1 - 2 * (ζ + η) := by
    have : 0 < 2 / C₀ := by positivity
    linarith
  have h2m : 2 * m ≤ N := by
    have : (2 * m : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hD : (N : ℝ) * (1 - 2 * (ζ + η)) ≤ (N : ℝ) - 2 * m := by nlinarith
  have hDpos : 0 < (N : ℝ) - 2 * m := by nlinarith
  have hCD : 2 * (N : ℝ) ≤ C₀ * ((N : ℝ) - 2 * m) := by
    have h1 : C₀ * (1 - 2 * (ζ + η)) ≥ 2 := by
      have : C₀ * (1 - 2 / C₀) = C₀ - 2 := by field_simp
      nlinarith
    nlinarith
  have hbad : (Finset.univ.filter (fun j => r < |z j - mu|)).card ≤ m := by
    have hsub : Finset.univ.filter (fun j => r < |z j - mu|)
        ⊆ 𝒥 ∪ 𝒥ᶜ.filter (fun j => r < |z j - mu|) := by
      intro j hj
      by_cases hjJ : j ∈ 𝒥
      · exact Finset.mem_union_left _ hjJ
      · apply Finset.mem_union_right
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hjJ, hj]
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcr : ((Finset.univ.filter (fun j => r < |z j - mu|)).card : ℝ) < N * (ζ + η) := by
      have : ((Finset.univ.filter (fun j => r < |z j - mu|)).card : ℝ)
          ≤ 𝒥.card + (𝒥ᶜ.filter (fun j => r < |z j - mu|)).card := by exact_mod_cast hc
      nlinarith
    rw [hm]; exact Nat.le_floor hcr.le
  have hdet := det_trim z mu r m 𝒥 hr0.le h2m hbad
  have hTM : RobustMultitask.Estimator.trimmedMean z (ζ + η) - mu
      = ((∑ ι ∈ Finset.univ.filter (fun ι : Fin N => m ≤ ι.val ∧ ι.val + m < N),
            z (Tuple.sort z ι)) - ((N : ℝ) - 2 * m) * mu) / ((N : ℝ) - 2 * m) := by
    unfold RobustMultitask.Estimator.trimmedMean
    rw [← hm]
    field_simp
  have hnum : |(∑ ι ∈ Finset.univ.filter (fun ι : Fin N => m ≤ ι.val ∧ ι.val + m < N),
            z (Tuple.sort z ι)) - ((N : ℝ) - 2 * m) * mu|
      < N * τ * s * (6 * ζ + 8 * η) := by
    have hJr : (𝒥.card : ℝ) * r ≤ ζ * N * r := by
      apply mul_le_mul_of_nonneg_right hcard.le hr0.le
    have hmr : 2 * (m : ℝ) * r ≤ 2 * (N * (ζ + η)) * r := by gcongr
    have : ζ * N * r + 2 * (N * (ζ + η)) * r + 2 * η * N * τ * s
        ≤ N * τ * s * (6 * ζ + 8 * η) := by
      rw [hr]
      have : 0 ≤ N * τ * s * η := by positivity
      nlinarith
    linarith
  rw [hTM, abs_div, abs_of_pos hDpos, div_lt_iff₀ hDpos]
  calc _ < N * τ * s * (6 * ζ + 8 * η) := hnum
    _ = τ * s * (3 * ζ + 4 * η) * (2 * N) := by ring
    _ ≤ τ * s * (3 * ζ + 4 * η) * (C₀ * ((N : ℝ) - 2 * m)) := by gcongr
    _ = _ := by ring


set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (Z : Fin N → Ω → ℝ) (𝒥 : Finset (Fin N)) (σ : Fin N → ℝ≥0) (mu ζ η C₀ : ℝ)
    (hC₀ : 2 < C₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2) (hcard : (𝒥.card : ℝ) < ζ * N)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 - 1 / C₀ - ζ)
    (hσ : ∀ j ∉ 𝒥, 0 < σ j)
    (hsub : ∀ j ∉ 𝒥, HasSubgaussianMGF (fun ω => Z j ω - mu) (σ j ^ 2) P)
    (hind : iIndepFun (fun j : {j : Fin N // j ∉ 𝒥} => Z j) P) :
    P {ω | C₀ * (⨆ j : {j : Fin N // j ∉ 𝒥}, (σ j : ℝ)) * (3 * ζ + 4 * η)
            * Real.sqrt (Real.log (3 / η))
          ≤ |RobustMultitask.Estimator.trimmedMean (fun j => Z j ω) (ζ + η) - mu|}
      ≤ ENNReal.ofReal (3 * Real.exp (-((N : ℝ) * η ^ 2) / 9)) := by
  classical
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    refine (prob_le_one).trans ?_
    simp only [CharP.cast_eq_zero, zero_mul, neg_zero, zero_div, exp_zero, mul_one]
    exact ENNReal.one_le_ofReal.2 (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hC0 : 0 < C₀ := by linarith
  have hinvC : 0 < 1 / C₀ := by positivity
  have hη2 : η ≤ 1 / 2 := by linarith
  have hω : 2 * (ζ + η) ≤ 1 - 2 / C₀ := by
    have : 2 / C₀ = 2 * (1 / C₀) := by ring
    linarith
  -- honest indices
  let H := {j : Fin N // j ∉ 𝒥}
  have hJlt : 𝒥.card < N := by
    have : (𝒥.card : ℝ) < N := by nlinarith
    exact_mod_cast this
  obtain ⟨j0, hj0⟩ : ∃ j : Fin N, j ∉ 𝒥 := by
    by_contra hall
    push Not at hall
    have : (Finset.univ : Finset (Fin N)) ⊆ 𝒥 := fun j _ => hall j
    have := Finset.card_le_card this
    simp at this; omega
  set nh := Fintype.card H with hnh
  have hnhN : (nh : ℝ) ≤ N := by
    have := Fintype.card_subtype_le (fun j : Fin N => j ∉ 𝒥)
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hnh0 : (0 : ℝ) ≤ nh := Nat.cast_nonneg _
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = ⨆ j : H, (σ j : ℝ) := ⟨_, rfl⟩
  have hστ : ∀ j : H, (σ j : ℝ) ≤ τ := fun j => hτ ▸
    le_ciSup (f := fun j : H => (σ j : ℝ)) (Set.finite_range _).bddAbove j
  have hτpos : 0 < τ := lt_of_lt_of_le (by exact_mod_cast hσ j0 hj0) (hστ ⟨j0, hj0⟩)
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (3 / η) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (6 : ℝ) ≤ 3 / η := by rw [le_div_iff₀ hη0]; linarith
    linarith
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt L := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hL1
  have hs0 : 0 < s := by linarith
  have hsL : s ^ 2 = L := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hexpL : exp (-L) = η / 3 := by
    rw [hL, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hexp2L : exp (-(2 * L)) = (η / 3) ^ 2 := by
    rw [show -(2 * L) = -L + -L by ring, Real.exp_add, hexpL]; ring
  obtain ⟨r, hr⟩ : ∃ r, r = 2 * τ * s := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  obtain ⟨l, hl⟩ : ∃ l, l = 2 * s / τ := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; positivity
  -- the key exponential estimate
  have hkey : ∀ j : H, exp (-(l * r)) * exp (((σ j ^ 2 : ℝ≥0) : ℝ) * l ^ 2 / 2) ≤ (η / 3) ^ 2 := by
    intro j
    rw [← Real.exp_add, ← hexp2L]
    apply Real.exp_le_exp.2
    have h1 : ((σ j ^ 2 : ℝ≥0) : ℝ) ≤ τ ^ 2 := by
      push_cast
      exact pow_le_pow_left₀ (NNReal.coe_nonneg _) (hστ j) 2
    have h2 : ((σ j ^ 2 : ℝ≥0) : ℝ) * l ^ 2 / 2 ≤ τ ^ 2 * l ^ 2 / 2 := by gcongr
    have h3 : τ ^ 2 * l ^ 2 / 2 = 2 * L := by
      rw [hl, ← hsL]; field_simp
    have h4 : l * r = 4 * L := by
      rw [hl, hr, ← hsL]; field_simp; ring
    linarith
  -- centred variables and the two transforms
  let X : H → Ω → ℝ := fun j ω => Z j ω - mu
  have hX : ∀ j : H, HasSubgaussianMGF (X j) (σ j ^ 2) P := fun j => hsub j.1 j.2
  let gB : ℝ → ℝ := fun x => if r < |x| then 1 else 0
  let gY : ℝ → ℝ := fun x => if |x| ≤ r then x else 0
  let gT : ℝ → ℝ := fun x => if |x| ≤ r then 0 else x
  have hgB : Measurable gB :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id.abs) measurable_const
      measurable_const
  have hgY : Measurable gY :=
    Measurable.ite (measurableSet_le measurable_id.abs measurable_const) measurable_id
      measurable_const
  have hgT : Measurable gT :=
    Measurable.ite (measurableSet_le measurable_id.abs measurable_const) measurable_const
      measurable_id
  have hgBb : ∀ x, |gB x| ≤ exp (-(l * r)) * (exp (l * x) + exp (-l * x)) := by
    intro x
    simp only [gB]
    split_ifs with h
    · rw [abs_one]
      have h1 : 1 ≤ exp (l * |x| - l * r) := by
        rw [Real.one_le_exp_iff]; nlinarith
      calc (1 : ℝ) ≤ exp (l * |x| - l * r) := h1
        _ = exp (-(l * r)) * exp (l * |x|) := by rw [← Real.exp_add]; ring_nf
        _ ≤ _ := by gcongr; exact exp_abs_le l x hl0.le
    · simp only [abs_zero]; positivity
  have hgTb : ∀ x, |gT x| ≤ (r + 1 / l) * exp (-(l * r)) * (exp (l * x) + exp (-l * x)) := by
    intro x
    simp only [gT]
    split_ifs with h
    · simp only [abs_zero]; positivity
    · push Not at h
      have hu := Real.add_one_le_exp (l * (|x| - r))
      have hE1 : 1 ≤ exp (l * (|x| - r)) := by rw [Real.one_le_exp_iff]; nlinarith
      have h1 : |x| ≤ (r + 1 / l) * exp (l * (|x| - r)) := by
        have : |x| - r ≤ (1 / l) * exp (l * (|x| - r)) := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl0]; nlinarith
        nlinarith
      calc |x| ≤ (r + 1 / l) * exp (l * (|x| - r)) := h1
        _ = (r + 1 / l) * (exp (-(l * r)) * exp (l * |x|)) := by
          rw [← Real.exp_add]; ring_nf
        _ ≤ (r + 1 / l) * (exp (-(l * r)) * (exp (l * x) + exp (-l * x))) := by
          gcongr; exact exp_abs_le l x hl0.le
        _ = _ := by ring
  let B : H → Ω → ℝ := fun j ω => gB (X j ω)
  let Y : H → Ω → ℝ := fun j ω => gY (X j ω)
  -- expectation bounds
  have hEB : ∀ j : H, P[B j] ≤ 2 * (η / 3) ^ 2 := by
    intro j
    obtain ⟨-, hb⟩ := sg_expect_bound (hX j) gB hgB _ l hgBb
    have := le_abs_self (P[B j])
    calc P[B j] ≤ |∫ ω, gB (X j ω) ∂P| := this
      _ ≤ 2 * exp (-(l * r)) * exp (((σ j ^ 2 : ℝ≥0) : ℝ) * l ^ 2 / 2) := hb
      _ ≤ 2 * (η / 3) ^ 2 := by rw [mul_assoc]; gcongr; exact hkey j
  have hEY : ∀ j : H, |P[Y j]| ≤ η * τ * s := by
    intro j
    obtain ⟨hTi, hb⟩ := sg_expect_bound (hX j) gT hgT _ l hgTb
    have hXi := (hX j).integrable
    have hsplit : ∀ ω, gY (X j ω) = X j ω - gT (X j ω) := by
      intro ω; simp only [gY, gT]; split_ifs <;> ring
    have hmean := sg_integral_eq_zero (hX j)
    have : P[Y j] = - ∫ ω, gT (X j ω) ∂P := by
      simp only [Y, hsplit]
      rw [integral_sub hXi hTi, hmean, zero_sub]
    rw [this, abs_neg]
    calc |∫ ω, gT (X j ω) ∂P|
        ≤ 2 * ((r + 1 / l) * exp (-(l * r))) * exp (((σ j ^ 2 : ℝ≥0) : ℝ) * l ^ 2 / 2) := hb
      _ = 2 * (r + 1 / l) * (exp (-(l * r)) * exp (((σ j ^ 2 : ℝ≥0) : ℝ) * l ^ 2 / 2)) := by ring
      _ ≤ 2 * (r + 1 / l) * (η / 3) ^ 2 := by
          have : 0 ≤ r + 1 / l := by positivity
          gcongr; exact hkey j
      _ ≤ η * τ * s := by
          have hrl : r + 1 / l = 2 * τ * s + τ / (2 * s) := by
            rw [hr, hl]; field_simp
          rw [hrl]
          have h1 : τ / (2 * s) ≤ τ * s := by
            rw [div_le_iff₀ (by positivity)]; nlinarith
          have h2 : 2 * (2 * τ * s + τ / (2 * s)) * (η / 3) ^ 2 ≤ 2 * (3 * τ * s) * (η / 3) ^ 2 := by
            gcongr; linarith
          have h3 : 2 * (3 * τ * s) * (η / 3) ^ 2 = η * τ * s * (2 * η / 3) := by ring
          have h4 : η * τ * s * (2 * η / 3) ≤ η * τ * s := by
            have : 0 ≤ η * τ * s := by positivity
            nlinarith
          linarith
  -- independence of the transformed families
  obtain ⟨cB, hcB⟩ : ∃ cB : H → ℝ, ∀ j, cB j = P[B j] := ⟨_, fun _ => rfl⟩
  obtain ⟨cY, hcY⟩ : ∃ cY : H → ℝ, ∀ j, cY j = P[Y j] := ⟨_, fun _ => rfl⟩
  have hindB : iIndepFun (fun (j : H) ω => B j ω - P[B j]) P := by
    have := hind.comp (fun (j : H) (y : ℝ) => gB (y - mu) - cB j)
      (fun j => (hgB.comp (measurable_id.sub_const mu)).sub_const _)
    simp only [hcB] at this
    exact this
  have hindY : iIndepFun (fun (j : H) ω => Y j ω - P[Y j]) P := by
    have := hind.comp (fun (j : H) (y : ℝ) => gY (y - mu) - cY j)
      (fun j => (hgY.comp (measurable_id.sub_const mu)).sub_const _)
    simp only [hcY] at this
    exact this
  have hindY' : iIndepFun (fun (j : H) ω => -(Y j ω - P[Y j])) P := by
    have := hind.comp (fun (j : H) (y : ℝ) => -(gY (y - mu) - cY j))
      (fun j => ((hgY.comp (measurable_id.sub_const mu)).sub_const _).neg)
    simp only [hcY] at this
    exact this
  -- subgaussianity (Hoeffding's lemma)
  have hsgB : ∀ j : H, HasSubgaussianMGF (fun ω => B j ω - P[B j])
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro j
    refine hasSubgaussianMGF_of_mem_Icc (hgB.comp_aemeasurable (hX j).aemeasurable)
      (ae_of_all _ fun ω => ?_)
    simp only [B, gB]; split_ifs <;> simp
  have hsgY : ∀ j : H, HasSubgaussianMGF (fun ω => Y j ω - P[Y j])
      ((‖r - (-r)‖₊ / 2) ^ 2) P := by
    intro j
    refine hasSubgaussianMGF_of_mem_Icc (hgY.comp_aemeasurable (hX j).aemeasurable)
      (ae_of_all _ fun ω => ?_)
    simp only [Y, gY]
    split_ifs with h
    · exact ⟨by linarith [neg_abs_le (X j ω)], by linarith [le_abs_self (X j ω)]⟩
    · exact ⟨by linarith, by linarith⟩
  have hc1 : (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by
    push_cast; simp; norm_num
  have hc2 : (((‖r - (-r)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = r ^ 2 := by
    push_cast
    rw [Real.norm_eq_abs, show r - -r = 2 * r by ring, abs_of_pos (by positivity)]
    ring
  -- the three bad events
  set E1 := {ω | η * N / 3 ≤ ∑ j : H, (B j ω - P[B j])} with hE1
  set E2 := {ω | η * N * τ * s ≤ ∑ j : H, (Y j ω - P[Y j])} with hE2
  set E3 := {ω | η * N * τ * s ≤ ∑ j : H, -(Y j ω - P[Y j])} with hE3
  have hnhpos : (0 : ℝ) < nh := by
    have : 0 < nh := Fintype.card_pos_iff.2 ⟨⟨j0, hj0⟩⟩
    exact_mod_cast this
  have hP1 : P E1 ≤ ENNReal.ofReal (exp (-((N : ℝ) * η ^ 2) / 9)) := by
    refine (sg_sum_tail _ hindB _ hsgB (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    apply Real.exp_le_exp.2
    rw [hc1, neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
    have : (N : ℝ) * η ^ 2 * (2 * (nh * (1 / 4))) ≤ (η * N / 3) ^ 2 * 9 := by
      have : (N : ℝ) * η ^ 2 * (2 * (nh * (1 / 4))) = (η ^ 2 * N) * nh / 2 := by ring
      rw [this]
      have : (η * N / 3) ^ 2 * 9 = (η ^ 2 * N) * N := by ring
      rw [this]
      have : 0 ≤ η ^ 2 * N := by positivity
      nlinarith
    linarith
  have hP2 : ∀ (W : H → Ω → ℝ), iIndepFun W P →
      (∀ j, HasSubgaussianMGF (W j) ((‖r - (-r)‖₊ / 2) ^ 2) P) →
      P {ω | η * N * τ * s ≤ ∑ j : H, W j ω}
        ≤ ENNReal.ofReal (exp (-((N : ℝ) * η ^ 2) / 9)) := by
    intro W hW hsg
    refine (sg_sum_tail _ hW _ hsg (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    apply Real.exp_le_exp.2
    rw [hc2, neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
    have e1 : (N : ℝ) * η ^ 2 * (2 * (nh * r ^ 2)) = (η ^ 2 * N * τ ^ 2 * s ^ 2) * (8 * nh) := by
      rw [hr]; ring
    have e2 : (η * N * τ * s) ^ 2 * 9 = (η ^ 2 * N * τ ^ 2 * s ^ 2) * (9 * N) := by ring
    rw [e1, e2]
    have : 0 ≤ η ^ 2 * N * τ ^ 2 * s ^ 2 := by positivity
    nlinarith
  have hP3 : P E2 ≤ ENNReal.ofReal (exp (-((N : ℝ) * η ^ 2) / 9)) := hP2 _ hindY hsgY
  have hP4 : P E3 ≤ ENNReal.ofReal (exp (-((N : ℝ) * η ^ 2) / 9)) :=
    hP2 _ hindY' (fun j => (hsgY j).neg)
  have hgoalEq : (⨆ j : {j : Fin N // j ∉ 𝒥}, (σ j : ℝ)) = τ := hτ.symm
  have hsqEq : Real.sqrt (Real.log (3 / η)) = s := by rw [hs, hL]
  rw [hgoalEq, hsqEq]
  have hsumH : ∀ f : Fin N → ℝ, ∑ j : H, f j = ∑ j ∈ 𝒥ᶜ, f j := fun f =>
    (Finset.sum_subtype (𝒥ᶜ) (fun x => by simp) f).symm
  have hsumEB : ∑ j : H, P[B j] ≤ nh * (2 * (η / 3) ^ 2) := by
    calc ∑ j : H, P[B j] ≤ ∑ _j : H, 2 * (η / 3) ^ 2 := Finset.sum_le_sum (fun j _ => hEB j)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hEBN : nh * (2 * (η / 3) ^ 2) ≤ 2 * η * N / 3 := by
    have h1 : (2 * (η / 3) ^ 2) ≤ 2 * η / 3 := by nlinarith
    calc (nh : ℝ) * (2 * (η / 3) ^ 2) ≤ N * (2 * η / 3) := by
          apply mul_le_mul hnhN h1 (by positivity) hNr.le
      _ = 2 * η * N / 3 := by ring
  have hsumEY : |∑ j : H, P[Y j]| ≤ η * N * τ * s := by
    refine (abs_sum_le_card_mul _ _ (η * τ * s) (fun j _ => hEY j)).trans ?_
    rw [Finset.card_univ, ← hnh]
    have : 0 ≤ η * τ * s := by positivity
    nlinarith
  have hcover : {ω | C₀ * τ * (3 * ζ + 4 * η) * s
          ≤ |RobustMultitask.Estimator.trimmedMean (fun j => Z j ω) (ζ + η) - mu|}
      ⊆ E1 ∪ E2 ∪ E3 := by
    intro ω hωS
    simp only [Set.mem_ofPred_eq] at hωS
    by_contra hcon
    simp only [Set.mem_union, hE1, hE2, hE3, Set.mem_ofPred_eq, not_or, not_le] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have hcountH : ((𝒥ᶜ.filter (fun j => r < |Z j ω - mu|)).card : ℝ) = ∑ j : H, B j ω := by
      rw [hsumH (fun j => gB (Z j ω - mu)), Finset.sum_boole]
    have hcountlt : ((𝒥ᶜ.filter (fun j => r < |Z j ω - mu|)).card : ℝ) < η * N := by
      rw [hcountH]
      have : ∑ j : H, B j ω = ∑ j : H, (B j ω - P[B j]) + ∑ j : H, P[B j] := by
        rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
      rw [this]
      linarith only [h1, hsumEB, hEBN]
    have hYsum : |∑ j ∈ 𝒥ᶜ, (if |Z j ω - mu| ≤ r then Z j ω - mu else 0)|
        < 2 * η * N * τ * s := by
      have e0 : ∑ j : H, (Y j ω - P[Y j]) + ∑ j : H, P[Y j] = ∑ j : H, Y j ω := by
        rw [← Finset.sum_add_distrib]; simp
      have e : ∑ j ∈ 𝒥ᶜ, (if |Z j ω - mu| ≤ r then Z j ω - mu else 0)
          = ∑ j : H, (Y j ω - P[Y j]) + ∑ j : H, P[Y j] := by
        rw [e0, ← hsumH (fun j => if |Z j ω - mu| ≤ r then Z j ω - mu else 0)]
      rw [e]
      have hb1 : |∑ j : H, (Y j ω - P[Y j])| < η * N * τ * s := by
        rw [abs_lt]; constructor
        · have : ∑ j : H, -(Y j ω - P[Y j]) = -∑ j : H, (Y j ω - P[Y j]) :=
            Finset.sum_neg_distrib _
          linarith only [this, h3]
        · exact h2
      calc _ ≤ |∑ j : H, (Y j ω - P[Y j])| + |∑ j : H, P[Y j]| := abs_add_le _ _
        _ < _ := by linarith only [hb1, hsumEY]
    have hfinal := cover_det hNpos (fun j => Z j ω) 𝒥 mu ζ η C₀ τ s r hC₀ hζ0 hη0 hη1 hcard
      hτpos hs0 hr hcountlt hYsum
    exact absurd hωS (not_le.2 hfinal)
  calc _ ≤ P (E1 ∪ E2 ∪ E3) := measure_mono hcover
    _ ≤ P E1 + P E2 + P E3 := (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ ENNReal.ofReal (exp (-((N : ℝ) * η ^ 2) / 9)) + ENNReal.ofReal (exp (-((N : ℝ) * η ^ 2) / 9))
        + ENNReal.ofReal (exp (-((N : ℝ) * η ^ 2) / 9)) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
